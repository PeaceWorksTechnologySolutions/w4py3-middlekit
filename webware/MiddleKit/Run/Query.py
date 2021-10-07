#!/usr/bin/env python

# For running tests at bottom
#import os
#import sys
#path = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
#sys.path.append(path)

from MiddleKit.Core.ObjRefAttr import ObjRefAttr
from MiddleKit.Core.ListAttr import ListAttr
from MiddleKit.Core.StringAttr import StringAttr
from MiddleKit.Run.spark import GenericParser, GenericASTTraversal, GenericASTTraversalPruningException
from MiddleKit.Run.scanner import GenericScanner
from MiddleKit.Run.scanner import GenericToken
import time

'''
This module implements a sql-like query language for MiddleKit.  
The primary benefits (over using MiddleKit with raw SQL where-clauses) are:
    - you can fetch objects from the "primary table" as well as joined objects in a single query (using 'with')
    - if the class in your query has subclasses, the corresponding tables are queried automatically and these
      results are returned together
    - it writes the messy MiddleKit objref joins for you (i.e. does the bitwise operations)
    - some SQL operators (i.e. ilike) are implemented for databases which don't support them natively (mysql)

'''


# create a string attribute instance for escaping strings
stringAttr = StringAttr({'Name': 'unused'})


class ParseError(Exception):
    pass


class ScanError(Exception):
    pass


class Token(GenericToken):

    def dump(self, indent=''):
        if self.attr:
            return "%s%s, %s\n" % (indent, self.type, self.attr)
        return "%s%s\n" % (indent, self.type)


class Scanner(GenericScanner):
    keywords = { 'and': 1,
                 'or': 1,
                 'not': 1,
                 'like': 1,
                 'ilike': 1,
                 'regexp': 1,
                 'null': 1,
                 'none': 1,
                 'is': 1,
                 'with': 1,
                 'in': 1,
                 'exists': 1,
                 'where': 1,
                }

    def tokenize(self, input):
        self._input = input
        self.rv = []
        GenericScanner.tokenize(self, input)
        return self.rv

    def error(self, s, pos):
        e = "\n" + self._input + "\n"
        e += ' ' * pos + '^\n'
        e += "Syntax error in MiddleKit query"
        raise ScanError(e)
    
    def t_whitespace(self, s):
        r' \s+ '
        pass

    def t_operator(self, s):
        r' == | \!= | <> | <= | >= | < | > | \+ | - | \* | , '
        t = Token(type=s)
        self.rv.append(t)

    def t_lParen(self, s):
        r' \( '
        t = Token(type='lParen')
        self.rv.append(t)

    def t_rParen(self, s):
        r' \) '
        t = Token(type='rParen')
        self.rv.append(t)
        
    def t_dot(self, s):
        r' \. '
        t = Token(type='dot')
        self.rv.append(t)

    def t_identifier(self, s):
        r' [a-zA-Z][a-zA-Z0-9]* '
        if s.lower() in self.keywords:
            keyword = s.lower()
            if keyword == 'none':
                keyword = 'null'
            t = Token(type=keyword)
        else:
            t = Token(type='identifier',attr=s)
        self.rv.append(t)
    
    def t_quotedString(self, s):
        r' \'([^\']|\'\')*\'|\"([^\"]|\"\")*\" '
        if s[0] == "'":
            s = s[1:-1].replace("''", "'")
        elif s[1] == '"':
            s = s[1:-1].replace('""', '"')
        t = Token(type='quotedString',attr=s)
        self.rv.append(t)

    def t_integer(self, s):
        r' \d+ '
        t = Token(type='integer', attr=s)
        self.rv.append(t)

    def t_default(self, s):
        r' $ '
        # set default to end-of-string, so that nothing is accepted by
        # default.  We want to generate an error when input is invalid.
        pass


class Node:
    def __init__(self, type, left=None, right=None, extra=None):
        self.type = type.type
        self.attr = type.attr
        self._kids = []
        self.left = left
        self.right = right
        self.inheritedContext = None
        self.resolvedContext = None
        self.dereferenced = 0
        self.extra = extra
        if left: self._kids.append(left)
        if right: self._kids.append(right)

    def __getitem__(self, i):
        return self._kids[i]

    def dump(self, indent=''):
        output = ''
        for kid in self._kids:
            output += kid.dump(indent+'    ')
        return "%sNode: %s, %s\n%s" % (indent, self.type, self.attr, output)


class Parser(GenericParser):
    def __init__(self, start='start'):
        GenericParser.__init__(self, start)

    def test(self, string):
        scanner = Scanner()
        return self.parse(scanner.tokenize(string))

    def error(self, token):
        if token.attr:
            value = token.attr
        else:
            value = token.type
        raise ParseError("Syntax error in MiddleKit query near: `%s'" % value)

    def p_start_1(self, args):
        ' start ::= qual '
        return args[0]

    def p_start_2(self, args):
        ' start ::= qual with attrList'
        return Node(type=Node(type=args[1]),
                    left=args[0],
                    right=args[2])

    def p_start_3(self, args):
        ' start ::= with attrList'
        return Node(type=Node(type=args[0]),
                    left=None,
                    right=args[1])

    def p_start_4(self, args):
        ' start ::= '
        return Node(type=Token(type=""))

    def p_attrList_1(self, args):
        ' attrList ::= attrList , qualifiedAttr '
        return Node( type=Node(type=args[1]),
                     left=args[0],
                     right=args[2])

    def p_attrList_2(self, args):
        ' attrList ::= qualifiedAttr '
        return args[0]

    def p_qual_1(self, args):
        ' qual ::= lParen qual rParen '
        return Node(type=args[0],
                   left=args[1])

    def p_qual_2(self, args):
        ' qual ::= disjunction '
        return args[0]

    def p_disj_1(self, args):
        ' disjunction ::= qual or qual '
        return Node(type=args[1],
                    left=args[0],
                    right=args[2])

    def p_disj_2(self, args):
        ' disjunction ::= conjunction '
        return args[0]

    def p_conj_1(self, args):
        ' conjunction ::= qual and qual '
        return Node(type=args[1],
                    left=args[0],
                    right=args[2])

    def p_conj_2(self, args):
        ' conjunction ::= condition '
        return args[0]

    def p_cond_1(self, args):
        ' condition ::= not qual '
        return Node(type=args[0],
                    left=args[1])

    def p_cond_2(self, args):
        ' condition ::= expr comparisonop expr '
        return Node(type=args[1],
                    left=args[0],
                    right=args[2])

    def p_cond_3(self, args):
        ' condition ::= exists lParen identifier where qual rParen'
        return Node(type=args[0],
                    right=args[4],
                    extra=args[2])

    def p_cond_4(self, args):
        ' condition ::= expr '
        return args[0]

    def p_compop(self, args):
        ''' 
        comparisonop ::= ==
        comparisonop ::= !=
        comparisonop ::= <>
        comparisonop ::= >=
        comparisonop ::= >
        comparisonop ::= <
        comparisonop ::= <=
        comparisonop ::= like
        comparisonop ::= ilike
        comparisonop ::= regexp
        comparisonop ::= is
        comparisonop ::= in
        '''
        t = Token(type='operator', attr=args[0].type)
        return Node(type=t)
            
    def p_expr_1(self, args):
        ' expr         ::= lParen exprList rParen'
        return Node(type=args[0],
                   left=args[1])

    def p_expr_2(self, args):
        ' expr         ::= expr + expr '
        return Node(type=args[1],
                    left=args[0],
                    right=args[2])

    def p_expr_3(self, args):
        ' expr         ::= expr - expr '
        return Node(type=args[1],
                    left=args[0],
                    right=args[2])

    def p_expr_4(self, args):
        ' expr         ::= factor '
        return args[0]

    def p_expr_5(self, args):
        ' expr         ::= null '
        return Node(type=args[0])

    def p_exprList_1(self, args):
        ' exprList ::= exprList , expr '
        return Node( type=Node(type=args[1]),
                     left=args[0],
                     right=args[2])

    def p_exprList_2(self, args):
        ' exprList ::= expr '
        return args[0]

    def p_factor_1(self, args):
        ' factor       ::= expr * expr '
        return Node(type=args[1],
                    left=args[0],
                    right=args[2])

    def p_factor_2(self, args):
        ' factor       ::= term '
        return args[0]

    def p_factor_3(self, args):
        ''' factor       ::= + term 
            factor       ::= - term 
        '''
        t = Token(type='unary', attr=args[0].type)
        return Node(type=Node(type=t),
                    left=args[1])
 
    def p_term_2(self, args):
        ''' term         ::= number
            term         ::= qualifiedAttr 
        '''
        return args[0]

    def p_term_3(self, args):
        ' term       ::= quotedString '
        return Node(type=args[0])

    def p_term_4(self, args):
        ' term       ::= quotedString '
        return Node(type=args[0])
    
    def p_number_1(self, args):
        ' number       ::= integer '
        return Node(type=args[0])

    def p_number_2(self, args):
        ' number       ::= integer dot integer '
        return Node(type=Token('decimal'),
                    left=args[0],
                    right=args[2])

    def p_qualAttr_1(self, args):
        ' qualifiedAttr ::= identifier dot qualifiedAttr '
        t = Token(type='identifierForKlass', attr=args[0].attr)
        return Node(type=Token('dereference'),
                    left=Node(type=t),
                    right=args[2])

    def p_qualAttr_2(self, args):
        ' qualifiedAttr ::= identifier '
        t = Token(type='identifierForAttr', attr=args[0].attr)
        return Node(type=t)


def dump_contexts(contexts):
    for c in contexts:
        print(c.dump())
    print('-' * 40)


class KlassContext:
    def __init__(self, klass, alias, identifier=None, parent=None):
        self.klass = klass
        self.alias = alias
        self.identifier = identifier
        self.parent = parent

    def dump(self):
        if self.identifier:
            identifier = ', identifier=%s' % self.identifier
        else:
            identifier = ''
        return 'KlassContext: klass=%s, alias=%s%s' % (self.klass.name(), self.alias, identifier)

        
class Join:
    def __init__(self, fromContext, attr, toContext):
        self.fromContext = fromContext
        self.attr = attr
        self.toContext = toContext

    def sql(self):
        return " left join %s %s on %s.%s & 4294967295 = %s.%s " % (self.toContext.klass.sqlTableName(), self.toContext.alias, self.fromContext.alias, self.attr + "Id", self.toContext.alias, self.toContext.klass.sqlSerialColumnName())

class AttrCheck(GenericASTTraversal):
    def __init__(self, ast, store, rootContexts, rootJoins):
        GenericASTTraversal.__init__(self, ast)
        ast.inheritedContext = rootContexts[0]
        self.store = store
        self._tablenum = 0
        self.contexts = rootContexts
        self.joins = rootJoins
        self.joinCache = {}
        self.preorder()

    def nextAlias(self):
        self._tablenum += 1
        return 't%d' % self._tablenum

    def n_dereference(self, node):
        node.left.inheritedContext = node.inheritedContext
        self.preorder(node.left)
        node.right.inheritedContext = node.left.resolvedContext
        self.preorder(node.right)
        node.resolvedContext = node.right.resolvedContext
        self.prune() # we've recursed explicitly; no need to continue on down

    def n_identifierForKlass(self, node):
        try:
            #print 'Looking for %s in context:' % (node.attr)
            node.inheritedContext.dump()
            attr = node.inheritedContext.klass.lookupAttr(node.attr)
        except KeyError:
            # attribute not found; check whether the identifier is a Class from a parent context
            c = node.inheritedContext
            while c.parent:
                #print c.klass.name()
                c = c.parent
                if c.klass.name() == node.attr:  # found a klass which matches
                    node.resolvedContext = c
                    break
            if node.resolvedContext is None:
                raise "Unknown attribute '%s'" % (node.attr)
        else:
            # we've found the attribute
            if not isinstance(attr, ObjRefAttr):
                raise "%s.%s cannot be dereferenced -- it is not an object reference." % (node.inheritedContext.klass.name(), node.attr)

            resolvedKlass = self.store._klassForClass(attr.targetClassName())
            join = (node.inheritedContext.klass.name(), node.attr, resolvedKlass.name())
            #print 'inherited context %s' % node.inheritedContext.dump()
            #print 'checking for join %s' % `join`
            if join in self.joinCache:
                node.resolvedContext = self.joinCache[join]
            else:
                node.resolvedContext = KlassContext(resolvedKlass, self.nextAlias())
                #print 'adding context: %s' % node.resolvedContext.dump()
                self.joinCache[join] = node.resolvedContext
                #print 'adding join: %s' % str(join)
                self.contexts.append(node.resolvedContext)
                self.joins.append( Join( node.inheritedContext, node.attr, node.resolvedContext))
            #print 'resolved %s.%s' % (node.inheritedContext.klass.name(), attr.name())

    def n_identifierForAttr(self, node):
        if node.attr == node.inheritedContext.klass.sqlSerialColumnName():
            node.resolvedContext = node.inheritedContext
            node.isSerialColumn = True
            node.sqlCol = node.attr
            return
        try:
            attr = node.inheritedContext.klass.lookupAttr(node.attr)
        except KeyError:
            raise "Middle class '%s' has no attribute '%s'" % (node.inheritedContext.klass.name(), node.attr)
        #print 'resolved %s.%s' % (node.inheritedContext.klass.name(), attr.name())
        if isinstance(attr, ListAttr):
            raise "cannot compare %s.%s -- it is a list attribute" % (node.inheritedContext.klass.name(), node.attr)
        node.resolvedContext = node.inheritedContext
        node.sqlCol = attr.sqlColumnName()
        node.isSerialColumn = False

    def n_exists(self, node):
        # FIXME: look up Klass (left node), ensure it exists
        klass = self.store.model().klass(node.extra.attr)
        # set KlassContext for right side
        node.inheritedContext = node.right.inheritedContext = KlassContext(klass, self.nextAlias(), parent=node.inheritedContext)
        #print 'Current contexts:'
        #dump_contexts(self.contexts)
        oldstuff = self.contexts, self.joins, self.joinCache
        #print 'clearing contexts, joins'
        node.contexts = self.contexts = []
        node.joins = self.joins = []
        self.joinCache = {}
        self.preorder(node.right)
        #print 'Current contexts:'
        #dump_contexts(self.contexts)
        #print 'restoring contexts, joins'
        self.contexts, self.joins, self.joinCache = oldstuff
        #print 'Current contexts:'
        #dump_contexts(self.contexts)
        self.prune()

    def default(self, node):
        # if it exists, propagate the context klass to the children
        if node.left:
            node.left.inheritedContext = node.inheritedContext
        if node.right:
            node.right.inheritedContext = node.inheritedContext

def buildJoins(joins):
    output = []
    for join in joins:
        output.append(join.sql())
    return " ".join(output)

class RunQueries(GenericASTTraversal):
    def __init__(self, ast, store, rootContexts, rootJoins):
        GenericASTTraversal.__init__(self, ast)
        self.store = store
        self.postorder(ast)

    def n_with(self, node):
        if node.left:
            node.output = node.left.output
        else:
            node.output = ''

    def n_identifierForKlass(self, node):
        node.output = ''

    def n_identifierForAttr(self, node):
        if node.resolvedContext is None: 
            pass
            #print 'Node has no resolvedContext:'
            #print node.dump()
        node.output = "%s.%s" % (node.resolvedContext.alias, node.sqlCol)
        if node.isSerialColumn:
            node.output += ' | %d ' % (node.resolvedContext.klass.id() << 32)

    def n_operator(self, node):
        if node.attr == 'ilike':
            node.output = self.store.sqlCaseInsensitiveLike(node.left.output, node.right.output)
        elif node.attr == '==':
            if node.left and node.left.type == 'null':
                node.output = "%s is null" % node.right.output
            elif node.right and node.right.type == 'null':
                node.output = "%s is null" % node.left.output
            else:
                #print node.dump()
                node.output = "%s = %s" % (node.left.output, node.right.output)
        elif node.attr == 'regexp':
            node.output = self.store.sqlCaseInsensitiveRegexp(node.left.output, node.right.output)
        else:
            node.output = " ".join([node.left.output, node.attr, node.right.output])

    def n_lParen(self, node):
        node.output = " (%s) " % node.left.output

    def n_exists(self, node):
        joins = buildJoins(node.joins)
        where = node.right.output
        # FIXME: we don't handle the case where the Class in the subquery has subclasses.  This
        # could be implemented by emitting (exists (select * from A ...) or exists (select * from B ...) or ...)
        node.output = 'exists ( select * from %s %s %s where %s )' % (node.inheritedContext.klass.sqlTableName(), node.inheritedContext.alias, joins, where)

    def default(self, node):
        node.output = []
        if node.type == 'not':
            node.output.append(node.type)
        elif node.type == 'unary':
            node.output.append(node.attr)

        if node.left:
            try:
                node.output.append(node.left.output)
            except AttributeError:
                raise "node %s has no output" % node.left.dump()
                
        if node.type == 'quotedString':
            node.output.append(stringAttr.sqlValue(node.attr))
        elif node.type in ['integer', 'operator']:
            node.output.append(node.attr)
        elif node.type in ['+','-','*','and','or','null', ',']:
            node.output.append(node.type)

        if node.right:
            node.output.append(node.right.output)
        node.output = " ".join(node.output)


class Query:
    def __init__(self, store):
        self._store = store

    def handleSubklasses(self, tree, contexts, joins, index, fetchReferenced):
        store = self._store
        if index >= len(contexts):
            base = contexts[0]
            cols = ["t0.%s" % c for c in base.klass.allColumns()]
            if fetchReferenced:
                fetchKlasses = [c.klass for c in contexts]
                for context in contexts[1:]:
                    cols.extend( ["%s.%s" % (context.alias, c) for c in context.klass.allColumns()])
            else:
                fetchKlasses = [base.klass]
            cols = ",".join(cols)
            select = "select %s from %s %s" % (cols, base.klass.sqlTableName(), base.alias)
            sql = select + buildJoins(joins)
            if tree.output:
                clauses = " where %s " % tree.output
            else:
                clauses = ""
            #print sql, clauses
            return store.fetchObjectsFromQuery(sql, fetchKlasses, clauses=clauses)[0]
        else:
            objs = []
            context = contexts[index]
            savedklass = context.klass
            for klass in [context.klass] + context.klass.subklasses():
                if not klass.isAbstract():
                    context.klass = klass
                    objs += self.handleSubklasses(tree, contexts, joins, index+1, fetchReferenced)
            context.klass = savedklass  # restore the original klass
            return objs

    def fetchObjects(self, klass, qualifier, fetchReferenced=0):
        scanner = Scanner()
        parser = Parser()
        try:
            tokens = scanner.tokenize(qualifier)
            tree = parser.parse(tokens)
        except ParseError as e:
            err = e.args[0]
            err += "\n\n%s" % qualifier
            e.args = (err,)
            raise
        #print tree.dump()
        rootContexts = [KlassContext(klass, 't0')]
        rootJoins = []
        AttrCheck(tree, self._store, rootContexts, rootJoins)
        RunQueries(tree, self._store, rootContexts, rootJoins)
        return self.handleSubklasses(tree, rootContexts, rootJoins, 0, fetchReferenced)


if __name__ == "__main__":
    scanner = Scanner()
    tokens = scanner.tokenize('a == b')
    assert [t.dump() for t in tokens] == ['identifier, a\n', '==,  \n', 'identifier, b\n']
    parser = Parser()
    parser.test('a == b')
    parser.test("( (  title ilike 'the' ) and (  title ilike 'one' ) )")
    parser.test("( (  title > (5 + (1-5)) ) )")
    parser.test("a in ('a', 'b')")
    parser.test("exists (Request where Request.user == User)")
