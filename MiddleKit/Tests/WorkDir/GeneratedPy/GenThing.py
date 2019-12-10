'''
GenThing.py
Generated by MiddleKit.
'''

# MK attribute caches for setFoo() methods
_aAttr = None
_bAttr = None


from datetime import date, datetime, time, timedelta
from decimal import Decimal
from MiscUtils.DateParser import parseDateTime, parseDate, parseTime
from MiddleKit.Run.MiddleObject import MiddleObject


from MiddleKit.Run.MiddleObject import MiddleObject
from MiddleKit.Run.SQLObjectStore import ObjRefError



class GenThing(MiddleObject):

    def __init__(self):
        MiddleObject.__init__(self)
        self._a = None
        self._b = None


    def a(self):
        return self._a

    def setA(self, value):
        if value is not None:
            if not isinstance(value, str):
                raise TypeError('expecting string type, but got value %r of type %r instead' % (value, type(value)))

        # set the attribute
        origValue = self._a
        self._a = value

        # MiddleKit machinery
        if not self._mk_initing and self._mk_serialNum>0 and value is not origValue:
            global _aAttr
            if _aAttr is None:
                _aAttr = self.klass().lookupAttr('a')
                if not _aAttr.shouldRegisterChanges():
                    _aAttr = 0
            if _aAttr:
                # Record that it has been changed
                self._mk_changed = True
                if self._mk_changedAttrs is None:
                    self._mk_changedAttrs = {}  # maps name to attribute
                self._mk_changedAttrs['a'] = _aAttr  # changedAttrs is a set
                # Tell ObjectStore it happened
                self._mk_store.objectChanged(self)

    def b(self):
        return self._b

    def setB(self, value):
        if value is not None:
            if not isinstance(value, str):
                raise TypeError('expecting string type, but got value %r of type %r instead' % (value, type(value)))

        # set the attribute
        origValue = self._b
        self._b = value

        # MiddleKit machinery
        if not self._mk_initing and self._mk_serialNum>0 and value is not origValue:
            global _bAttr
            if _bAttr is None:
                _bAttr = self.klass().lookupAttr('b')
                if not _bAttr.shouldRegisterChanges():
                    _bAttr = 0
            if _bAttr:
                # Record that it has been changed
                self._mk_changed = True
                if self._mk_changedAttrs is None:
                    self._mk_changedAttrs = {}  # maps name to attribute
                self._mk_changedAttrs['b'] = _bAttr  # changedAttrs is a set
                # Tell ObjectStore it happened
                self._mk_store.objectChanged(self)

