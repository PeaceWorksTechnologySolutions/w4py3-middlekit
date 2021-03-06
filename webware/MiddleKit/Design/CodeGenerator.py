"""CodeGenerator.py

This module defines the basic machinery for a code generator,
but cannot be used directly. Instead, use concrete generators
like MySQLPythonGeneratory and MySQLSQLGenerator.

Terminology: "the standard classes" = ModelObject, Klasses, Klass and Attr

Modules that wish to do code generation must:
  * Define a class that inherits CodeGenerator
    (even if its implementation is 'pass').
  * Define various mix-in classes such as ModelObject,
    Klasses, Klass and Attr for the purpose of defining
    methods to aid in code generation.

What happens: When the generator is initialized, mixes in the methods
of various classes found in the module with the ones found in the model
(typically these come from MiddleKit.Core).

TO DO
-----
Make sure all three goals are met:
  * User-defined classes can be used in place of the standard classes
  * Inheritance of generators is supported
  * Class inheritance (like Klasses inheriting ModelObject works)
"""


import os
import sys

from webware.MiscUtils import AbstractError
from webware.MiscUtils.Configurable import Configurable
from webware.MiscUtils.Funcs import asclocaltime

from MiddleKit.Core.ModelUser import ModelUser


class CodeGenerator(ModelUser):

    def name(self):
        """Return the name of the generator for informational purposes.

        The name the is the class name.
        """
        return self.__class__.__name__

    def requireDir(self, dirname):
        if not os.path.exists(dirname):
            os.mkdir(dirname)
        assert os.path.isdir(dirname)

    def writeInfoFile(self, filename):
        with open(filename, 'w') as f:
            self.writeInfoItems(f)

    def writeInfoItems(self, f):
        wr = self.writeInfoItem
        wr(f, 'Date', asclocaltime())
        wr(f, 'Python ver', sys.version)
        wr(f, 'Op Sys', os.name)
        wr(f, 'Platform', sys.platform)
        wr(f, 'Cur dir', os.getcwd())

    def writeInfoItem(self, out, key, value):
        key = key.ljust(10)
        out.write('%s = %s\n' % (key, value))

    def generate(self, outdir):
        raise AbstractError(self.__class__)
