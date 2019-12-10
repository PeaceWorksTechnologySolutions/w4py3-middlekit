'''
GenTVSeries.py
Generated by MiddleKit.
'''

# MK attribute caches for setFoo() methods
_titleAttr = None
_directorsAttr = None
_castAttr = None
_yearsAttr = None


from datetime import date, datetime, time, timedelta
from decimal import Decimal
from MiscUtils.DateParser import parseDateTime, parseDate, parseTime
from MiddleKit.Run.MiddleObject import MiddleObject
import sys
from os.path import dirname
sys.path.insert(0, dirname(dirname(dirname(__file__))))
from Middle.Video import Video
del sys.path[0]

from MiddleKit.Run.SQLObjectStore import ObjRefError



class GenTVSeries(Video):

    def __init__(self):
        Video.__init__(self)
        self._years = None


    def years(self):
        return self._years

    def setYears(self, value):
        if value is not None:
            if isinstance(value, long):
                value = int(value)
                if isinstance(value, long):
                    raise OverflowError(value)
            elif not isinstance(value, int):
                raise TypeError('expecting int type, but got value %r of type %r instead' % (value, type(value)))

        # set the attribute
        origValue = self._years
        self._years = value

        # MiddleKit machinery
        if not self._mk_initing and self._mk_serialNum>0 and value is not origValue:
            global _yearsAttr
            if _yearsAttr is None:
                _yearsAttr = self.klass().lookupAttr('years')
                if not _yearsAttr.shouldRegisterChanges():
                    _yearsAttr = 0
            if _yearsAttr:
                # Record that it has been changed
                self._mk_changed = True
                if self._mk_changedAttrs is None:
                    self._mk_changedAttrs = {}  # maps name to attribute
                self._mk_changedAttrs['years'] = _yearsAttr  # changedAttrs is a set
                # Tell ObjectStore it happened
                self._mk_store.objectChanged(self)

