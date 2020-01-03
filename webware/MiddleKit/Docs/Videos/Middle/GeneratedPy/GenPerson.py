'''
GenPerson.py
Generated by MiddleKit.
'''

# MK attribute caches for setFoo() methods
_videoAttr = None
_nameAttr = None
_birthDateAttr = None


from datetime import date, datetime, time, timedelta
from decimal import Decimal
from webware.MiscUtils.DateParser import parseDateTime, parseDate, parseTime
from MiddleKit.Run.MiddleObject import MiddleObject


from MiddleKit.Run.MiddleObject import MiddleObject
from MiddleKit.Run.SQLObjectStore import ObjRefError



class GenPerson(MiddleObject):

    def __init__(self):
        MiddleObject.__init__(self)
        self._video     = None
        self._name      = None
        self._birthDate = None


    def video(self):
        if self._video is not None and not isinstance(self._video, MiddleObject):
            try:
                self.__dict__['_video'] = self._mk_store.fetchObjRef(self._video)
            except ObjRefError as e:
                self.__dict__['_video'] = self.objRefErrorWasRaised(e, 'Person', 'video')
        return self._video

    def setVideo(self, value):
        
        if value is not None and not isinstance(value, int):
            if not isinstance(value, MiddleObject):
                raise TypeError('expecting a MiddleObject, but got value %r of type %r instead' % (value, type(value)))
            from Middle.Video import Video
            if not isinstance(value, Video):
                raise TypeError('expecting Video, but got value %r of type %r instead' % (value, type(value)))

        # set the attribute
        origValue = self._video
        self._video = value

        # MiddleKit machinery
        if not self._mk_initing and self._mk_serialNum>0 and value is not origValue:
            global _videoAttr
            if _videoAttr is None:
                _videoAttr = self.klass().lookupAttr('video')
                if not _videoAttr.shouldRegisterChanges():
                    _videoAttr = 0
            if _videoAttr:
                # Record that it has been changed
                self._mk_changed = True
                if self._mk_changedAttrs is None:
                    self._mk_changedAttrs = {}  # maps name to attribute
                self._mk_changedAttrs['video'] = _videoAttr  # changedAttrs is a set
                # Tell ObjectStore it happened
                self._mk_store.objectChanged(self)

    def name(self):
        return self._name

    def setName(self, value):
        assert value is not None
        if value is not None:
            if not isinstance(value, str):
                raise TypeError('expecting string type, but got value %r of type %r instead' % (value, type(value)))

        # set the attribute
        origValue = self._name
        self._name = value

        # MiddleKit machinery
        if not self._mk_initing and self._mk_serialNum>0 and value is not origValue:
            global _nameAttr
            if _nameAttr is None:
                _nameAttr = self.klass().lookupAttr('name')
                if not _nameAttr.shouldRegisterChanges():
                    _nameAttr = 0
            if _nameAttr:
                # Record that it has been changed
                self._mk_changed = True
                if self._mk_changedAttrs is None:
                    self._mk_changedAttrs = {}  # maps name to attribute
                self._mk_changedAttrs['name'] = _nameAttr  # changedAttrs is a set
                # Tell ObjectStore it happened
                self._mk_store.objectChanged(self)

    def birthDate(self):
        return self._birthDate

    def setBirthDate(self, value):
        if isinstance(value, datetime):
            value = value.date()
        if value is not None:
            if isinstance(value, str):
                value = parseDate(value)
            if not isinstance(value, date):
                raise TypeError('expecting date type (e.g., date), but got'
                    ' value %r of type %r instead' % (value, type(value)))

        # set the attribute
        origValue = self._birthDate
        self._birthDate = value

        # MiddleKit machinery
        if not self._mk_initing and self._mk_serialNum>0 and value is not origValue:
            global _birthDateAttr
            if _birthDateAttr is None:
                _birthDateAttr = self.klass().lookupAttr('birthDate')
                if not _birthDateAttr.shouldRegisterChanges():
                    _birthDateAttr = 0
            if _birthDateAttr:
                # Record that it has been changed
                self._mk_changed = True
                if self._mk_changedAttrs is None:
                    self._mk_changedAttrs = {}  # maps name to attribute
                self._mk_changedAttrs['birthDate'] = _birthDateAttr  # changedAttrs is a set
                # Tell ObjectStore it happened
                self._mk_store.objectChanged(self)
