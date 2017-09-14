callback support
queueCallback: aCallbackContext

	self ensureRoomOnObjStackAt: CallbackQueueRootIndex.
	self push: aCallbackContext onObjStack: callbackQueue.