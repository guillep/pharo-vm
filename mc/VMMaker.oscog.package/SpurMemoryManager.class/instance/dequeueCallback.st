callback support
dequeueCallback

	^callbackQueue ~= nilObj ifTrue:
		[self popObjStack: callbackQueue]