callback support
primitiveFetchNextCallback
	<option: #SpurObjectMemory>
	objectMemory dequeueCallback
		ifNil: [self primitiveFailFor: PrimErrNotFound]
		ifNotNil: [ :callback | self pop: 1 thenPush: callback ]