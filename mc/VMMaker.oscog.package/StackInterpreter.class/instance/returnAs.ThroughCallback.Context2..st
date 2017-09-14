callback support
returnAs: returnTypeOop ThroughCallback: vmCallbackContext Context2: callbackMethodContext
	"callbackMethodContext is an activation of invokeCallback:[stack:registers:jmpbuf:].
	 Its sender is the VM's state prior to the callback.  Reestablish that state (via longjmp),
	 and mark callbackMethodContext as dead."
	<export: true>
	<var: #vmCallbackContext type: #'VMCallbackContext *'>
	| calloutMethodContext theFP thePage |
	<var: #theFP type: #'char *'>
	<var: #thePage type: #'StackPage *'>
	self assert: primFailCode = 0.
	self assert: (objectMemory isIntegerObject: returnTypeOop).
	self assert: (objectMemory isImmediate: vmCallbackContext) not.
	self assert: ((objectMemory addressCouldBeObj: callbackMethodContext)
				and: [objectMemory isContext: callbackMethodContext]).
	self assert: (debugCallbackPath := 0) = 0.
	self assert: (debugCallbackReturns := debugCallbackReturns + 1) > 0.
	
	"Maybe necessary?"
	self restoreCStackStateForCallbackContext: vmCallbackContext.
	primitiveFunctionPointer := vmCallbackContext savedPrimFunctionPointer.
	
	"N.B. siglongjmp is defined as _longjmp on non-win32 platforms.
	  This matches the use of _setjmp in ia32abicc.c."
	self siglong: vmCallbackContext trampoline jmp: (self integerValueOf: returnTypeOop).
	"NOTREACHED"
	^true