callback support
sendInvokeCallbackContext: vmCallbackContext
	"Send the calllback message to Alien class with the supplied arg(s).  Use either the 1 arg
	 invokeCallbackContext: or the 4 arg invokeCallback:stack:registers:jmpbuf: message,
	 depending on what selector is installed in the specialObjectsArray. Note that if invoking the
	 legacy invokeCallback:stack:registers:jmpbuf: we pass the vmCallbackContext as the jmpbuf
	 argument (see reestablishContextPriorToCallback:). The arguments are raw C addresses and
	 are converted to integer objects on the way. sendInvokeCallbackContext: &
	 returnAs:ThroughCallback:Context: along with ownVM: and disownVM: conspire to save and
	 restore newMethod, argumentCount and primitiveFunctionPointer around a callback.
	 The VM depends on argumentCount being correct to cut-back the correct number of
	 arguments on primitive return.  If a primitive that invokes a callback fails after invoking a
	 callback (a bad idea, but s**t happens during development) then newMethod is required to
	 activate the right faling method, and Spur expects primitiveFunctionPointer to be valid, so
	 asserts will fail misleadingly if not."
	<export: true>
	<var: #vmCallbackContext type: #'VMCallbackContext *'>
	| address |
	self print: 'Queuing Callback'; cr.
	
	"???"
	"vmCallbackContext savedPrimFunctionPointer: primitiveFunctionPointer."
	
	"But this one is maybe necessary?"
	self saveCStackStateForCallbackContext: vmCallbackContext.
	
	address := self positiveMachineIntegerFor: vmCallbackContext.
	objectMemory queueCallback: address.
	pendingCallbacks := pendingCallbacks + 1.
	self forceInterruptCheck.
	self enterSmalltalkExecutiveFromCallback.
	"not reached"
	^true