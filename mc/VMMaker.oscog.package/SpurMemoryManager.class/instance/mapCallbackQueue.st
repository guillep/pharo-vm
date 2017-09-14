weakness and ephemerality
mapCallbackQueue
	<inline: #never>
	self objStack: callbackQueue do:
		[:i :page| | callback |
		callback := self fetchPointer: i ofObject: page.
		(self isNonImmediate: callback) ifTrue: "someone could try and become weaklings into immediates..."
			[(self isForwarded: callback) ifTrue:
				[callback := self followForwarded: callback].
			 (scavenger isScavengeSurvivor: callback) ifFalse:
				[callback := scavenger copyAndForwardMourner: callback].
			 "we could check for change but writes are cheasp with write buffers..."
			 self storePointerUnchecked: i ofObject: page withValue: callback]]