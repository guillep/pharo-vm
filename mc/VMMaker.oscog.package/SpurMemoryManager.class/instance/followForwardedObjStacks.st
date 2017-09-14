compaction
followForwardedObjStacks
	"Compaction will move objStack pages as well as ordinary objects.
	 So they need their slots followed."
	self followForwardedInObjStack: markStack atIndex: MarkStackRootIndex.
	self followForwardedInObjStack: weaklingStack atIndex: WeaklingStackRootIndex.
	self followForwardedInObjStack: mournQueue atIndex: MournQueueRootIndex.
	
	"Should not be necessary, if these are just callback IDs"
	self followForwardedInObjStack: callbackQueue atIndex: CallbackQueueRootIndex.