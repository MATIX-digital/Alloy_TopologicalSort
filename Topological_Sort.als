module Topological_Sort
open util/graph[Workflow]
open util/integer
open LinkedList

//Workflows (nodes of dag)
sig Workflow extends ListableObject {
	//with transitive dependencies (directed edges)
	dependend_from: set Workflow
}

//Contains the sorted execution order
one sig ExecutionOrder extends ListSignature { }

//For visualisation: shows the elements that got queued in this time-step
var sig NewQueuedObjects in Workflow	{ }
//For visualisation: shows the queued elements
var sig QueuedObjects in Workflow	{ }



// Workflows not yet sorted with fulfilled dependencies
// alle Workflows - Wf mit unerfüllten Abhängigkeiten - Wf in ExecutionOrder
let getLeafElements = {(Workflow - (dependend_from - Workflow -> (getAllListItemsOfCurrentTimeStep[ExecutionOrder])).Workflow) - (getAllListItemsOfCurrentTimeStep[ExecutionOrder])}

pred topological_sort {
	//Guard Condition: there are elements without unqueued dependencies 
	some getLeafElements

	//Visualisation
	NewQueuedObjects' = getLeafElements
	
	// Workflows not yet sorted with fulfilled dependencies are added to ExecutionOrder
	addToList[ExecutionOrder, getLeafElements]
}

fun needed_for: Workflow -> Workflow {
	~dependend_from
}

fact graphIsDag {
	dag[needed_for]
}

pred init {
	no ExecutionOrder.LinkedList
	no ExecutionOrder.startElement
	no QueuedObjects
	no NewQueuedObjects
}

pred stutter {
	unchanged[ExecutionOrder.LinkedList]
	unchanged[ExecutionOrder.startElement]
	no NewQueuedObjects'
}

pred trans {
	init
	always	(
		topological_sort or 
		stutter
	)
} 

pred runConditions {
	trans
	always alwaysConditions

	//Every Workflow has to be added to ExecutionOrder
	eventually getListLength[ExecutionOrder] = #Workflow
}


pred alwaysConditions	{
	//Visualisation
	QueuedObjects = (getAllListItemsOfCurrentTimeStep[ExecutionOrder] - NewQueuedObjects)
	no {QueuedObjects & NewQueuedObjects}
}

run {
	//For some dependency
	#Workflow.dependend_from > 2
	#dependend_from.Workflow > 2
	runConditions

} for exactly 5 Workflow

run FindUnvalidWorlds {
	//For some dependency
	#Workflow.dependend_from > 2
	#dependend_from.Workflow > 2
	runConditions

	always historically not Topological_Sort_Check
} for exactly 6 Workflow

pred Topological_Sort_Check {
	all w: Workflow | all wd: w.dependend_from | wd not in w.^(ExecutionOrder.LinkedList)
}



