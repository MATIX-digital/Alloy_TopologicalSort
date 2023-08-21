module LinkedList
open util/integer



// Linked list for temporal logic. 

// Keep integer-range in mind!
// A ListableObject cannot be in the same list more than once!
// The pop method is not perfect and has some usage conditions.

// Any operation that manipulates the list, sets the future list. It's not allowed to remain unchanged in frame-condition.
// If a list isn't manipulated, unchangedList[list] must be invoked in the Frame-Condition.



/*
Problem: A ListableObject cannot be in the same list more than once!

Possible solution: 

abstract sig ListSignature{
	var LinkedList: ListableObjectCarrier -> ListableObjectCarrier,
	var startElement: lone ListableObjectCarrier
}

var sig ListableObjectCarrier {
	carriedElement: one ListableObject
}

//List Elements
let getAllListItemsOfCurrentTimeStep[list] {ListableObjectCarrier.((list).LinkedList).carriedElement + (((list).LinkedList).ListableObjectCarrier).carriedElement + ((list).startElement).carriedElement } 

//List Element Carrier
let getAllListItemCarrierOfCurrentTimeStep[list] {ListableObjectCarrier.((list).LinkedList) + ((list).LinkedList).ListableObjectCarrier + (list).startElement } 
let getAllAddedFutureElementCarrier[list] = {ListableObjectCarrier.((list).LinkedList') + ((list).LinkedList').ListableObjectCarrier + (list).startElement' } 


...

Problem with the potential solution: The returned set of a get-function cannot contain a doubly-listed element twice: For a given LinkedList: {ListableObject$0 -> ListableObject$0},  getListElementsFromIndex[list, 0, 2] = {ListableObject$0}

*/








abstract sig ListableObject{ }

abstract sig ListSignature{
	var LinkedList: ListableObject -> ListableObject,
	var startElement: lone ListableObject
}

pred unchangedList[list:ListSignature] {
	unchanged[list.startElement]
	unchanged[list.LinkedList]
}

let unchanged[r] { (r)' = (r) }

let getAllListItemsOfCurrentTimeStep[list] {ListableObject.((list).LinkedList) + ((list).LinkedList).ListableObject + (list).startElement } 
let getAllAddedFutureElements[list] = {ListableObject.((list).LinkedList') + ((list).LinkedList').ListableObject + (list).startElement' } 

pred keepListCorrectForNextStep[list: ListSignature] {
	// An element in a list can reference only one other element and be referenced only once.
	all ww:ListableObject | (#(ww->ListableObject & list.LinkedList')).lt[2] and (#(ListableObject -> ww & list.LinkedList')).lt[2] 
	//The startElement transitively (using ^) references every list element except itself. This implies there are no cycles and it's a connected chain.
	((getAllAddedFutureElements[list])-list.startElement' in list.startElement'.^(list.LinkedList')) and list.startElement' not in list.startElement'.^(list.LinkedList')
}


pred addListElementsAtIndex[list: ListSignature, index: Int, elements: set ListableObject]	{
	((index = getListLength[list]) or (index = 0 and no list.startElement and  no list.LinkedList))=> addToList[list,elements] else (
		(((index).gt[getListLength[list]]) or no elements) => unchangedList[list] else (
			index = 0 => (
				// Set startElement'
				(one starter: elements | list.startElement' = starter)

				and (#elements = 1 => (list.LinkedList' = list.LinkedList + {elements -> list.startElement} ) else (
					// Set list length
					(#list.LinkedList') = (#list.LinkedList).plus[#elements]
					// The old list is in the new list
					and list.LinkedList in list.LinkedList'
					// The startElement appears exactly once only on the left side of the list. All other elements appear exactly once on each side
					and (all elementsToAdd: elements-list.startElement' | {elementsToAdd+list.startElement'} in list.LinkedList'.ListableObject and elementsToAdd in ListableObject.(list.LinkedList'))
					// Connect the new section of the list with the old section of the list
					and (one lastToAdd: elements-list.startElement' | {lastToAdd -> list.startElement} in list.LinkedList' )
				))
				// Ensure the list is still valid for the next step
				and keepListCorrectForNextStep[list]
			)	else	(
				// The old {LinkedList - index-1 -> index} is in the new LinkedList
				{list.LinkedList - {getListElementsFromIndex[list,index.minus[1],1] -> getListElementsFromIndex[list,index,1]}}  in list.LinkedList'
				// Set list length
				and (#list.LinkedList') = (#list.LinkedList).plus[#elements]
				
				// Elements appear exactly once on both sides. Adjust references from index-1 and lastAddedElement
				and (one firstAddedElement, lastAddedElement: elements | 
						((#elements).gte[2] => firstAddedElement != lastAddedElement) 
						and ({{getListElementsFromIndex[list,index.minus[1],1] -> firstAddedElement} + {lastAddedElement -> getListElementsFromIndex[list,index,1]}} in list.LinkedList') 
						and (elements in list.LinkedList'.ListableObject and elements-list.startElement' in ListableObject.(list.LinkedList')))

				and keepListCorrectForNextStep[list]
				// Frame condition for startElement
				and list.startElement' = list.startElement
			)
		)
	)
}


pred addToList[list: ListSignature, elements: set ListableObject]	{
	// Set the start element / frame condition for startElement
	no list.startElement => (one starter: elements | list.startElement' = starter) else list.startElement' = list.startElement
	// The old list is in the new list
	list.LinkedList in list.LinkedList'
	// The startElement appears exactly once only on the left side of the list and the last element appears exactly once only on the right side of the list. All other elements appear exactly once on each side
	(one list.startElement or (#elements).gte[2]) => one lastToAdd: elements-list.startElement' | elements-lastToAdd in list.LinkedList'.ListableObject and elements-list.startElement' in ListableObject.(list.LinkedList')
	
    // Set the list length, ensuring only elements set by ... in LinkedList.list' are included, and no random additional ones.
	no list.startElement  => #list.LinkedList' = (#elements).minus[1] else #list.LinkedList' = (#list.LinkedList).plus[#elements]
	keepListCorrectForNextStep[list]
}

fun getLastListElement[list: ListSignature]: one ListableObject	{
	{ListableObject.(list.LinkedList) - (list.LinkedList).ListableObject}
}

fun getListElementsFromIndex[list:ListSignature, index: Int, howManyElements: Int]: set ListableObject	{
	/*
	Es werden alle Elemente zurückgegeben für die gilt: Transitive Verkettung > (Anzahl an Listenrelationen - Anzahl(zurückzugebende Elemente) - Index) and < (Transitive Verkettung(Element <= Listenlänge - Index)
	All elements are returned for which: Transitive concatenation > (Number of list relations - Number(elements to return) - Index) and < (Transitive concatenation(Element <= List length - Index)
	*/
	{elems: getAllListItemsOfCurrentTimeStep[list]  | #(elems.^(list.LinkedList)) > (#list.LinkedList).minus[howManyElements.plus[index]] and #(elems.^(list.LinkedList)) < (#list.LinkedList).minus[index.minus[1]] }
}

// There's no possibility to throw exceptions. Instead, the list will remain unchanged in the next step!
pred removeElementsFromIndex[list:ListSignature, index: Int, howManyElements: Int]	{
	(index.lt[0] or howManyElements.lte[0]) => unchangedList[list] else index = 0 => removeElementsFromIndexZero[list,howManyElements] else (
		index >= #getAllListItemsOfCurrentTimeStep[list] => unchangedList[list] else (
			index.plus[howManyElements] >= #getAllListItemsOfCurrentTimeStep[list] => (
				list.LinkedList' = {list.LinkedList - {getListElementsFromIndex[list,index.minus[1],1].^(list.LinkedList) -> ListableObject + ListableObject -> getListElementsFromIndex[list,index.minus[1],1].^(list.LinkedList)}}
				and list.startElement' = list.startElement
			) else (
				{getListElementsFromIndex[list,index.minus[1],1] -> getListElementsFromIndex[list,index.plus[howManyElements],1]} in list.LinkedList'
				and (all restOfList: {getListElementsFromIndex[list,index.plus[howManyElements.minus[1]],1].^(list.LinkedList) +  { beforeIndex :getAllListItemsOfCurrentTimeStep[list] | #(beforeIndex.^(list.LinkedList)) > (#getAllListItemsOfCurrentTimeStep[list]).minus[index]}}| {restOfList -> (restOfList.(list.LinkedList))} in list.LinkedList')
				and #list.LinkedList' = (#list.LinkedList).minus[howManyElements]
				and list.startElement' = list.startElement
			)
		)
	)
}

private pred removeElementsFromIndexZero[list: ListSignature, howManyElements: one Int] {
	// If no elements can be removed, keep the list unchanged
	((no list.LinkedList and no list.startElement) or howManyElements.lte[0] ) => unchangedList[list] else (
		// Remove elements: 1. Delete entire list and startElement if howManyElements > getListLength[list]
		howManyElements >= getListLength[list] => no list.startElement' and no list.LinkedList' else (
			// If the LinkedList needs to be deleted
			howManyElements = (getListLength[list]).minus[1] => (
				no list.LinkedList' and list.startElement' = getLastListElement[list]
			) else (
				 // 3. Set startElement
				(all elems: list.LinkedList.ListableObject - getElementsFIFO[list, howManyElements]  | #elems.^(list.LinkedList) = (#list.LinkedList).minus[howManyElements] => list.startElement' = elems )
				//4.. Alle übrigen Elemente der Liste hinzufügen und die entfernten not in getAllAddedFutureElements: Wenn ein Element Transitiv kürzer oder gleich lang verkettet ist als die Länger der Liste - howManyElements, dann ist sie mit ihrer alten relation weiterhin in der LinkedList enthalten. ansonsten kommt es im nächsten schritt nicht mehr in der Liste vor
				// 4. Add all remaining elements of the list and the removed ones not in getAllAddedFutureElements: If an element is transitively linked shorter or equal to the length of the list - howManyElements, then it remains in the LinkedList with its old relation. Otherwise, it will not appear in the list in the next step.
				and (all elems: list.LinkedList.ListableObject| #elems.^(list.LinkedList) <= (#list.LinkedList).minus[howManyElements] => ({elems -> (elems.(list.LinkedList))} in list.LinkedList') else elems not in getAllAddedFutureElements[list])
				
				// 5. Set list length
				and #list.LinkedList' = (#list.LinkedList).minus[howManyElements]
			)
		)
	)
}

pred clearList[list: ListSignature] {
	no list.startElement'
	no list.LinkedList'
}

fun getListLength[list: ListSignature]: one Int	{
	#(getAllListItemsOfCurrentTimeStep[list])
}

private fun getElementsFIFO[list: ListSignature, number: one Int]: set ListableObject {
	// If all elements need to be fetched from the list
	{number >= getListLength[list] => {getAllListItemsOfCurrentTimeStep[list]} else 
	// Otherwise: Each element that has a transitive chaining greater than the list's length minus the number of elements to be fetched is returned.
	{elems: getAllListItemsOfCurrentTimeStep[list]  | #(elems.^(list.LinkedList)) > (#list.LinkedList).minus[number]}
	}
}

//This has to be called before using popElementsFIFO: popElementsFIFO = getElementsFIFO AND no getElementsFIFO => unchangedList[list] 
fun popElementsFIFO[list: ListSignature, number: one Int]: set ListableObject {
	{removeElementsFromIndexZero[list,number] => {getElementsFIFO[list, number]} else {none}}
}


















//list checks
pred noObjectMultipleTimesInLeftOrRightSideOfList {
	all list: ListSignature | all ww:ListableObject | #(ListableObject->ww & list.LinkedList') < 2 or #(ww->ListableObject & list.LinkedList') < 2
}