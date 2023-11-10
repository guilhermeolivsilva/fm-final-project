/*
	DCC831 Formal Methods 2023.2
	Final Project – Auction House

	Name:  Guilherme de Oliveira Silva
	ID: 
*/

/*
	SIGNATURES
*/
abstract sig AuctionStatus {}
one sig AuctionActive, AuctionEnded extends AuctionStatus {}

sig Auction {
	seller: one Player,
	forSale: one Item,
	var currentAuctionStatus: one AuctionStatus,
	var highestBidder: some Player,
	var buyoutBidder: some Player
}

abstract sig ItemStatus {}
one sig ItemForSale, ItemNotForSale extends ItemStatus {}

sig Item {
	var owner: lone Player,
	var currentItemStatus: one ItemStatus
}

sig Player {
	var backpack: set Item
}

/*
	OPERATORS

	CREATE:		create auction
	END:		 		end auction
	BID:		 		bid on auction
	BUY:		 		buyout auction
*/

abstract sig Operator {}
one sig CREATE, END, BID, BUY extends Operator {}
one sig Track {
  var op: lone Operator
}

/*
	INITIAL STATE
*/

pred init [] {
}

/*
	TRANSITION RELATION
*/

pred trans []  {
}

/*
	SYSTEM PREDICATE
*/

pred System {
	init
   always trans
}

run execution { System } for 8
