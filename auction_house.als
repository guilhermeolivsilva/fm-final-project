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
one sig NotStarted, Active, Ended extends AuctionStatus {}

sig Auction {
	var seller: lone Player,
	var forSale: lone Item,
	var auctionStatus: one AuctionStatus,
	var highestBidder: lone Player,
	var buyoutBidder: lone Player
}

abstract sig ItemStatus {}
one sig ForSale, NotForSale extends ItemStatus {}

sig Item {
	var owner: lone ItemHolder,
	var itemStatus: one ItemStatus
}

abstract sig ItemHolder {
	var inventory: set Item
}

sig Player, AuctionHouse extends ItemHolder{}

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
	PREDICATES AND FACTS
*/

fact "Ownership is reflexive" {
	all i : Item, ih : ItemHolder |
		(i.owner = ih => i in ih.inventory) && (i in ih.inventory => i.owner = ih)
}

fact "Item owner can't bid in their own auction" {
	all a : Auction |
		(no a.seller) || (a.seller != a.highestBidder && a.seller != a.buyoutBidder)
}

fact "Items must not appear in multiple auctions" {
	all a1, a2 : Auction | a1.auctionStatus = Active && a1 != a2 => a1.forSale != a2.forSale
}



/*
	OPERATIONS
*/

pred createAuction [i : Item, p : Player, a : Auction] {
	/*
		Preconditions
		1. The Item must not be already listed in another Auction.
		2. The Item must belong to the seller.
		3. The Auction must be inactive.
	*/
	no otherAuction : Auction | otherAuction.forSale = i
	i.itemStatus = NotForSale
	i.owner = p
	a.auctionStatus = NotStarted

	/*
		Post-conditions
		1. The Item ownership is transferred to the Auction House.
		2. The Item status is set to ForSale.
		3. The Auction status is set to active.
		4. There are no bidders.
	*/
	i.owner' = AuctionHouse
	i.itemStatus' = ForSale
	a.auctionStatus' = Active
	a.forSale' = i
	a.seller' = p
	no a.highestBidder
	no a.buyoutBidder
	Track.op' = CREATE

	/*
		Frame conditions
		1. Other Items in the Player p's inventory should remain the same.
		2. The other Player's relations should remain the same.
		3. The other Auctions' relations should remain the same.
	*/
	all otherItems : (p.inventory - i) | otherItems' = otherItems
	all otherPlayers : (Player - p) | otherPlayers.inventory' = otherPlayers.inventory
}

/*
	INITIAL STATE
*/

pred init [] {
	// No initial operation to track
	no op

	// No Auctions have started or finished
	all a : Auction | a.auctionStatus = NotStarted

	// No Items nor Players are associated with any Auctions
	no Auction.highestBidder
	no Auction.buyoutBidder
	no Auction.seller
	no Auction.forSale

	// No Items are for sale
	all i : Item | i.itemStatus = NotForSale
}

/*
	TRANSITION RELATION
*/

pred trans []  {
	(some i : Item, p : Player, a : Auction | createAuction[i, p, a])
}

/*
	SYSTEM PREDICATE
*/

pred System {
	init
   always trans
}

run execution { System } for 8
