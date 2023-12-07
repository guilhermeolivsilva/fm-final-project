/*
	DCC831 Formal Methods 2023.2
	Final Project – Auction House

	Name:  Guilherme de Oliveira Silva
	ID: 
*/

/*
	PACKAGES
*/
open util/integer

/*
	SIGNATURES
*/

// Auction
abstract sig AuctionStatus {}
one sig NotStarted, Active, Ended extends AuctionStatus {}
sig JustStarted, FirstRound, SecondRound, ThirdRound extends Active {}
sig Auction {
	var seller: lone Player,
	var forSale: lone Item,
	var auctionStatus: one AuctionStatus,
	var highestBidder: lone Player,
	var buyoutBidder: lone Player
}

// Item
abstract sig ItemStatus {}
one sig ForSale, NotForSale extends ItemStatus {}
sig Item {
	var owner: lone ItemHolder,
	var itemStatus: one ItemStatus
}

// Player/Auction House
abstract sig ItemHolder {
	var inventory: set Item,
	var balance: Int
}
sig Player, AuctionHouse extends ItemHolder{}

/*
	OPERATORS

	CREATE:				create auction
	END:		 		end auction
	BID:		 		bid on auction
	BUY:		 		buyout auction
*/

abstract sig Operator {}
one sig CREATE, END, BID, BUY, TAX extends Operator {}
one sig Track {
  var op: lone Operator
}

/*
	AUXILIARY PREDICATES AND FACTS
*/

pred otherAuctionsStayTheSame [a : set Auction] {
	all otherAuctions : a | otherAuctions.seller' = otherAuctions.seller
	all otherAuctions : a | otherAuctions.forSale' = otherAuctions.forSale
	all otherAuctions : a | otherAuctions.auctionStatus' = otherAuctions.auctionStatus
	all otherAuctions : a | otherAuctions.highestBidder' = otherAuctions.highestBidder
	all otherAuctions : a | otherAuctions.buyoutBidder' = otherAuctions.buyoutBidder
}

pred otherItemsStayTheSame [i : set Item] {
	all otherItems : i | otherItems.owner' = otherItems.owner
	all otherItems : i | otherItems.itemStatus' = otherItems.itemStatus
}

pred otherItemHoldersStayTheSame [ih : set ItemHolder] {
	all otherItemHolders : ih | otherItemHolders.inventory' = otherItemHolders.inventory
	all otherItemHolders : ih | otherItemHolders.balance' = otherItemHolders.balance
}

pred updateAuctionsStatus [a : set Auction] {
	all otherAuctions : a |
		otherAuctions.auctionStatus = ThirdRound => otherAuctions.auctionStatus' = Ended

	all otherAuctions : a |
		otherAuctions.auctionStatus = SecondRound => otherAuctions.auctionStatus' = ThirdRound

	all otherAuctions : a |
		otherAuctions.auctionStatus = FirstRound => otherAuctions.auctionStatus' = SecondRound

	all otherAuctions : a |
		otherAuctions.auctionStatus = JustStarted => otherAuctions.auctionStatus' = FirstRound
}

fact "Item ownership is reflexive" {
	all i : Item, ih : ItemHolder |
		(i.owner = ih => i in ih.inventory) &&
		(i in ih.inventory => i.owner = ih)
}

fact "Item owner can't bid in their own auction" {
	all a : Auction |
		(no a.seller) ||
		(a.seller != a.highestBidder && a.seller != a.buyoutBidder)
}

fact "Items must not appear in multiple auctions" {
	all a1, a2 : Auction |
		a1.auctionStatus = Active &&
		a2.auctionStatus = Active &&
		a1 != a2 => a1.forSale != a2.forSale
}

/*
	OPERATIONS
*/

/*
	KNOWN BUGS
	1. An Auction status does not hold between steps.
	2. The item.owner relation does not hold between steps.
	3. The item.itemStatus relation does not hold between steps.
*/
pred createAuction [i : Item, p : Player, a : Auction] {
	/*
		Preconditions
		1. The Item must not be already listed in another Auction.
		2. The Item must belong to the seller.
		3. The Auction must be inactive.
	*/
	no otherAuctions : (Auction - a) | otherAuctions.forSale = i
	i.itemStatus = NotForSale
	i.owner = p
	a.auctionStatus = NotStarted

	/*
		Post-conditions
		1. The Item ownership is transferred to the Auction House and removed from the seller's inventory.
		2. The Item status is set to ForSale.
		3. The Auction status is set to "just started".
		4. There are no bidders.
	*/
	i.owner' = AuctionHouse
	AuctionHouse.inventory' = AuctionHouse.inventory + i
	p.inventory' = (p.inventory - i)
	i.itemStatus' = ForSale
	a.auctionStatus' = JustStarted
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
	// TODO: fix the parameters
	// otherItemHoldersStayTheSame[p]
	// otherItemsStayTheSame[i]
	// otherAuctionsStayTheSame[a]
	// updateAuctionsStatus[a]
}

pred bidOnAuction [p : Player, a : Auction] {
	/*
		Preconditions
		1. The Player to bid must be different from the seller.
		2. The Auction must be Active (i.e., at most, at the third round).
		3. The Player must not already be the highest bidder.
	*/
	p != a.seller
	a.auctionStatus = Active
	a.highestBidder != p

	/*
		Postconditions
		1. The Player becomes the highest bidder.
	*/
	a.highestBidder' = p

	Track.op' = BID
}

/*
	INITIAL STATE
*/

pred init [] {
	// No initial operation to track
	no op

	// No Auctions have yet started
	all a : Auction | a.auctionStatus = NotStarted

	// No Items nor Players are associated with any Auctions
	no Auction.highestBidder
	no Auction.buyoutBidder
	no Auction.seller
	no Auction.forSale

	// No Items are for sale
	all i : Item | i.itemStatus = NotForSale
	no AuctionHouse.inventory

	// All Items have a Player owner
	all i : Item | some p : Player | i.owner = p

	// All Players start with 3 gold
	all p : Player | p.balance = 3

	// The Auction House starts with no gold
	AuctionHouse.balance = 0
}

/*
	TRANSITION RELATION
*/

pred trans []  {
	// (some i : Item, p : Player, a : Auction | createAuction[i, p, a])
	// or
	(after some a : Auction | some p : Player |  bidOnAuction[p, a])
}

/*
	SYSTEM PREDICATE
*/

pred System {
	init
	always trans
}

run execution { System } for 10