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

fact "Item ownership is reflexive" {
	all i : Item, ih : ItemHolder |
		(i.owner = ih => i in ih.inventory) and
		(i in ih.inventory => i.owner = ih)
}

fact "Item owner can't bid in their own auction" {
	all a : Auction |
		(no a.seller) or
		(a.seller != a.highestBidder && a.seller != a.buyoutBidder)
}

fact "Items must not appear in multiple auctions" {
	all a1, a2 : Auction |
		a1.auctionStatus = Active &&
		a2.auctionStatus = Active &&
		a1 != a2 => a1.forSale != a2.forSale
}

/*
	FRAME CONDITIONS
*/

pred SetOfItemsIsUnchanged[itemSet : set Item] {
	all items : itemSet | items' = items
}

pred SetOfPlayersIsUnchanged[playerSet : set Player] {
	all players : playerSet | players' = players
}

pred AuctionHouseIsUnchanged[i : Item] {
	AuctionHouse.balance' = AuctionHouse.balance
	all items : AuctionHouse.inventory - i |
		(items in AuctionHouse.inventory => items in AuctionHouse.inventory') and
		(items.owner' = items.owner)
}

/*
	OPERATIONS
*/

pred createAuction [i : Item, p : Player, a : Auction] {
	// Preconditions
	// 1. The Item must not be already listed in another Auction.
	no otherAuctions : (Auction - a) | otherAuctions.forSale = i
	i.itemStatus = NotForSale

	// 2. The Player must own the item.
	i.owner = p

	// 3. The Auction must be inactive.
	a.auctionStatus = NotStarted

	// 4. The Player must have at least 1 gold in order to sell something.
	gte[p.balance, 1]

	// Post-conditions
	// 1. The Item ownership is transferred to the Auction House and removed from the seller's inventory.
	i.owner' = AuctionHouse
	AuctionHouse.inventory' = AuctionHouse.inventory + i
	p.inventory' = (p.inventory - i)

	// 2. The Item status is set to ForSale.
	i.itemStatus' = ForSale

	// 3. The Auction status is set to "just started".
	a.auctionStatus' = JustStarted

	// 4. The Item is set as the sellee, Player is set as the seller.
	a.forSale' = i
	a.seller' = p

	// 5. There are no bidders.
	no a.highestBidder
	no a.buyoutBidder

	// 6. The Player pays a tax of 1 gold to list the item.
	p.balance' = sub[p.balance, 1]

	Track.op' = CREATE

	// Frame conditions
	// 1. Items unrelated to the Auction should remain the same.
	// (This includes the other items in the Seller's inventory.)
	SetOfItemsIsUnchanged[Item - i]
	SetOfItemsIsUnchanged[p.inventory - i]

	// 2. The other Player's  should remain the same.
	SetOfPlayersIsUnchanged[(Player - p)]

	// 3. The Auction House retains its attributes: it keeps its balance and
	// all the other previously listed items.
	AuctionHouseIsUnchanged[i]
}

pred bidOnAuction [p : Player, a : Auction] {
	// Preconditions
	// 1. The Player to bid must be different from the seller.
	p != a.seller

	// 2. The Auction must be Active (i.e., at most, at the third round).
	a.auctionStatus = Active

	// 3. The Player must not already be the highest bidder.
	a.highestBidder != p

	// Postconditions
	// 1. The Player becomes the highest bidder.
	a.highestBidder' = p

	Track.op' = BID
}

/*
	INITIAL STATE
*/

pred init [] {
	// There is only one Auction House
	one AuctionHouse

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
	(some i : Item, p : Player, a : Auction | createAuction[i, p, a])
	// or
	// (after some a : Auction | some p : Player |  bidOnAuction[p, a])
}

/*
	SYSTEM PREDICATE
*/

pred System {
	init
	// always trans
	trans
}

run execution { System } for 10