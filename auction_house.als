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

pred UpdateAuctionStatus[auctionSet : set Auction] {
	all auctions : auctionSet |
		(auctions.auctionStatus = JustStarted => auctions.auctionStatus' = FirstRound) and
		(auctions.auctionStatus = FirstRound => auctions.auctionStatus' = SecondRound) and
		(auctions.auctionStatus = SecondRound => auctions.auctionStatus' = ThirdRound) and
		(auctions.auctionStatus = ThirdRound => auctions.auctionStatus' = Ended)
}

/*
	FRAME CONDITIONS
*/

pred SetOfAuctionsIsUnchanged[auctionSet : set Auction] {
	all auctions : auctionSet |
		(auctions.seller' = auctions.seller) and
		(auctions.forSale' = auctions.forSale) and
		(auctions.highestBidder' = auctions.highestBidder) and
		(auctions.buyoutBidder' = auctions.buyoutBidder)
}

pred SetOfItemsIsUnchanged[itemSet : set Item] {
	all items : itemSet |
		(items.owner' = items.owner) and
		(items.itemStatus'= items.itemStatus)
}

pred SetOfPlayersIsUnchanged[playerSet : set Player] {
	all players : playerSet |
		(players.inventory' = players.inventory) and
		(players.balance' = players.balance)
}

pred AuctionHouseIsUnchanged[itemSet : set Item] {
	AuctionHouse.balance' = AuctionHouse.balance
	all items : itemSet |
		(items in AuctionHouse.inventory => items in AuctionHouse.inventory') and
		(items.owner' = items.owner) and
		(items.itemStatus' = items.itemStatus)
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
	a.highestBidder' = none
	a.buyoutBidder' = none

	// 6. The Player pays a tax of 1 gold to list the item.
	p.balance' = sub[p.balance, 1]

	// Internal management
	// 1. Track the operation
	Track.op' = CREATE

	// 2. Update the status of other auctions
	UpdateAuctionStatus[Auction - a]

	// Frame conditions
	// 1. Items unrelated to the Auction should remain the same.
	// (This includes the other items in the Seller's inventory.)
	SetOfItemsIsUnchanged[Item - i]
	SetOfItemsIsUnchanged[p.inventory - i]

	// 2. The other Player's  should remain the same.
	SetOfPlayersIsUnchanged[Player - p]

	// 3. The Auction House retains its attributes: it keeps its balance and
	// all the other previously listed items.
	AuctionHouseIsUnchanged[AuctionHouse.inventory - i]

	// 4. Other Auctions should remain the same.
	SetOfAuctionsIsUnchanged[Auction - a]
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

	// Internal management
	// 1. Track the operation
	Track.op' = BID

	// 2. Update all the auctions' status
	// TOOD: make UpdateAuctionStatus and this predicate consistent
	// UpdateAuctionStatus[Auction]

	// Frame conditions
	// 1. Items unrelated to the Auction should remain the same.
	SetOfItemsIsUnchanged[Item]

	// 2. The other Player's  should remain the same.
	SetOfPlayersIsUnchanged[Player]

	// 3. The Auction House retains its attributes: it keeps its balance and
	// all the other previously listed items.
	AuctionHouseIsUnchanged[AuctionHouse.inventory]

	// 4. Other Auctions should remain the same.
	SetOfAuctionsIsUnchanged[Auction - a]

	// 5. Other attributes of `a`, except for the highest bidder, must
	// remain the same.
	a.seller' = a.seller
	a.forSale' = a.forSale
	a.buyoutBidder' = a.buyoutBidder
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
	(after some a : Auction, p : Player | bidOnAuction[p, a])
}

/*
	SYSTEM PREDICATE
*/

pred System {
	init
	trans
}

run execution { System } for 10