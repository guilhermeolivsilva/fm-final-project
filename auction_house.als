/*
	DCC831 Formal Methods 2023.2
	Final Project – Auction House

	Name:  Guilherme de Oliveira Silva
	ID: 2023671528
*/

/*
	PACKAGES
*/
open util/integer

/*
	SIGNATURES
*/

// Player/Auction House
abstract sig ItemHolder {
	var inventory: set Item,
	var balance: Int
}
sig Player, AuctionHouse extends ItemHolder{}

// Item
abstract sig ItemStatus {}
one sig ForSale, NotForSale extends ItemStatus {}
sig Item {
	var owner: lone ItemHolder,
	var itemStatus: one ItemStatus
}

// Auction
abstract sig AuctionStatus {}
one sig NotStarted, Active, AuctionHasBeenSold, AuctionHasNotBeenSold, Ended extends AuctionStatus {}
sig JustStarted, FirstRound, SecondRound, ThirdRound extends Active {}
sig Auction {
	var seller: lone Player,
	var listedItem: lone Item,
	var auctionStatus: one AuctionStatus,
	var highestBidder: lone Player,
	var buyoutBuyer: lone Player
}

/*
	OPERATORS

	CREATE:				create auction
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
	AUXILIARY PREDICATES AND FACTS
*/

fact "Item owner can't bid in their own auction" {
	all a : Auction |
		(no a.seller) or
		(a.seller != a.highestBidder and a.seller != a.buyoutBuyer)
}

fact "Item ownership is reflexive" {
	all i : Item, ih : ItemHolder |
		(i.owner = ih => i in ih.inventory) and
		(i in ih.inventory => i.owner = ih)
}

fact "Items must not appear in multiple auctions" {
	all a1, a2 : Auction |
		a1.auctionStatus = Active and
		a2.auctionStatus = Active and
		a1 != a2 => a1.listedItem != a2.listedItem
}

fact "Ended Auctions cannot restart" {
	all a : Auction | a.auctionStatus = Ended => a.auctionStatus' = Ended
}

fact "No balance can be negative" {
	always all ih : ItemHolder | gte[ih.balance, 0]
}

pred UpdateAuctionStatus[auctionSet : set Auction] {
	all auctions : auctionSet |
		(auctions.auctionStatus' = JustStarted => auctions.auctionStatus'' = FirstRound) and
		(auctions.auctionStatus' = FirstRound => auctions.auctionStatus'' = SecondRound) and
		(auctions.auctionStatus' = SecondRound => auctions.auctionStatus'' = ThirdRound) and
		(auctions.auctionStatus' = ThirdRound => auctions.auctionStatus'' = Ended)
}

/*
	FRAME CONDITIONS
*/

pred SetOfAuctionsIsUnchanged[auctionSet : set Auction] {
	all auctions : auctionSet |
		(auctions.seller' = auctions.seller) and
		(auctions.listedItem' = auctions.listedItem) and
		(auctions.highestBidder' = auctions.highestBidder) and
		(auctions.buyoutBuyer' = auctions.buyoutBuyer)
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

pred AuctionHouseInventoryIsUnchanged[itemSet : set Item] {
	all items : itemSet |
		(items in AuctionHouse.inventory => items in AuctionHouse.inventory') and
		(items.owner' = items.owner) and
		(items.itemStatus' = items.itemStatus)
}

pred AuctionHouseBalanceIsUnchanged[] {
	AuctionHouse.balance' = AuctionHouse.balance
}

/*
	OPERATIONS
*/

pred createAuction[i : Item, p : Player, a : Auction] {
	// Preconditions
	// 1. The Item must not be already listed in another Auction.
	no otherAuctions : (Auction - a) | otherAuctions.listedItem = i
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

	// 2. The Auction House receives the deposit tax
	AuctionHouse.balance' = add[AuctionHouse.balance, 1]

	// 3. The Item status is set to ForSale.
	i.itemStatus' = ForSale

	// 4. The Auction status is set to "just started".
	a.auctionStatus' = JustStarted

	// 5. The Item is set as the sellee, Player is set as the seller.
	a.listedItem' = i
	a.seller' = p

	// 6. There are no bidders.
	a.highestBidder' = none
	a.buyoutBuyer' = none

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

	// 3. The Auction House retains its attributes: it keeps all the other
	// previously listed items.
	AuctionHouseInventoryIsUnchanged[AuctionHouse.inventory - i]

	// 4. Other Auctions should remain the same.
	SetOfAuctionsIsUnchanged[Auction - a]
}

pred bidOnAuction[p : Player, a : Auction] {
	// Preconditions
	// 1. The Player to bid must be different from the seller.
	p != a.seller

	// 2. The Auction must be Active (i.e., at most, at the third round).
	a.auctionStatus = Active

	// 3. The Player must not already be the highest bidder.
	a.highestBidder != p

	// 4. The Player must have at least 1 gold to bid.
	gte[p.balance, 1]

	// Postconditions
	// 1. The Player becomes the highest bidder.
	a.highestBidder' = p

	// Internal management
	// 1. Track the operation
	Track.op' = BID

	// 2. Update all the auctions' status to the next round.
	UpdateAuctionStatus[Auction]

	// Frame conditions
	// 1. Items unrelated to the Auction should remain the same.
	SetOfItemsIsUnchanged[Item]

	// 2. The other Player's  should remain the same.
	SetOfPlayersIsUnchanged[Player]

	// 3. The Auction House retains its attributes: it keeps its balance and
	// all the other previously listed items.
	AuctionHouseInventoryIsUnchanged[AuctionHouse.inventory]
	AuctionHouseBalanceIsUnchanged[]

	// 4. Other Auctions should remain the same.
	SetOfAuctionsIsUnchanged[Auction - a]

	// 5. Other attributes of `a`, except for the highest bidder, must
	// remain the same.
	a.seller' = a.seller
	a.listedItem' = a.listedItem
	a.buyoutBuyer' = none
}

pred buyoutAuction[p : Player, a : Auction] {
	// Preconditions
	// 1. The Player to buyout must be different from the seller.
	p != a.seller

	// 2. The Auction must be Active (i.e., at most, at the third round).
	a.auctionStatus = Active

	// 3. The Player must have at least 1 gold to bid.
	gte[p.balance, 1]

	// Postconditions
	// 1. The Player becomes the buyout bidder. (And the highest bidder too,
	// for convenience.)
	a.buyoutBuyer' = p
	a.highestBidder' = p

	// 2. The Auction ends.
	a.auctionStatus' = AuctionHasBeenSold

	// Internal management
	// 1. Track the operations
	Track.op' = BUY

	// 2. Update the other auctions' status to the next round.
	UpdateAuctionStatus[Auction - a]

	// Frame conditions
	// 1. Items unrelated to the Auction should remain the same.
	SetOfItemsIsUnchanged[Item]

	// 2. The other Player's  should remain the same.
	SetOfPlayersIsUnchanged[Player]

	// 3. The Auction House retains its attributes: it keeps its balance and
	// all the other previously listed items.
	AuctionHouseInventoryIsUnchanged[AuctionHouse.inventory]
	AuctionHouseBalanceIsUnchanged[]

	// 4. Other Auctions should remain the same.
	SetOfAuctionsIsUnchanged[Auction - a]

	// 5. Other attributes of `a` must remain the same.
	a.seller' = a.seller
	a.listedItem' = a.listedItem
}

pred endSoldAuction[a : Auction] {
	// Preconditions
	// 1. The Auction must have been sold.
	a.auctionStatus' = AuctionHasBeenSold

	// Postconditions
	// 1. The Auction is marked as Ended.
	a.auctionStatus'' = Ended

	// 2. The Auction House's cut is collected.
	AuctionHouse.balance'' = add[AuctionHouse.balance', 1]

	// 3. The Players involved in the Auction exchange gold
	a.highestBidder'.balance'' = sub[a.highestBidder'.balance, 3]
	a.seller.balance'' = add[a.seller.balance', 2]

	// 4. The sold Item is transferred to the winning Player
	AuctionHouse.inventory'' = AuctionHouse.inventory' - a.listedItem
	a.listedItem.owner'' = a.highestBidder'
	a.highestBidder'.inventory'' = a.highestBidder.inventory' + a.listedItem

	// 5. The sold Item is listed as NotForSale.
	a.listedItem.itemStatus'' = NotForSale

	// Internal management
	// 1. Track the operations
	Track.op'' = END

	// Frame conditions
	// 1. Items unrelated to the Auction should remain the same.
	// (This includes the other items in the Seller's inventory.)
	SetOfItemsIsUnchanged[Item - a.listedItem]

	// 2. The other Player's  should remain the same.
	SetOfPlayersIsUnchanged[Player - a.highestBidder - a.seller]

	// 3. The Auction House retains its attributes: it keeps its balance and
	// all the other previously listed items.
	AuctionHouseInventoryIsUnchanged[AuctionHouse.inventory - a.listedItem]

	// 4. Other Auctions should remain the same.
	SetOfAuctionsIsUnchanged[Auction - a]
}

pred endUnsoldAuction[a : Auction] {
	// Preconditions
	// 1. The Auction must have been sold.
	a.auctionStatus' = AuctionHasNotBeenSold

	// Postconditions
	// 1. The Auction is marked as Ended.
	a.auctionStatus'' = Ended

	// 2. The unsold Item is returned to the original owner
	AuctionHouse.inventory'' = AuctionHouse.inventory' - a.listedItem
	a.listedItem.owner'' = a.seller'
	a.seller'.inventory'' = a.seller.inventory' + a.listedItem

	// 3. The sold Item is listed as NotForSale.
	a.listedItem.itemStatus'' = NotForSale

	// Internal management
	// 1. Track the operations
	Track.op'' = END

	// Frame conditions
	// 1. Items unrelated to the Auction should remain the same.
	// (This includes the other items in the Seller's inventory.)
	SetOfItemsIsUnchanged[Item - a.listedItem]

	// 2. The other Player's  should remain the same.
	SetOfPlayersIsUnchanged[Player'' - a.seller]

	// 3. The Auction House retains its attributes: it keeps its balance and
	// all the other previously listed items.
	AuctionHouseInventoryIsUnchanged[AuctionHouse.inventory - a.listedItem]

	// 4. Other Auctions should remain the same.
	SetOfAuctionsIsUnchanged[Auction - a]
}

/*
	INITIAL STATE
*/

pred init[] {
	// There is only one Auction House
	always one AuctionHouse

	// No initial operation to track
	no op

	// No Auctions have yet started
	all a : Auction | a.auctionStatus = NotStarted

	// No Items nor Players are associated with any Auctions
	no Auction.highestBidder
	no Auction.buyoutBuyer
	no Auction.seller
	no Auction.listedItem

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

pred trans[] {
	some i : Item, p : Player, a : Auction | createAuction[i, p, a]
	after some a : Auction, p : Player |
		(buyoutAuction[p, a] or bidOnAuction[p, a])
		and (endSoldAuction[a] or endUnsoldAuction[a])
}

/*
	SYSTEM PREDICATE
*/

pred System {
	init
	trans
}

run execution { System } for 8


/*
	PROPERTIES
*/

pred p1 {
	// No Player can bid on their own Auction.
	all a : Auction |
		(a.seller != a.highestBidder and a.seller != a.buyoutBuyer) or
		no a.seller
}

pred p2 {
	// Every Item belongs to exactly 1 owner.
	all i : Item | #i.owner = 1
}

pred p3 {
	// A Player must have owned the Item they're selling.
	all a : Auction | all p : Player | a.seller' = p => a.listedItem' in p.inventory
}

pred p4 {
	// A bought out Auction ends instantly.
	Track.op = BUY => Track.op' = END
}

pred p5 {
	// A Player that buys out an Auction had at least 2 gold before.
	all p : Player | Track.op' = BUY => gte[p.balance, 2]
}

pred p6 {
	// A Player that sells an Item receives 1 gold.
	all p : Player | Track.op' = END => eq[p.balance', add[p.balance, 1]]
}

pred p7 {
	// When the execution ends, the Auction House's inventory must be empty.
	Track.op = END => AuctionHouse.inventory = none
}

/*
	ASSERTIONS
*/

assert checkP1 { System => p1 }
check checkP1


assert checkP2 { System => p2 }
check checkP2

assert checkP3 { System => p3 }
check checkP3

assert checkP4 { System => p4 }
check checkP4

assert checkP5 { System => p5 }
check checkP5

assert checkP6 { System => p6 }
check checkP6

assert checkP7 { System => p7 }
check checkP7