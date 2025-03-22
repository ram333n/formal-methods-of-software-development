class PaymentCard {
    const id: int
    var numberOfTrips: int

    constructor(id: int, numberOfTrips: int) 
        requires 0 < id <= 1000000
        requires numberOfTrips >= 0
        ensures 0 < this.id <= 1000000
        ensures this.numberOfTrips >= 0
    {
        this.id := id;
        this.numberOfTrips := numberOfTrips;
    }
}

class CreditCard {
    var balance: real

    constructor(balance: real) 
        requires balance >= 0.0
        ensures this.balance >= 0.0
    {
        this.balance := balance;
    }
}

class Terminal {
    constructor() {}
    
    method payWithPaymentCard(card: PaymentCard, passengersCount: int)
        modifies card
        requires card.numberOfTrips >= 0
        requires passengersCount > 0
        ensures card.numberOfTrips >= 0
        ensures !canPayWithPaymentCard(old(card.numberOfTrips), passengersCount) ==> card.numberOfTrips == old(card.numberOfTrips)
    {
        if !canPayWithPaymentCard(card.numberOfTrips, passengersCount) {
            print "Not enough number of trips on payment card. Provided: ", card.numberOfTrips, ", ", "expected: ", passengersCount, "\n";
            return;
        }

        card.numberOfTrips := card.numberOfTrips - passengersCount;
        print "Payment with payment card was successful. Payed: ", passengersCount, ", ", "remaining trip count: ", card.numberOfTrips, "\n"; 
    }

    predicate canPayWithPaymentCard(numberOfTripsOnCard: int, passengersCount: int) 
        requires numberOfTripsOnCard >= 0
        requires passengersCount > 0
    {
        numberOfTripsOnCard >= passengersCount
    }

    function evaluatePrice(pricePerPassenger: real, passengersCount: int): real
        requires pricePerPassenger > 0.0
        requires passengersCount > 0
        ensures evaluatePrice(pricePerPassenger, passengersCount) > 0.0
    {
        (passengersCount as real) * pricePerPassenger
    }

    method payWithCreditCard(card: CreditCard, passengersCount: int, pricePerPassenger: real) 
        modifies card
        requires card.balance >= 0.0
        requires passengersCount > 0
        requires pricePerPassenger > 0.0
        ensures card.balance >= 0.0
        ensures !canPayWithCreditCard(old(card.balance), evaluatePrice(pricePerPassenger, passengersCount))
            ==> card.balance == old(card.balance)
    {
        var price := evaluatePrice(pricePerPassenger, passengersCount);

        if !canPayWithCreditCard(card.balance, price) {
            print "Not enough money. Balance: ", card.balance, ", ", "expected: ", price, "\n";
            return;
        }

        card.balance := card.balance - price;
        print "Payment with credit card was successful. Payed: ", price, ", ","Balance:", card.balance, "\n"; 
    }

    predicate canPayWithCreditCard(cardBalance: real, price: real) 
        requires cardBalance >= 0.0
        requires price > 0.0
    {
        cardBalance >= price
    }
}

method Main() 
{
    var terminal := new Terminal();

    var paymentCardId := 42;
    var initNumberOfTrips := 3;
    var paymentCard := new PaymentCard(paymentCardId, initNumberOfTrips);

    var initBalance := 25.0;
    var pricePerPassenger := 8.0;
    var creditCard := new CreditCard(initBalance);
    print "==============================Initial params==============================", "\n";
    print "Initial paymentCardId: ", paymentCardId, "\n";
    print "Initial initNumberOfTrips: ", initNumberOfTrips, "\n";
    print "Initial credit card balance: ", initBalance, "\n";
    print "Price per passenger: ", pricePerPassenger, "\n";

    print "==============================Start program==============================", "\n";
    terminal.payWithPaymentCard(paymentCard, 1);
    terminal.payWithPaymentCard(paymentCard, 2);
    terminal.payWithPaymentCard(paymentCard, 2);

    terminal.payWithCreditCard(creditCard, 1, pricePerPassenger);
    terminal.payWithCreditCard(creditCard, 2, pricePerPassenger);
    terminal.payWithCreditCard(creditCard, 1, pricePerPassenger);
}