
sig Person {
    knows: set Person
}


fact noSelfKnow {
    all p: Person | not (p in p.knows)
}


pred example {
    some p: Person | some p.knows
}


run example for 3 Person
