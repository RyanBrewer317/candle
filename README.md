# Candle

Candle is an ongoing project to create a programming language in the Cedille family that targets the [FVM](https://github.com/SaberVM/FVM). Unfortunately I've disabled its use of the FVM for now because of some significant bugs, and I'm focusing on making the Cedille theory implemented correctly first. Thus there's just a slow interpreter at the moment.

Candle will use what I'll call the Intrinsic CDLE (based on this wonderful [dissertation](https://www.proquest.com/openview/23ab2f5eadbcc1951caf591838a891e3)) as the foundation of its type system. Primitive numerics, strings, and arrays will be added. This is a significant detail because Cedilles are generally just pure untyped lambda calculus at runtime, and therefore can't reach a stuck state, but that won't be true of Candle.

The core logic is all implemented now; check the `main.cd` file to see what currently typechecks and runs!
