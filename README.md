# Candle

Candle is an ongoing project to create a programming language in the Cedille family that targets the [FVM](https://github.com/SaberVM/FVM).

Candle will use what I'll call the Intrinsic CDLE (based on this wonderful [dissertation](https://www.proquest.com/openview/23ab2f5eadbcc1951caf591838a891e3)) as the foundation of its type system. Primitive numerics, strings, and arrays will be added. This is a significant detail because Cedilles are generally just pure untyped lambda calculus at runtime, and therefore can't reach a stuck state, but that won't be true of Candle.

The core logic is like half-ish implemented now.
![image](https://github.com/user-attachments/assets/943d2c54-ad4c-4a56-9b80-c37e8ca370b9)
