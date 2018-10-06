# Casino

Repository of cryptographic primitives, benchmarks and implementations of our
research around Multi Party Computation (MPC) and their applications to
card games.

Our main research papers:

* [Kaleidoscope: An Efficient Poker Protocol with Payment Distribution and Penalty Enforcement](https://eprint.iacr.org/2017/899.pdf)
* [ROYALE: A Framework for Universally Composable Card Games with Financial Rewards and Penalties Enforcement](https://files.zotero.net/4350901438/Royale-5.pdf)
* [21 - Bringing Down the Complexity: Fast Composable Protocols for Card Games Without Secret State](https://eprint.iacr.org/2018/303.pdf)

## Breakdown

* casino-prim contains basic crypto ECC, ZKP (DLEQ, DLOG), some data types (Matrix) and some general small utilities
* shuffle-proof contains the zero knowledge proof of shuffle as per [Efficient Zero-Knowledge Argument for Correctness of a Shuffle](http://www0.cs.ucl.ac.uk/staff/J.Groth/MinimalShuffle.pdf)
* poker contains the cards, some poker related things, and a EDSL for poker event processing based on a cooperative non-blocking loop. It is an almost complete simulator of the Kaleidoscope paper, without the betting procedure and the signatures.
