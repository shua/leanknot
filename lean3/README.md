This repository holds some formalizations of knot theory proofs in lean.

Currently planning on:

- [x] underlying representation of bricks/walls [basic]
- [x] notion of planar isotopy equivalence [basic]
- [x] notion of reidemeister move equivalence [basic]
- [ ] proof that brick/wall notions of equivalency are sufficient
- [x] definition of tangle [tangle]
- [ ] inductive notion of tangle equivalency (will allow greater application of r-move and planar iso equiv)
- [x] proof of tangle invariance across notions of equivalence [tangle]
- [x] definition of link [link]
- [ ] definition of knot
- [x] definition of braid [scratch]
- [ ] definition of permutation, proof that braid is a permutation

Not quite sure about the following:

- [ ] notion of tri-colourability
- [ ] notion of alternating
- [ ] HOMFLY/Jones polynomials


[basic]: src/basic.lean
[tangle]: src/tangle.lean
[link]: src/link.lean
[scratch]: src/scratch.lean
