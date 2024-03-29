This repository holds some formalizations of knot theory proofs in lean.

Currently planning on:

- [x] underlying representation of bricks/walls [basic]
- [x] notion of planar isotopy equivalence [basic]
- [x] notion of reidemeister move equivalence [basic]
- [ ] proof that brick/wall notions of equivalency are sufficient (not sure how to do this?)
- [x] definition of tangle [tangle]
- [ ] tangle surgery or inductive notion of tangle equivalency
- [x] proof of tangle invariance across notions of equivalence [tangle]
- [x] definition of link [link]
- [x] definition of knot [link]
- [x] definition of braid [braid]
- [ ] definition of permutation, proof that braid is a permutation

Not quite sure about the following:

- [ ] notion of tri-colourability
- [ ] notion of alternating
- [ ] HOMFLY/Jones polynomials


[basic]: Basic.lean
[tangle]: Tangle.lean
[link]: Link.lean
[braid]: Braid.lean

## References
- Prathamesh, T. V. H. (2015). Formalising Knot Theory in Isabelle/HOL. Lecture Notes in Computer Science, 438–452. [doi:10.1007/978-3-319-22102-1_29](https://dx.doi.org/10.1007/978-3-319-22102-1_29) / [prathamesh-t/Tangle-Isabelle](https://github.com/prathamesh-t/Tangle-Isabelle/)
