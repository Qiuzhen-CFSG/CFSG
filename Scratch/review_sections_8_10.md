# Independent audit: Sections 8--10

This audit compares the current Lean statements with direct 600dpi/PDF reads
of pages 37--60 (`pdftoppm` pages 27--50). No production files were edited.

## Confirmed discrepancies

1. **(8.2) wrong hypothesis direction and wrong object in conclusion.** PDF p.37 says
   `Suppose that Z_{a+1} \nleq Z(G_{a+1})`; current `LemmaEightTwo` takes
   `hcenter : ZAt ... firstStep ≤ CenterAmbient (...)`, the opposite condition.
   The PDF conclusion is `\bar G_d ≅ Σ_4` or `\bar G_d ≅ C_2 × Σ_4` for every d,
   where the notation immediately above defines `\bar G_d = G_d/C_{G_d}(Z_d)`.
   Current conclusion is `IsModel (GAt d) S4 ∨ IsModel (GAt d) (C2 × S4)`,
   i.e. unbarred local groups and therefore misses the centralizer quotient.
   Evidence: `/tmp/audit810/hi27-82.png` (PDF page 27, journal p.37).

2. **(8.6)(b1) centralizer is taken in the wrong subgroup.** PDF p.41 requires
   `C_{O_2(E_a)}(T)=1`; current file has
   `Q ⊓ centralizer (T : Set H) = ⊥`. This should use
   `twoCoreIn (EAt ... a) ⊓ centralizer T = ⊥` (or an equivalent ambient encoding).

3. **(8.6)(b3) omits normality of W in L.** PDF p.41 says “an elementary abelian
   normal subgroup W of order 2^4 in L”. Current existential only has `W ≤ L`,
   elementary abelian, and cardinality; add relative normality
   `(W.subgroupOf L).Normal` (or equivalent).

4. **(8.6)(c3) first clause is not a quotient/Q-invariance statement.** PDF p.41
   quantifies every **Q-invariant subgroup of order 3 in**
   `E_{a+1}/O_2(E_{a+1})`, acting fixed-point-freely on
   `Q_{a+1}/Z_{a+1}`. Current quantifies an ambient subgroup `R ≤ E_{a+1}` of
   order 3, normal in E, with no quotient by O₂ and no Q-invariance. A
   quotient-aware helper is needed.

5. **(8.6)(c3) involution clause is too strong / wrong quotient encoding.** PDF says
   every involution in `Q Q_{a+1}/Q_{a+1}` centralizes a subgroup of order 2^5 in
   `Q_{a+1}`. Current quantifies `x ∈ Q ⊔ Q_{a+1}`, `x ∉ Q_{a+1}`, and
   requires the ambient representative itself to satisfy `x^2=1`; a quotient
   involution only requires the coset square to lie in `Q_{a+1}`. Use a quotient
   representative/coset predicate.

6. **(9.4)(ii) misses conjugation of r.** PDF p.50 requires
   `⟨G_{a+1} ∩ G_ν,t⟩ = G_{a+1}` for every
   `ν ∈ Δ(a+1) ∩ Δ(r^x)`. Current `h2` quantifies `n ∈ Δ(a+1)` and
   `n ∈ Δ(r)` (not `Δ(r^x)`). Use the graph action vertex `Γ.act x r` (with the
   paper's conjugation convention).

7. **(9.5) t lies in the wrong subgroup.** PDF p.52 says
   `t ∈ V_{a+1} \ Q_{a'}`; current `ht` says
   `t ∈ VAt ... a' ∧ t ∉ QAt ... a'`. Change first membership to
   `VAt ... firstStep`.

8. **(9.5)(b) product type is semidirect, not direct.** The high-resolution PDF
   glyph in p.52 is the same backslash/semidirect symbol as in (9.1)(a), while
   direct products elsewhere use an explicit `×`. Source says
   `G_{a'}/Q_{a'} ≅ SL_2(2) \ C_2`; current uses
   `QuotientIsModel ... (SL2Two × C2)`. Use `QuotientIsSemidirectModel`.
   Evidence: `/tmp/audit810/hi42-95b.png`.

## Structural under-specification to address

The paper's `a+3`, `a'-2`, and `a+2` denote the selected vertices along the
critical-path/graph notation, not arbitrary vertices. Current statements
quantify unrestricted `aPlus3` in (9.6)/(9.7), unrestricted `aMinus2` in (9.5),
and unrestricted `aPlus2` in (10.1), without tying them to the corresponding
path/action vertex. This permits statements that do not match the source's
fixed vertex notation. Use `CriticalPath.path` indices (where defined), or add
the exact graph/path relation.

## Mostly aligned after direct read

* (8.1)(a) denominator now matches `|Z_a/(Z_a∩Q_{a'})| =
  |Z_{a'}/(Z_{a'}∩Q_a)|`; (8.1)(c) source `×` is direct product.
* (8.3), (8.4), (8.5) use the positive hypothesis `Z_{a+1} ≤ Z(G_{a+1})`.
* (8.6) L orientation is `⟨Q_{a-1}^{G_a}⟩`, matching current orientation.
* (9.1)(a) is semidirect `SL₂(2) \ C₂`, current semidirect helper is right;
  (9.1)(b,c) otherwise matches.
* (9.2), (9.3), (9.8), (9.9), (9.10) conclusions/visible hypotheses match,
  modulo the general quotient-helper containment weakness.
* (10.1) alternatives (a)/(b), including b1/b2 cardinal/derived clauses,
  visually match p.59--60; its `a+2` parameter still needs path binding.

## Recommendation for parent patch

For (8.1), keep the existing `QuotientWitness` over
`GAt a ⊓ centralizer (ZAt a : Set H)`; this is the right ambient encoding of
the printed `\bar G_a=G_a/C_{G_a}(Z_a)`. Map `Z_a`, `E_a`, `R`, and `S` through
the witness projection, and express each printed `×` with the existing
`IsInternalDirectProductFamily`. The first denominator in (8.1)(a) must be
`Z_a ⊓ Q_{a'}` (already fixed), not `Z_{a'} ⊓ Q_{a'}`.

For (10.1), if introducing path aliases is too invasive, bind the offset
parameters with explicit equalities to `ctx.criticalPath.path` at indices 2/3
(under the needed length inequalities) rather than leaving `aPlus2` arbitrary.
The ambient `W`/`Wnext` definitions otherwise match the source; the printed
bars in the setup denote quotient notation, while the theorem's W subgroups
are ambient subgroups, so current `conjugateClosure`/intersection shape is
appropriate.
