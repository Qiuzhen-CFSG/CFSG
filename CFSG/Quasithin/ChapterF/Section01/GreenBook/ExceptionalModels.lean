module

public import Theory.GroupTheory.Amalgam.LocalStructure
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.HallJanko.Transport
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.HallJanko.Assembly
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.Catalogue

/-!
# The six exceptional models and their automorphism extensions in F.1.12

This assembly exports the constructed G₂(2)′, Tits, J₂, Aut(J₂), M₁₂ and
Aut(M₁₂) amalgams, and the G₂(2) and full binary Ree extensions used in the
proof. `ExceptionalModels.local_assertions` verifies all eight concrete rows
without additional local premises. `ExceptionalModels.automorphism_extensions`
identifies all four extensions with the full automorphism groups; the individual
modules also export the compatible transports of their marked amalgams.

`ExceptionalModels.ParabolicModel` gives the raw local-equivalence predicates
for these fixed models. `ExceptionalModels.IsModel` retains both commuting
squares in every case except J₂ and Aut(J₂). Exhaustive recognition and the
exceptional uniqueness upgrades belong to the separate source-theorem owners.

The amalgam in the source is `(L₁B, B, L₂B)`. The whole source Borel `B₁B₂S`
is proved equal to the concrete overlap. In the Hall--Janko models its order
is respectively 384 and 768, whereas the Sylow orders are 128 and 256.
In the other models the Borel is the common Sylow subgroup.
The source local factors, their Sylow enlargements and the full parabolics
remain distinct: the outer J₂ first quotient has numerator `L₁S`, and its
quaternion--dihedral core is intrinsic to `L₁`. All quotients use cores
intrinsic to their numerator groups.

The intended equivalence relations are already supplied by
`Theory.GroupTheory.RankTwoAmalgam.Iso` and `ParabolicEquiv`. In cases (10)
and (11), involving `J₂` and `Aut(J₂)`, only the latter is asserted. Its three
isomorphisms need not commute with the overlap embeddings. The other four
exceptional cases require `Iso`; uniqueness of an amalgam with the specified
local structure is a separate recognition problem.

## Source corrections proved by the concrete calculations

* Notation E.2.16 (printed p. 228) defines `Q₈²` as the central product of
  two quaternion groups, with their centers identified. It has order 32;
  it is not the direct product of order 64.
* F.1.12(I)(12) prints `L₁/O₂(L₂)` and assigns both core descriptions to
  `O₂(L₂)`. The proved first quotient is `L₁/O₂(L₁) ≅ PSL₂(2)` and its
  core is `Q₈ * Q₈`. The second quotient is also PSL₂(2), with core order
  32. `MathieuTwelve.local_calculations` supplies these corrected assertions.
  The second core is proved neither quaternion-central-product nor normal
  in the first parabolic, so the printed denominator is not a valid substitute.
* For Aut(M₁₂), both cores have order 64 and both quotients are PSL₂(2).
  The first core satisfies `[Q_H,O²(H)] ≅ Q₈ * Q₈` and
  `Q_H/Z ≅ E₄ wr C₂`, with the original `Z = Ω₁(Z(S))` of order two.
  `AutMathieuTwelve.marked_Z` fixes the literal denominator; equality with
  the core's full center is a separate proved fact. The center has order two,
  excluding the printed `C₄ * Q₈²`; the core is also proved different from
  the split quaternion-swap model. The compatible actual quotient and action
  are exported from `M12ExceptionalExtension.VerifiedPair`.
* The first Tits core has order 512 and quotient the actual Sz(2), a
  Frobenius group of order 20, as in Parrott (1972), p.672. The second core
  has order 1024 and quotient PSL₂(2). `no_printed_first_package` rules out
  the printed 1024/D₁₀ pair for every possible `L₁` inside the first full
  parabolic. Thus distinguishing `L₁` from `L₁S` cannot repair that pair.
  The chosen local factors are the proved prime-to-two residuals of the
  full parabolics. The full binary Ree cores have orders 1024 and 2048,
  with the same two actual quotient groups and compatible inclusion-induced
  quotient maps. The Tits and full-Ree alternatives are unchanged.

The binary G₂ full model has the special first core of order 32 and center
order two, and second core order 32. Its actual derived model has cores
`C₄ * Q₈` and `C₄ × C₄`; both quotients in both models are PSL₂(2).

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, F.1.12(I)(8)--(13), printed p. 263 (PDF p. 274),
Notation E.2.16, and the proof of 14.2.21, printed pp.988--989 (PDF
pp.1005--1006); Parrott, *A Characterization of the Tits' Simple Group*
(1972), p.672. The model files retain their concrete-carrier provenance.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.GreenBook

/-!
The legacy Hall--Janko aliases below retain their public interfaces. Their
marking assumes `S ≤ Lᵢ` and their recognition predicates do not constrain
the ambient carrier, so they do not encode the outer source alternative.
Use `HallJanko.J2Model`, `HallJanko.AutJ2Model`, and the carrier-indexed
predicates exported from `ExceptionalModels.HallJanko`. The concrete witnesses
`HallJanko.j2Model` and `HallJanko.autJ2Model` in `HallJanko.Assembly` now
discharge all their local calculations and the full-automorphism identification. -/

abbrev J2MarkedModel := Sporadic.LeechRelated.J2.J2LocalModel
abbrev AutJ2MarkedModel := Sporadic.LeechRelated.J2.AutJ2LocalModel

end CFSG.Quasithin.ChapterF.GreenBook
