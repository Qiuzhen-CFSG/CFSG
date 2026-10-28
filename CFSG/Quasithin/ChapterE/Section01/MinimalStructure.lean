module

public import CFSG.Quasithin.ChapterE.Defs
public import CFSG.Quasithin.ChapterE.Section01.MinimalSupplement
public import CFSG.Quasithin.ChapterE.Section01.MinimalStructure.Frattini
public import CFSG.Quasithin.ChapterE.Section01.MinimalStructure.Residual
public import CFSG.Quasithin.ChapterE.Section01.MinimalStructure.Radical
public import CFSG.Quasithin.ChapterE.Section01.MinimalStructure.Kernel
public import CFSG.Quasithin.ChapterE.Section01.MinimalStructure.OddSeries
public import CFSG.Quasithin.ChapterE.Section01.MinimalStructure.ComponentSeries
public import CFSG.Quasithin.ChapterE.Section01.MinimalStructure.ChiefFactor

/-!
# Structure of minimal supplements

This module assembles E.1.10(2)--(5) for genuine minimal supplements.
The Frattini argument gives two-closedness of the preimage of the intrinsic
two-core of the actual quotient image. Kernel solvability and Hall's theorem
then lift the odd-prime core series in (3). Solvable-kernel transport of the
radical quotient and its layer, together with the radical and residual
arguments, gives all three conclusions of (4). The chief-factor theorem in
(5) supplies an actual positive direct-power isomorphism and an explicit
simple normal section of a subnormal subgroup of the ambient group.

The individual clauses are `IsMinimalSupplement.twoClosed_preimage_twoCore`,
`IsMinimalSupplement.oddSeries`, `IsMinimalSupplement.componentSeries`, and
`IsMinimalSupplement.exists_directPower_and_simpleSection_of_isChief`.
All normality and core constructions are intrinsic to the indicated groups;
the supplement itself need not be normal in the ambient group.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma E.1.10, printed p.211.
-/

public section
namespace CFSG.Quasithin.ChapterE
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- E.1.10(4), with all three hypotheses and conclusions. The hypothesis
`KbarX = O_{∞,E}(KbarX)` is expressed by its intrinsic radical--C-component
layer being the whole group. The first conclusion `K = O_{∞,E,2}(K)` says
that the quotient of the radical quotient by its ordinary layer is a two-group.
The two-residual `O²` is distinct from the two-core `O₂`. -/
theorem IsMinimalSupplement.componentSeries (T : Sylow 2 G)
    {X Y K : Subgroup G} [X.Normal] [Y.Normal]
    (h : IsMinimalSupplement (T : Subgroup G) X Y K)
    (hE : oInfELayer ((K ⊓ X).map (QuotientGroup.mk' Y)) = ⊤)
    (hr : IsTwoClosed (solvableRadical (K.map (QuotientGroup.mk' Y))))
    (hres : pResidual 2 (K.map (QuotientGroup.mk' Y)) =
      solvableResidual (K.map (QuotientGroup.mk' Y))) :
    HasTwoGroupQuotient (componentLayer (K ⧸ solvableRadical K)) ∧
      IsTwoClosed (solvableRadical K) ∧
      pResidual 2 K = solvableResidual K :=
  ⟨h.hasTwoGroupQuotient_componentLayer T (oInfELayer_eq_top_iff.mp hE),
    h.twoClosed_solvableRadical T hr, h.pResidual_eq_solvableResidual T hres⟩

end CFSG.Quasithin.ChapterE
