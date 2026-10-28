module

public import CFSG.Quasithin.ChapterC.Section01.BlockBasics
public import Theory.ElementaryAbelian.Quotient
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.GroupAction.CentralElementaryFrattini
public import Theory.Representation.FirstCohomologyBounds

/-!
# Frattini control and the cohomology bound for a block

This module isolates the two reusable steps in C.1.13(a,b).  Central elementary
commutator displacements give Frattini control.  After passing to the fixed-free
quotient, the usual connecting cocycle embeds the literal quotient
`Q / (U \sup D)` in first cohomology.  The fixed-point hypothesis is discharged
from two-perfection when fixed vectors give distinguishable displacement maps
to an elementary two-group.

Reference: Aschbacher--Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), C.1.13, printed pp.124--125.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterC

open Representation Representation.OneCohomology
open scoped IsMulCommutative

/-- The Frattini conclusion in C.1.13(a), separated from the ambient block
identifications. -/
theorem frattini_le_block_fixed_of_central_elementary_displacement
    {L Q : Type*} [Group L] [Group Q] [Finite Q] [MulDistribMulAction L Q]
    (U : Subgroup Q) (hQ : IsPGroup 2 Q) (hcentral : U ≤ Subgroup.center Q)
    (hexp : ∀ u ∈ U, u ^ 2 = 1)
    (hdisplacement : ∀ (l : L) (q : Q), (l • q) / q ∈ U) :
    frattini Q ≤ FixedPoints.subgroup L Q :=
  frattini_le_fixed_of_central_elementary_displacement U hQ hcentral hexp hdisplacement

/-- The connecting cocycle on the literal quotient `Q / (U \sup D)`.  The
linear equivalence records the quotient action constructed from the group
structure; no cohomological injection is assumed. -/
def blockQuotientToH1
    {L Q W : Type*} [Group L] [Finite L] [Group Q]
    (U D : Subgroup Q) [(U ⊔ D).Normal]
    [IsElementaryAbelian 2 (Q ⧸ (U ⊔ D))]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) (L ⧸ pCore 2 L) W)
    (V : Subrepresentation ρ) (htrivial : HasTrivialQuotient V)
    (e : Additive (Q ⧸ (U ⊔ D)) ≃ₗ[ZMod 2] (W ⧸ V.toSubmodule)) :
    Additive (Q ⧸ (U ⊔ D)) →ₗ[ZMod 2] H1 V.toRepresentation :=
  linearEquivToH1 ρ V htrivial e

/-- Fixed-point-free quotient models make the connecting cocycle injective. -/
theorem blockQuotientToH1_injective
    {L Q W : Type*} [Group L] [Finite L] [Group Q]
    (U D : Subgroup Q) [(U ⊔ D).Normal]
    [IsElementaryAbelian 2 (Q ⧸ (U ⊔ D))]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) (L ⧸ pCore 2 L) W)
    (V : Subrepresentation ρ) (htrivial : HasTrivialQuotient V)
    (hfixed : fixed ρ = ⊥)
    (e : Additive (Q ⧸ (U ⊔ D)) ≃ₗ[ZMod 2] (W ⧸ V.toSubmodule)) :
    Function.Injective (blockQuotientToH1 U D ρ V htrivial e) :=
  linearEquivToH1_injective ρ V htrivial hfixed e

/-- Two-perfection removes the extra fixed subgroup in the C.1.13 quotient
argument.  Here `displacement` is the map sending a fixed quotient vector to
its commutator homomorphism into the elementary centralizer layer. -/
theorem block_fixed_eq_bot_of_twoPerfect_detection
    {L W P : Type*} [Group L] [Finite L] [Group P]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) (L ⧸ pCore 2 L) W)
    (hperfect : IsPPerfect 2 (L ⧸ pCore 2 L)) (hP : IsPGroup 2 P)
    (displacement : fixed ρ → (L ⧸ pCore 2 L) →* P)
    (hdisplacement : Function.Injective displacement) : fixed ρ = ⊥ :=
  fixed_eq_bot_of_pPerfect_detection ρ hperfect hP displacement hdisplacement

/-- The preceding fixed-point reduction with two-perfection supplied before
passing to the literal `L / O₂(L)` quotient. -/
theorem block_fixed_eq_bot_of_L_twoPerfect_detection
    {L W P : Type*} [Group L] [Finite L] [Group P]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) (L ⧸ pCore 2 L) W)
    (hperfect : IsPPerfect 2 L) (hP : IsPGroup 2 P)
    (displacement : fixed ρ → (L ⧸ pCore 2 L) →* P)
    (hdisplacement : Function.Injective displacement) : fixed ρ = ⊥ := by
  apply block_fixed_eq_bot_of_twoPerfect_detection ρ
    (hperfect.of_surjective (QuotientGroup.mk' (pCore 2 L))
      (QuotientGroup.mk'_surjective _)) hP displacement hdisplacement

/-- C.1.13(b) in quotient-model form: the two-rank of the actual quotient is
bounded by the dimension of first cohomology. -/
theorem block_quotient_rank_le_H1_of_twoPerfect_detection
    {L Q W P : Type*} [Group L] [Finite L] [Group Q] [Group P]
    (U D : Subgroup Q) [(U ⊔ D).Normal]
    [IsElementaryAbelian 2 (Q ⧸ (U ⊔ D))]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) (L ⧸ pCore 2 L) W)
    (V : Subrepresentation ρ) (htrivial : HasTrivialQuotient V)
    (hperfect : IsPPerfect 2 (L ⧸ pCore 2 L)) (hP : IsPGroup 2 P)
    (displacement : fixed ρ → (L ⧸ pCore 2 L) →* P)
    (hdisplacement : Function.Injective displacement)
    (e : Additive (Q ⧸ (U ⊔ D)) ≃ₗ[ZMod 2] (W ⧸ V.toSubmodule)) :
    Module.finrank (ZMod 2) (Additive (Q ⧸ (U ⊔ D))) ≤
      Module.finrank (ZMod 2) (H1 V.toRepresentation) := by
  exact finrank_le_H1_of_linearEquiv ρ V htrivial
    (block_fixed_eq_bot_of_twoPerfect_detection ρ hperfect hP displacement hdisplacement) e

end CFSG.Quasithin.ChapterC
