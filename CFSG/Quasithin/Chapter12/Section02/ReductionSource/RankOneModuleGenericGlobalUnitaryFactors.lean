module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFactors
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryReduction

/-!
# The original unitary residual factors in Chapter12

The faithful left factor occupies the plane endpoint of the actual unitary
amalgam. Its PSL₂ quotient fixes n = 2m, with m > 1; the right residual is
the point factor with PSL₂(2^m) quotient. The same conclusions hold for
the degree-two extension, by the already constructed compatible reduction
to the ordinary amalgam. The original S and the reduced T ∩ L remain distinct.

The original cores have orders q⁴ and q⁵, with the latter special and its
center of order q centralized by the right residual. These are the local
inputs used by the unitary normality argument in 5.2.8. Right maximality,
exhaustive comparison, original uniqueness and ambient completion remain
explicit obligations; these results do not identify the ambient group.
Source: Aschbacher–Smith 5.2.6–8, pp.650–653, and the Chapter12 application
on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The literal reduced parabolics retain the original perfect residuals. -/
theorem rankOne_global_reduced_parabolic_residuals
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (hc : Global.ConcreteAmalgamComparison (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))) :
    ∀ i : Fin 2,
      (solvableResidual (ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) i)).map
        (ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) i).subtype = ![L,residual H] i :=
  d.reduced_parabolic_residuals (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp hc

/-- Both ordinary orientations give the original plane and point factors. -/
theorem rankOne_global_unitary_local_structure
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (amalgam m hm).reverse)) :
    1 < m ∧ n = 2*m ∧ Nonempty (L ≃* L2 m hm) ∧
      Nonempty (residual H ≃* PointLocal.ProjectiveLocal m hm) ∧
      ClassicalGroup.IsPSL (residual H ⧸ pCore 2 (residual H)) 2 (2^m) :=
  d.unitary_local_structure (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp m hm he

/-- The extended comparison identifies the same original factors after reduction. -/
theorem rankOne_global_unitaryExtension_local_structure
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (Extension.amalgam m hm).reverse)) :
    1 < m ∧ n = 2*m ∧ Nonempty (L ≃* L2 m hm) ∧
      Nonempty (residual H ≃* PointLocal.ProjectiveLocal m hm) ∧
      ClassicalGroup.IsPSL (residual H ⧸ pCore 2 (residual H)) 2 (2^m) :=
  d.unitaryExtension_local_structure (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp m hm he

/-- The actual original cores satisfy the source elementary and special clauses. -/
theorem rankOne_global_unitary_core_structure
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (he : (Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (amalgam m hm).reverse)) ∨
      (Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (Extension.amalgam m hm).reverse))) :
    1 < m ∧ n = 2*m ∧
      IsElementaryAbelian 2 (pCore 2 L) ∧ Nat.card (pCore 2 L) = (2^m)^4 ∧
      Nat.card (pCore 2 (residual H)) = (2^m)^5 ∧ Nat.card (center (pCore 2 (residual H))) = 2^m ∧
      center (pCore 2 (residual H)) = commutator (pCore 2 (residual H)) ∧
      center (pCore 2 (residual H)) = frattini (pCore 2 (residual H)) ∧
      IsElementaryAbelian 2 (center (pCore 2 (residual H))) ∧
      (center (pCore 2 (residual H))).map (pCore 2 (residual H)).subtype ≤ center (residual H) :=
  d.unitary_core_structure (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp m hm he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
