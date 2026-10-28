module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.FixedRoot
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalSymplecticExtensionOrder.FixedDerived

/-!
# The Chapter 12 field-four root-to-outer fusion step

The native unique fixed root is transported through the same original pure
endpoint, in either orientation. Ambient normalizer growth then forces a
root involution to fuse into T minus S if the inner Sylow is proper.

These applications use W=wholeReduced T L and retain Hypothesis 12.2.1,
many locals, the original n>1 and PSL2 quotient, HStar, Preparation and the
perfect whole residual. The fixed binary A6/D8 exclusion and the final
same-extension order comparison are still necessary.

Source: Aschbacher--Smith F.4.37, printed p.293, applied in 5.3.3 and
Chapter 12, pp.659,795 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- A field-four outer involution fixes a unique nonidentity element of
one original root center, using the actual endpoint action. -/
theorem rankOne_global_symplectic_outer_fixed_root_unique
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
    (hq : Nat.card F=4) (f : T) (hf : orderOf f=2) (ho : f.val ∉ Global.sourceS L H) :
    ∃ i : Fin 2, ∃ z : G, z≠1 ∧
      z ∈ (center (![L,residual H] i)).map (![L,residual H] i).subtype ∧
      z ∈ centralizer ({f.val} : Set G) ∧
      ∀ x ∈ (center (![L,residual H] i)).map (![L,residual H] i).subtype,
        x ∈ centralizer ({f.val} : Set G) → x=1 ∨ x=z :=
  d.symplectic_outer_fixed_root_unique
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he hq f hf ho

/-- Properness of the original inner Sylow forces genuine ambient fusion
from an original root involution to an outer involution of T. -/
theorem rankOne_global_symplectic_proper_inner_sylow_outer_root_fusion
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
    (hst : Global.sourceS L H≠(T : Subgroup G)) :
    ∃ i : Fin 2, ∃ z : G, orderOf z=2 ∧
      z ∈ (center (![L,residual H] i)).map (![L,residual H] i).subtype ∧
      ∃ t : T, orderOf t=2 ∧ t.val ∉ Global.sourceS L H ∧ IsConj z t.val :=
  d.symplectic_proper_inner_sylow_outer_root_fusion
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he hst

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
