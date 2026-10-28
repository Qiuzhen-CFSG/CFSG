module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2Transfer
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalG2ShortFixed

/-!
# All-degree involution transfer in the literal Chapter 12 setup

The chosen-module input applies generalized Thompson transfer to the
original quotient action. Every ambient involution is conjugate into the
original S in both G₂ and triality rows. The G₂ comparison consequently
marks the two entire ambient involution classes, without assuming S=T.
The actual source centralizers then give a q⁴ lower bound for every
ambient involution-centralizer Sylow two-subgroup.

This discharges the fusion and lower-bound premises of the even-degree
F.4.38 argument. Outer-involution centralizer geometry, exhaustive
comparison, original uniqueness and full GlobalExit retain their existing
assembly obligations. All subgroup maps and the cubic triality quotient
remain the literal source ones.

Source: Aschbacher–Smith F.4.38, p.294, 5.3.3, p.659, and the
Chapter 12 setup, p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Transfer into the original G₂ intersection core, with no parity premise. -/
theorem rankOne_global_g2_involution_fused_into_sourceS
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H)) (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse))
    (x : G) (hx : orderOf x=2) :
    ∃ y ∈ Global.sourceS L H, IsConj x y :=
  d.g2_involution_fused_into_sourceS (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH.1.1.2 hp F he x hx

/-- The same transfer conclusion for the actual triality arms quotient. -/
theorem rankOne_global_triality_involution_fused_into_sourceS
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H)) (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0<m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam
          (_root_.Triality.Standard.binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam
          (_root_.Triality.Standard.binaryParameters m hm)).reverse))
    (x : G) (hx : orderOf x=2) :
    ∃ y ∈ Global.sourceS L H, IsConj x y :=
  d.triality_involution_fused_into_sourceS (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH.1.1.2 hp m hm he x hx

/-- The two marked classes cover every ambient involution at every degree. -/
theorem rankOne_global_g2_ambient_involution_classes_of_transfer
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)) :
    ∃ e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse,
      ∃ z v : (L ⊔ residual H : Subgroup G),
        z.val = (e.right.symm (Global.G2CompletionFusion.long (1:F))).val ∧
        v.val = (e.right.symm (Global.G2CompletionFusion.short (1:F))).val ∧
        z.val ∈ (center (residual H)).map (residual H).subtype ∧
        orderOf z=2 ∧ orderOf v=2 ∧ ¬ IsConj z.val v.val ∧
        ∀ x : G, orderOf x=2 → IsConj z.val x ∨ IsConj v.val x :=
  d.g2_ambient_involution_classes_of_transfer (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F he

/-- The q⁴ lower bound for every ambient involution centralizer. -/
theorem rankOne_global_g2_involution_centralizer_sylow_lower_bound
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse))
    (x : G) (hx : orderOf x=2) (P : Sylow 2 (centralizer ({x} : Set G))) :
    Nat.card F^4 ≤ Nat.card P :=
  d.g2_involution_centralizer_sylow_lower_bound (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F he x hx P

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
