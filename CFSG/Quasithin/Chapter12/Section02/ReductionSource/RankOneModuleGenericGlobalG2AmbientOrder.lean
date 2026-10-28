module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2AmbientOrder
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalG2CompletionFusion

/-!
# Ambient G₂ involution and order comparison in the Chapter 12 setup

The compatible source pair supplies two marked involution classes in the
original S. Once S is the ambient Sylow subgroup T, Sylow conjugacy makes
this a complete ambient catalogue. Thompson's order formula then identifies
the full-normalizer join with G if the designated short-root centralizer
lies in the left normalizer; simplicity gives L ∨ O²(H) = G as well.

At odd original degrees the existing field-index calculation discharges
S = T. The short-root centralizer bound in F.4.42 remains explicit, as do
the exhaustive compatible comparison and original uniqueness in Preparation.
The actual factor join is not yet identified with a concrete G₂ model, so
these are ambient-recognition reductions and do not prove GlobalExit.

Source: Aschbacher–Smith F.4.38, F.4.40–44, pp.294–296, and 5.3.3–4,
pp.659–660 (`refs/quasithin.pdf`); the Chapter 12 application is on p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Odd original degree gives a complete, irredundant two-class catalogue
of the ambient involutions, without a completion-isomorphism premise. -/
theorem rankOne_global_g2_two_involution_classes_of_odd
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n) (hnodd : Odd n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (G2.amalgam (F := F)).reverse)) :
    ∃ z v : G, z ∈ L ⊔ residual H ∧ v ∈ L ⊔ residual H ∧
      orderOf z=2 ∧ orderOf v=2 ∧ ¬ IsConj z v ∧
      ∀ x : G, orderOf x=2 → IsConj z x ∨ IsConj v x := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  have hST := (d.g2_short_root_not_fused_of_odd hi hH hp hnodd F he).1
  obtain ⟨_,z,v,_,_,_,hz,hv,hnc,hclasses,_⟩ :=
    d.g2_ambient_involution_classes hi hH hp F he hST
  exact ⟨z.val,v.val,z.property,v.property,(Subgroup.orderOf_coe z).trans hz,
    (Subgroup.orderOf_coe v).trans hv,hnc,hclasses⟩

/-- The literal Chapter 12 normalizer join and factor join both equal G
once S=T and the marked short-root centralizer bound is established. -/
theorem rankOne_global_g2_ambient_recognition_reduction
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
        (G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (G2.amalgam (F := F)).reverse))
    (hST : Global.sourceS L H = (T : Subgroup G)) :
    ∃ e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (G2.amalgam (F := F)).reverse,
      let v : G := (e.right.symm (Global.G2CompletionFusion.short (1:F))).val
      orderOf v=2 ∧
      (centralizer ({v} : Set G) ≤ normalizer (L : Set G) →
        normalizer (L : Set G) ⊔ normalizer (residual H : Set G) = ⊤ ∧
        L ⊔ residual H = ⊤) :=
  d.g2_ambient_recognition_reduction
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F he hST

/-- At odd original degrees only the designated short-root centralizer
bound remains for this ambient-equality step; S=T is discharged. -/
theorem rankOne_global_g2_ambient_recognition_reduction_of_odd
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n) (hnodd : Odd n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (G2.amalgam (F := F)).reverse)) :
    ∃ e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (G2.amalgam (F := F)).reverse,
      let v : G := (e.right.symm (Global.G2CompletionFusion.short (1:F))).val
      orderOf v=2 ∧
      (centralizer ({v} : Set G) ≤ normalizer (L : Set G) →
        normalizer (L : Set G) ⊔ normalizer (residual H : Set G) = ⊤ ∧
        L ⊔ residual H = ⊤) :=
  d.g2_ambient_recognition_reduction_of_odd
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp hnodd F he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
