module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2LocalSylow
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalG2OuterGeometry
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalG2ShortFixed

/-!
# The all-degree G₂ Sylow equality in the literal Chapter 12 setup

The original torus involution has C_T(t) Sylow in the right-normalizer
centralizer. This excludes the previously constructed strict enlargement,
hence S=T for all n>1, including even degrees and field four. Applying this
equality to the existing fixed-coset argument gives the full short-root
centralizer bound, through the same compatible parabolic maps.

The original uniqueness and concrete comparison remain explicit preparation
inputs. Their construction and the concrete completion recognition remain
with the generic-global assembly; this does not assert GlobalExit.

Source: Aschbacher–Smith F.4.37–38, pp.293–294, F.4.42, p.295,
and 5.3.3, p.659 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open Atlas.G2 Atlas.G2.LieParabolicSetup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Local Sylow placement retains the exact original torus and involution. -/
theorem rankOne_global_g2_outer_centralizer_local_sylow
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B Y : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)
    (hD : Y ≤ ChapterF.Source.commonBorel ![L,residual H] (Global.sourceS L H))
    (hmark : ∀ b : (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1 : Subgroup G),
        b.val ∈ Y ↔ (e.middle b).val ∈ splitTorus)
    (t : T) (ht2 : orderOf t=2)
    (htD : t.val ∈ normalizer (Y : Set G)) :
    let C := normalizer (residual H : Set G) ⊓ centralizer ({t.val} : Set G)
    ∃ P : Sylow 2 C, (P : Subgroup C).map C.subtype =
      (T : Subgroup G) ⊓ centralizer ({t.val} : Set G) :=
  d.g2_outer_centralizer_local_sylow
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F e hD hmark t ht2 htD

/-- The original intersection core is the ambient Sylow subgroup at every n>1. -/
theorem rankOne_global_g2_sourceS_eq_sylow
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
    Global.sourceS L H = (T : Subgroup G) :=
  d.g2_sourceS_eq_sylow (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F he

/-- S=T discharges the fixed-coset and full short-root centralizer premises
also at even original degrees, including field four. -/
theorem rankOne_global_g2_short_centralizer_all_degrees
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
      let l := (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 0).subtype.comp
        e.left.symm.toMonoidHom
      (∃! q : centralizer ({l Global.G2ShortAction.short} : Set G) ⧸
          (normalizer (L : Set G)).subgroupOf (centralizer ({l Global.G2ShortAction.short} : Set G)),
          Global.G2ShortAction.longMark l • q=q) ∧
        centralizer ({l Global.G2ShortAction.short} : Set G) ≤ normalizer (L : Set G) := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨e,_,hfixed⟩ := d.g2_short_fixed_coset_geometry hi hH hp F he
  exact ⟨e,hfixed (d.g2_sourceS_eq_sylow hi hH hp F he)⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
