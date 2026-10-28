module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.Generation
public import Theory.GroupTheory.Amalgam.RankTwoCompletion

/-!
# The odd-degree prepared linear row

For odd n the faithful natural-module quotient action has no nontrivial
two-power field coefficient. Its two-elements have determinant one, so the
original ambient Sylow T lies in the affine factor L and S=T. This
discharges every extra premise of the centralizer and ambient-generation
results in Generation, using the original prepared hypotheses. The original
parabolic comparison now gives a faithful completion in the actual G,
with the original whole Borel as exact intersection, in either orientation.

The field degree is the original n>1; m=n is derived from the comparison.
These results prove generation and one involution class, not PSL₃ recognition.
The even-degree centralizer argument (including the S₅ exceptional marking),
compatible full-normalizer realization, Weyl relation and general-field
completion recognition remain obligations of the same ambient-row task.
Source: Aschbacher–Smith §5.3.7, p.660 and F.4.45–46, p.297;
natural semilinear normalizers in B.4.2(1), p.86 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G))
include d h hH hp hm hF he hmax

/-- The source common Sylow is the original ambient Sylow for odd n. -/
theorem Preparation.linear_sourceS_eq_sylow_of_odd (hnodd : Odd n) :
    sourceS L H = (T : Subgroup G) := by
  have ha : Nonempty (L ≃* Matrix.SL2.Affine F) := by
    rcases he with he | he <;> obtain ⟨e⟩ := he
    · obtain ⟨a⟩ := (BlockComparison.linear_parabolic_factor d h hH.1.1.2 hp F hm hF 0 true e.left).2.1
      exact ⟨a.trans (Matrix.PSL3.LinearThree.pointLocalEquivAffine F)⟩
    · obtain ⟨a⟩ := (BlockComparison.linear_parabolic_factor d h hH.1.1.2 hp F hm hF 0 false e.left).2.1
      exact ⟨a.trans (Matrix.PSL3.LinearThree.lineLocalEquivAffine F)⟩
  obtain ⟨a⟩ := ha
  have hc := d.linear_core_structure h hH hp F hm hF he
  have hC := (d.linear_root_centralizers h hH hp F hm hF he hmax).1
  have hST := sourceS_le_sylow h.sylow_normalizes hH.1.1.2
  let M := normalizer (L : Set G)
  let X := L.subgroupOf M
  let : X.Normal := normal_subgroupOf_of_le_normalizer (show M ≤ normalizer (L : Set G) from le_rfl)
  let e : X ≃* Matrix.SL2.Affine F := (subgroupOfEquivOfLe L.le_normalizer).trans a
  have hV : (X.pCoreIn 2).map M.subtype = L.pCoreIn 2 := by
    rw [map_pCoreIn_of_injective 2 X M.subtype M.subtype_injective]
    change (L.subgroupOf M |>.map M.subtype).pCoreIn 2 = _
    rw [map_subgroupOf_eq_of_le L.le_normalizer]
  have hCX : centralizer (X.pCoreIn 2 : Set M) = X.pCoreIn 2 := by
    apply le_antisymm
    · intro x hx
      have hh : (x : G) ∈ centralizer (L.pCoreIn 2 : Set G) := by
        rw [← hV]
        rintro _ ⟨y,hy,rfl⟩
        exact congrArg M.subtype (hx y hy)
      have hxV := hC.le hh
      rw [← hV] at hxV
      exact (mem_map_iff_mem M.subtype_injective).mp hxV
    · intro x hx y hy
      apply Subtype.ext
      exact hC.ge (hV ▸ mem_map_of_mem M.subtype hx) y (hV ▸ mem_map_of_mem M.subtype hy)
  have hq : 2 < Nat.card F := by
    rw [hF,hc.1]
    exact Nat.pow_lt_pow_right (by decide : 1<(2:ℕ)) h.exponent
  have hs := d.linear_sourceS_le_factors h hH.1.1.2 hp F hm hF he
  let P := T.subtype h.sylow_normalizes
  have hTL := Matrix.PSL3.LinearAmbientGeometry.sylow_le_affine_of_odd_field_degree X e hq hCX
    hnodd (hF.trans (congrArg (fun k => 2 ^ k) hc.1)) P
  have hTleL : (T : Subgroup G) ≤ L := fun x hx => hTL
    (show (⟨x,h.sylow_normalizes hx⟩ : M) ∈ (P : Subgroup M) from hx)
  calc
    sourceS L H = sourceS L H ⊓ L := (inf_eq_left.mpr (show sourceS L H ≤ L from hs 0)).symm
    _ = (T : Subgroup G) ⊓ L := d.left_intersection
    _ = (T : Subgroup G) := inf_eq_left.mpr hTleL

/-- The original §5.3.7 centralizer bound has no extra core premise for odd n. -/
theorem Preparation.linear_centralizer_le_inter_of_odd (hnodd : Odd n)
    (z : G) (hz : orderOf z = 2) (hzS : z ∈ centerIn (sourceS L H)) :
    centralizer ({z} : Set G) ≤
      normalizer (L : Set G) ⊓ normalizer (residual H : Set G) :=
  d.linear_centralizer_le_inter_of_sourceS_eq_sylow h hH hp F hm hF he hmax
    (d.linear_sourceS_eq_sylow_of_odd h hH hp F hm hF he hmax hnodd) z hz hzS

/-- The original normalizer and factor pairs generate G for odd n. -/
theorem Preparation.linear_ambient_generation_of_odd (hnodd : Odd n) :
    normalizer (L : Set G) ⊔ normalizer (residual H : Set G) = ⊤ ∧
      L ⊔ residual H = ⊤ :=
  d.linear_ambient_generation_of_sourceS_eq_sylow h hH hp F hm hF he hmax
    (d.linear_sourceS_eq_sylow_of_odd h hH hp F hm hF he hmax hnodd)

/-- The original ambient group has one involution class for odd n. -/
theorem Preparation.linear_involutions_isConj_of_odd (hnodd : Odd n)
    (x y : G) (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y := by
  obtain ⟨z,hz,hz2,_⟩ := d.linear_exists_sylow_central_involution h hH hp F hm hF he hmax
  have hz1 : z ≠ 1 := by intro hh; simp [hh] at hz2
  have hf := d.linear_involutions_fused_in_overgroup h hH hp F hm hF he hmax
    (d.linear_sourceS_eq_sylow_of_odd h hH hp F hm hF he hmax hnodd) ⊤ le_top z hz hz1
  obtain ⟨a,_,ha⟩ := hf x (mem_top x) hx
  obtain ⟨b,_,hb⟩ := hf y (mem_top y) hy
  exact (isConj_iff.mpr ⟨a,ha⟩).symm.trans (isConj_iff.mpr ⟨b,hb⟩)

/-- The actual G is a faithful marked completion, retaining the whole source overlap. -/
theorem Preparation.linear_ambient_completion_of_odd (hnodd : Odd n) :
    (∃ c : RankTwoAmalgam.FaithfulCompletion
        (ChapterF.GreenBook.LieModels.LinearThree.amalgam F) (G := G),
      c.left.range = ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ∧
      c.right.range = ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 ∧
      c.middle.range = ChapterF.Source.commonBorel ![L,residual H] (sourceS L H) ∧
      c.left.range ⊓ c.right.range = c.middle.range) ∨
    (∃ c : RankTwoAmalgam.FaithfulCompletion
        (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse (G := G),
      c.left.range = ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ∧
      c.right.range = ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 ∧
      c.middle.range = ChapterF.Source.commonBorel ![L,residual H] (sourceS L H) ∧
      c.left.range ⊓ c.right.range = c.middle.range) := by
  let P₀ := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
  let P₁ := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  have hgen : P₀ ⊔ P₁ = ⊤ := by
    rw [ChapterF.Source.parabolics_generate]
    change L ⊔ residual H ⊔ sourceS L H = ⊤
    rw [(d.linear_ambient_generation_of_odd h hH hp F hm hF he hmax hnodd).2,top_sup_eq]
  let c₀ : RankTwoAmalgam.FaithfulCompletion
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (G := G) :=
    RankTwoAmalgam.FaithfulCompletion.ofSubgroups P₀ (P₀ ⊓ P₁) P₁ inf_le_left inf_le_right hgen
  have hmid : c₀.middle.range = ChapterF.Source.commonBorel ![L,residual H] (sourceS L H) :=
    (range_subtype _).trans (ChapterF.Source.lemma_F_1_3_6 (d.hypothesisF11 h hH.1.1.2))
  have hover : c₀.left.range ⊓ c₀.right.range = c₀.middle.range := by
    change P₀.subtype.range ⊓ P₁.subtype.range = (P₀ ⊓ P₁ : Subgroup G).subtype.range
    rw [range_subtype,range_subtype,range_subtype]
  rcases he with he | he <;> obtain ⟨e⟩ := he
  · exact Or.inl ⟨c₀.comapIso e.symm,by simp only [RankTwoAmalgam.FaithfulCompletion.comapIso_left_range]; exact range_subtype _,
      by simp only [RankTwoAmalgam.FaithfulCompletion.comapIso_right_range]; exact range_subtype _,
      by simpa only [RankTwoAmalgam.FaithfulCompletion.comapIso_middle_range] using hmid,
      by simpa only [RankTwoAmalgam.FaithfulCompletion.comapIso_left_range,
        RankTwoAmalgam.FaithfulCompletion.comapIso_right_range,
        RankTwoAmalgam.FaithfulCompletion.comapIso_middle_range] using hover⟩
  · exact Or.inr ⟨c₀.comapIso e.symm,by simp only [RankTwoAmalgam.FaithfulCompletion.comapIso_left_range]; exact range_subtype _,
      by simp only [RankTwoAmalgam.FaithfulCompletion.comapIso_right_range]; exact range_subtype _,
      by simpa only [RankTwoAmalgam.FaithfulCompletion.comapIso_middle_range] using hmid,
      by simpa only [RankTwoAmalgam.FaithfulCompletion.comapIso_left_range,
        RankTwoAmalgam.FaithfulCompletion.comapIso_right_range,
        RankTwoAmalgam.FaithfulCompletion.comapIso_middle_range] using hover⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
