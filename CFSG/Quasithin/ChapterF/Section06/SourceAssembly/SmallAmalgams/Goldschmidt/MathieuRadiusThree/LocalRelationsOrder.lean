module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalRelationsFrame
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalRelationsLabels
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The radius-two label eight-group

The track commutator folds the left endpoint into the third branch at the
center. Its label is the product of the other two selected branch labels
and the central label. Thus the radius-two group has three involutory
commuting generators. The seven distinct nonidentity labels give equality
in the resulting order bound.

Source: Goldschmidt (1980), (6.12.3)--(6.12.4), printed p.404.
-/

@[expose] public section
noncomputable section
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup SimpleGraph Theory.GroupAction.CubicTree
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

/-- Canonical label balls conjugate under the literal vertex action. -/
theorem CanonicalLabelSetup.labelBall_map_conj (d : CanonicalLabelSetup F s)
    (a : RankTwo.Vertex F) (r : ℕ) (g : G) :
    (d.labelBall a r).map (MulAut.conj g).toMonoidHom = d.labelBall (g • a) r := by
  unfold labelBall
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨w, ⟨hw, hd⟩, rfl⟩, rfl⟩
    exact ⟨g • w, ⟨hw, (RankTwo.dist_smul F g a w).symm ▸ hd⟩,
      d.conjugate g w hw⟩
  · rintro ⟨w, ⟨hw, hd⟩, rfl⟩
    refine ⟨d.label (g⁻¹ • w), ⟨g⁻¹ • w, ⟨hw, ?_⟩, rfl⟩, ?_⟩
    · have hh := RankTwo.dist_smul F g a (g⁻¹ • w)
      rw [smul_inv_smul] at hh
      exact hh ▸ hd
    · change g * d.label (g⁻¹ • w) * g⁻¹ = d.label w
      simpa only [smul_inv_smul] using (d.conjugate g (g⁻¹ • w) hw).symm

/-- The exact three generators in Goldschmidt (6.12.4). -/
theorem CanonicalLabelSetup.radiusThree_radiusTwo_track_generators
    (d : CanonicalLabelSetup F s) (h : CubicTreeAction F) (hr : d.radius = 3)
    (htrack : ⁅d.label (d.track.vertex (d.center-2)),
      d.label (d.track.vertex (d.center+4))⁆ =
        d.label (d.track.vertex d.center) * d.label (d.track.vertex (d.center+2))) :
    d.labelBall (d.track.vertex d.center) 2 = Subgroup.closure
      (Set.range ![d.label (d.track.vertex (d.center-2)),
        d.label (d.track.vertex d.center), d.label (d.track.vertex (d.center+2))]) := by
  classical
  obtain ⟨f, hfc⟩ := d.exists_radiusThree_foldedBranchFrame h hr
  let A := Subgroup.closure (Set.range ![d.label (d.track.vertex (d.center-2)),
    d.label (d.track.vertex d.center), d.label (d.track.vertex (d.center+2))])
  have hm0 : d.label (d.track.vertex (d.center-2)) ∈ A := subset_closure ⟨0, rfl⟩
  have hm1 : d.label (d.track.vertex d.center) ∈ A := subset_closure ⟨1, rfl⟩
  have hm2 : d.label (d.track.vertex (d.center+2)) ∈ A := subset_closure ⟨2, rfl⟩
  have ht : (d.track.vertex (d.center-2)).type = d.side := by
    simpa only [show (2:ℤ)*(-1) = -2 by norm_num, sub_eq_add_neg] using d.shifted_type (-1)
  have hfold : d.label (d.label (d.track.vertex (d.center+4)) •
      d.track.vertex (d.center-2)) = d.label (d.track.vertex (d.center-2)) *
        (d.label (d.track.vertex d.center) * d.label (d.track.vertex (d.center+2))) := by
    rw [← htrack, d.conjugate _ _ ht, commutatorElement_def, d.label_inv ht]
    simp only [← mul_assoc, d.label_mul_self ht, one_mul]
  apply le_antisymm
  · rw [f.radiusTwo_generators d h d.center_type]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    induction i using Fin.cases with
    | zero => exact hm1
    | succ i =>
      rw [hfc]
      fin_cases i
      · exact hm0
      · exact hm2
      · change d.label (d.label (d.track.vertex (d.center+4)) •
          d.track.vertex (d.center-2)) ∈ A
        rw [hfold]
        exact A.mul_mem hm0 (A.mul_mem hm1 hm2)
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · have hc := d.label_mem_labelBall ((f.c_type h 0).trans d.center_type)
        (le_of_eq (f.c_dist h 0))
      simpa [hfc] using hc
    · exact d.label_mem_labelBall d.center_type (by simp)
    · have hc := d.label_mem_labelBall ((f.c_type h 1).trans d.center_type)
        (le_of_eq (f.c_dist h 1))
      simpa [hfc] using hc

/-- Every actual radius-two label group has order eight. -/
theorem CanonicalLabelSetup.radiusTwo_card_eq_eight_of_track_commutator
    (d : CanonicalLabelSetup F s) (h : LargeTreeSource F s) (hr : d.radius = 3)
    (htrack : ⁅d.label (d.track.vertex (d.center-2)),
      d.label (d.track.vertex (d.center+4))⁆ =
        d.label (d.track.vertex d.center) * d.label (d.track.vertex (d.center+2)))
    (a : RankTwo.Vertex F) (ha : a.type = d.side) :
    Nat.card (d.labelBall a 2) = 8 := by
  have hsmall : Nat.card (d.labelBall (d.track.vertex d.center) 2) ≤ 8 := by
    let : IsElementaryAbelian 2 (d.labelBall (d.track.vertex d.center) 2) :=
      d.labelBall_elementary h.action.toCubicTreeAction _ 2 (by omega)
        (by have := h.five_le; omega)
    let : Finite (RankTwo.stabilizer F (d.track.vertex d.center)) := h.action.finite_stabilizer _
    let : Finite (d.labelBall (d.track.vertex d.center) 2) := Finite.of_injective
      (Subgroup.inclusion (d.labelBall_le_stabilizer _ 2 (by omega)
        (by have := h.five_le; omega))) (Subgroup.inclusion_injective _)
    let u : Fin 3 → G := ![d.label (d.track.vertex (d.center-2)),
      d.label (d.track.vertex d.center), d.label (d.track.vertex (d.center+2))]
    have hgen : d.labelBall (d.track.vertex d.center) 2 = Subgroup.closure (Set.range u) :=
      d.radiusThree_radiusTwo_track_generators h.action.toCubicTreeAction hr htrack
    have hrank : Group.rank (d.labelBall (d.track.vertex d.center) 2) ≤ 3 := by
      calc
        _ = Group.rank (Subgroup.closure (Set.range u)) := Subgroup.rank_congr hgen
        _ ≤ Nat.card (Set.range u) := Subgroup.rank_closure_finite_le_nat_card _
        _ ≤ Nat.card (Fin 3) := Finite.card_range_le u
        _ = 3 := Nat.card_fin 3
    have hcard := card_dvd_exponent_pow_rank' (d.labelBall (d.track.vertex d.center) 2)
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (d.labelBall (d.track.vertex d.center) 2)))
    exact (Nat.le_of_dvd (by positivity) hcard).trans
      (pow_le_pow_right' (by decide) hrank)
  obtain ⟨g, hg⟩ := (RankTwo.same_orbit_iff F (d.track.vertex d.center) a).mpr
    (d.center_type.trans ha.symm)
  have hmap := d.labelBall_map_conj (d.track.vertex d.center) 2 g
  rw [hg] at hmap
  have hcard : Nat.card (d.labelBall a 2) =
      Nat.card (d.labelBall (d.track.vertex d.center) 2) := by
    rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact le_antisymm (hcard.symm ▸ hsmall) (d.radiusTwo_card_ge h a ha)

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
