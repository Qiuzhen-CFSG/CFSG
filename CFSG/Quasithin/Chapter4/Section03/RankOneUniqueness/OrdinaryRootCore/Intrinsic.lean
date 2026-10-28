module

public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.RadicalAction.Lattice
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Coordinates


/-!
# The intrinsic long root in the original local group

The plane radical fixed by the standard Sylow is the join of roots zero and
four. The relative Sylow normalizer fixes root four, normalizes root zero,
and contains a determinant-one torus with a nontrivial square weight.
Its commutator with that fixed module is therefore exactly root zero.
This is the intrinsic description used to establish invariance under T.

Source: Aschbacher--Smith 4.3.6, printed p.614.
-/

public section

open Subgroup Matrix
open scoped commutatorElement
open Representation.OneCohomology.SymplecticFour
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootCoreMatrix
open Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
private theorem plane_radical_le_unipotent :
    (Plane.radical (F := F)).map planeLocal.subtype ≤ unipotent := by
  rintro _ ⟨g, hg, rfl⟩
  have hm := Plane.radical_matrix (⟨g, hg⟩ : Plane.radical)
  change g.val.val = _ at hm
  rw [mem_unipotent_iff, mem_borel_iff]
  change (g.val.val (.inl 1) (.inl 0) = 0 ∧
    (∀ i j, g.val.val (.inr i) (.inl j) = 0)) ∧
    (g.val.val (.inl 0) (.inl 0) = 1 ∧ g.val.val (.inl 1) (.inl 1) = 1)
  rw [hm]
  simp

omit [Finite F] [CharP F 2] in
private theorem root_zero_le_plane_radical :
    RootSubgroup.group (F := F) 0 ≤ (Plane.radical (F := F)).map planeLocal.subtype := by
  intro g hg
  obtain ⟨t, rfl⟩ := (RootSubgroup.mem_group_iff 0 g).mp hg
  have hl : rootElement (K := F) 0 t ∈ planeLocal :=
    (positive_root_mem_unipotent 0 t (by simp)).2
  refine ⟨⟨rootElement 0 t, hl⟩, ?_, rfl⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

omit [Finite F] [CharP F 2] in
private theorem root_four_le_plane_radical :
    RootSubgroup.group (F := F) 4 ≤ (Plane.radical (F := F)).map planeLocal.subtype := by
  intro g hg
  obtain ⟨t, rfl⟩ := (RootSubgroup.mem_group_iff 4 g).mp hg
  have hl : rootElement (K := F) 4 t ∈ planeLocal :=
    (positive_root_mem_unipotent 4 t (by simp)).2
  refine ⟨⟨rootElement 4 t, hl⟩, ?_, rfl⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem plane_radical_fixed_sylow :
    (Plane.radical (F := F)).map planeLocal.subtype ⊓
      centralizer (unipotent (F := F) : Set (Sp F)) =
      RootSubgroup.group 0 ⊔ RootSubgroup.group 4 := by
  apply le_antisymm
  · rintro g ⟨hg, hc⟩
    let x : unipotent (F := F) := ⟨g, plane_radical_le_unipotent hg⟩
    have hx : x ∈ center (unipotent (F := F)) :=
      mem_center_iff.mpr (fun t => Subtype.ext (hc t t.property))
    rw [← CentralRootGeometry.theta_range] at hx
    obtain ⟨⟨s,t⟩, he⟩ := hx
    have hv := congrArg (unipotent (F := F)).subtype he
    change (CentralRootGeometry.theta s.toAdd t.toAdd).val = g at hv
    rw [CentralRootGeometry.theta_val] at hv
    rw [←hv]
    exact mul_mem (mem_sup_left ((RootSubgroup.mem_group_iff 0 _).mpr ⟨_,rfl⟩))
      (mem_sup_right ((RootSubgroup.mem_group_iff 4 _).mpr ⟨_,rfl⟩))
  · apply sup_le
    · refine le_inf root_zero_le_plane_radical ?_
      apply le_centralizer_iff.mpr
      rw [RootNormalizerResidual.centralizer_zero_eq]
      exact inf_le_left
    · refine le_inf root_four_le_plane_radical ?_
      apply le_centralizer_iff.mpr
      rw [RootNormalizerResidual.centralizer_four_eq]
      exact inf_le_right

omit [Finite F] [CharP F 2] in
private theorem plane_sylow_normalizer_le :
    planeLocal (F := F) ⊓ normalizer (unipotent (F := F) : Set (Sp F)) ≤
      pointParabolic := by
  rw [← borel_eq_normalizer_unipotent]
  exact inf_le_right.trans inf_le_left

private noncomputable def planeTorus (s : Fˣ) : Sp F := diagonalTorus s s⁻¹

omit [Finite F] [CharP F 2] in
private theorem planeTorus_mem (s : Fˣ) :
    planeTorus s ∈ planeLocal (F := F) ⊓ normalizer (unipotent (F := F) : Set (Sp F)) := by
  rw [← borel_eq_normalizer_unipotent]
  refine ⟨?_, diagonalTorus_mem_borel _ _⟩
  change planeTorus s ∈ planeLocal
  rw [mem_planeLocal_iff]
  refine ⟨(diagonalTorus_mem_borel _ _).2, ?_⟩
  simp [planeTorus, diagonalTorus, Matrix.diagonal]

omit [Finite F] [CharP F 2] in
private theorem planeTorus_root_zero (s : Fˣ) (t : F) :
    ⁅planeTorus s, rootElement 0 t⁆ = rootElement 0 (((s : F)^2 - 1)*t) := by
  dsimp only [planeTorus]
  rw [commutatorElement_def,
    RootNormalizerResidual.point_conjugate _ (diagonalTorus_mem_borel _ _).1]
  have hi : (rootElement (K := F) 0 t)⁻¹ = rootElement 0 (-t) := by
    apply inv_eq_of_mul_eq_one_right
    rw [RootSubgroup.element_add]
    simp [RootSubgroup.element_zero]
  rw [hi, RootSubgroup.element_add]
  congr 1
  simp only [diagonalTorus, Matrix.diagonal_apply_eq, Sum.elim_inl,
    Matrix.cons_val_zero]
  ring

/-- The source long root is the commutator of the Sylow-fixed full module
with its relative Sylow normalizer in the original local group. -/
theorem root_zero_commutator {n : ℕ} (hcard : Nat.card F = 2 ^ n) (hn : 1 < n) :
    ⁅(Plane.radical (F := F)).map planeLocal.subtype ⊓
        centralizer (unipotent (F := F) : Set (Sp F)),
      planeLocal (F := F) ⊓ normalizer (unipotent (F := F) : Set (Sp F))⁆ =
      RootSubgroup.group 0 := by
  rw [plane_radical_fixed_sylow]
  let B := planeLocal (F := F) ⊓ normalizer (unipotent (F := F) : Set (Sp F))
  have hBR : B ≤ normalizer (RootSubgroup.group (F := F) 0 : Set (Sp F)) := by
    rw [RootNormalizerResidual.normalizer_zero_eq]
    exact plane_sylow_normalizer_le
  apply le_antisymm
  · apply commutator_sup_le_of_relative_normal (normalizer (RootSubgroup.group (F := F) 0 : Set (Sp F)))
      (RootSubgroup.group 0) (RootSubgroup.group 4) B (RootSubgroup.group 0)
      le_rfl (RootSubgroup.group 0).le_normalizer
    · rw [RootNormalizerResidual.normalizer_zero_eq]
      exact fun g hg => pointLocal_le (plane_radical_le_unipotent (root_four_le_plane_radical hg)).1
    · exact le_normalizer_iff_commutator_le_left.mp hBR
    · have hc : ⁅RootSubgroup.group (F := F) 4, B⁆ = ⊥ := by
        apply commutator_eq_bot_iff_le_centralizer.mpr
        apply le_centralizer_iff.mpr
        rw [RootNormalizerResidual.centralizer_four_eq]
        exact inf_le_left
      rw [hc]
      exact bot_le
  · have hlarge : 2 < Nat.card F := by
      rw [hcard]
      exact (show 2 = 2^1 by decide).trans_lt (Nat.pow_lt_pow_right (by decide) hn)
    have hc : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
    let : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp hc
    obtain ⟨s,hs⟩ := exists_ne (1 : Fˣ)
    have hd : (s : F)^2 - 1 ≠ 0 := by
      intro he
      have he' : (s : F)^2 = (1 : F)^2 := by simpa using sub_eq_zero.mp he
      exact hs (Units.ext (CharTwo.sq_injective he'))
    intro z hz
    obtain ⟨t,rfl⟩ := (RootSubgroup.mem_group_iff 0 z).mp hz
    rw [commutator_comm]
    have hh := commutator_mem_commutator (planeTorus_mem s)
      (mem_sup_left ((RootSubgroup.mem_group_iff 0 _).mpr
        ⟨t / ((s:F)^2-1), rfl⟩) :
        rootElement (K:=F) 0 (t / ((s:F)^2-1)) ∈ RootSubgroup.group 0 ⊔ RootSubgroup.group 4)
    rw [planeTorus_root_zero, mul_div_cancel₀ _ hd] at hh
    exact hh
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootCoreMatrix
