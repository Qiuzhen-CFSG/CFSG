module
public import Theory.Representation.SymplecticFourOrthogonalCover.SylowFlag.Natural
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover.FixedRadical

/-!
# The intrinsic three-step flag of a symplectic Sylow

The first two steps are the fixed space and the fixed space modulo the first
step. A coordinate calculation supplies the third step, the perpendicular
hyperplane. Orthogonal duality reduces uniqueness of that hyperplane to the
existing uniqueness of the line. Sylow conjugacy transports the whole flag,
including its intrinsic fixed-space characterizations.

Source: Aschbacher--Smith, 11.0.2 and opening section 11.1, pp.759--761.
-/

@[expose] public noncomputable section
open Subgroup
set_option linter.unusedSectionVars false
open Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Sp4.ModelFlag
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The three-space perpendicular to the standard fixed point. -/
def hyperplane : Submodule F (Vector F) := (form F).orthogonal (point F)

theorem mem_hyperplane (x : Vector F) : x ∈ hyperplane ↔ x (.inr 0) = 0 := by
  constructor
  · intro hx
    have h := hx (e 0) (Submodule.subset_span (by simp))
    have h' := TwoLocalCover.form_alternating.eq_iff.mp h
    simpa using h'
  · intro hx y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [map_smul]
    have h : form F (e 0) x = 0 :=
      TwoLocalCover.form_alternating.eq_iff.mpr (by simpa using hx)
    simp [h]

theorem hyperplane_finrank : Module.finrank F (hyperplane (F := F)) = 3 := by
  rw [hyperplane, LinearMap.BilinForm.finrank_orthogonal TwoLocalCover.form_nondegenerate,
    finrank_point]
  simp [Theory.SpecificGroups.SymplecticFour.Vector]

theorem plane_le_hyperplane : plane F ≤ hyperplane := fun x hx =>
  (mem_hyperplane x).mpr (hx 0)

private theorem orthogonal_invariant (P : Subgroup (Sp F))
    (W : Submodule F (Vector F)) (hW : P ≤ stabilizer W) :
    P ≤ stabilizer ((form F).orthogonal W) := by
  intro g hg
  rw [mem_stabilizer_iff]
  intro x hx y hy
  have hy' := (mem_stabilizer_iff W g⁻¹).mp (hW (P.inv_mem hg)) y hy
  have h := preserves_form g (g⁻¹ • y) x
  rw [smul_inv_smul] at h
  exact h.trans (hx _ hy')

/-- Uniqueness of the third step is dual to uniqueness of the first. -/
theorem unipotent_hyperplane_unique (W : Submodule F (Vector F))
    (hW : unipotent ≤ stabilizer W) (hdim : Module.finrank F W = 3) :
    W = hyperplane := by
  have ho := orthogonal_invariant unipotent W hW
  have hd : Module.finrank F ((form F).orthogonal W) = 1 := by
    rw [LinearMap.BilinForm.finrank_orthogonal TwoLocalCover.form_nondegenerate, hdim]
    simp [Theory.SpecificGroups.SymplecticFour.Vector]
  have he := Representation.SymplecticFourOrthogonalCover.SylowFlag.invariant_line_unique
    ((form F).orthogonal W) (fun g x hx =>
      (mem_stabilizer_iff _ g.val.val).mp (ho g.property) x hx) hd
  have h := congrArg (form F).orthogonal he
  rw [LinearMap.BilinForm.orthogonal_orthogonal TwoLocalCover.form_nondegenerate
    TwoLocalCover.form_alternating.isRefl] at h
  exact h

/-- The third stage is recovered by fixed vectors modulo the standard plane. -/
theorem fixedModulo_plane_iff (x : Vector F) :
    (∀ u ∈ unipotent (F := F), u • x - x ∈ plane F) ↔ x ∈ hyperplane := by
  constructor
  · intro h
    have h6 := h (rootElement 6 1) (positive_root_mem_unipotent 6 1 (by simp)) 1
    rw [mem_hyperplane]
    simpa [rootElement, rootMatrix, smul_eq_mulVec, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.fromBlocks, Matrix.single,
      Matrix.one_apply] using h6
  · intro hx u hu
    obtain ⟨⟨b,a,w,v⟩, he⟩ := CentralRootGeometry.element_surjective (⟨u,hu⟩ : unipotent)
    have hu' : u.val = (CentralRootGeometry.element b a w v).val.val :=
      congrArg (fun z : unipotent (F := F) => z.val.val) he.symm
    have hx0 := (mem_hyperplane x).mp hx
    intro i
    fin_cases i <;>
      simp [smul_eq_mulVec, hu', CentralRootGeometry.element_matrix, Matrix.mulVec,
        dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.fromBlocks, hx0]

/-- Stages zero through three of the intrinsic fixed-space filtration. -/
def stage : Fin 4 → Submodule F (Vector F) := ![⊥, point F, plane F, hyperplane]

theorem stage_dimension (i : Fin 4) : Module.finrank F (stage (F := F) i) = i.val := by
  fin_cases i
  · exact finrank_bot _ _
  · exact finrank_point
  · exact finrank_plane
  · exact hyperplane_finrank

theorem stage_nested : Monotone (stage (F := F)) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  fin_cases i
  · exact bot_le
  · exact point_le_plane
  · exact plane_le_hyperplane

theorem mem_stage_succ_iff (i : Fin 3) (x : Vector F) :
    x ∈ stage i.succ ↔ ∀ u ∈ unipotent (F := F), u • x - x ∈ stage i.castSucc := by
  fin_cases i
  · change x ∈ point F ↔ ∀ u ∈ unipotent, u • x - x ∈ (⊥ : Submodule F (Vector F))
    simpa only [Submodule.mem_bot, sub_eq_zero] using (fixedBy_unipotent_iff x).symm
  · exact (fixedModulo_point_iff x).symm
  · exact (fixedModulo_plane_iff x).symm

theorem stage_unique (i : Fin 3) (W : Submodule F (Vector F))
    (hW : unipotent ≤ stabilizer W) (hdim : Module.finrank F W = i.val + 1) :
    W = stage i.succ := by
  fin_cases i
  · exact Representation.SymplecticFourOrthogonalCover.SylowFlag.invariant_line_unique W
      (fun g x hx => (mem_stabilizer_iff _ g.val.val).mp (hW g.property) x hx) hdim
  · exact (Representation.SymplecticFourOrthogonalCover.SylowFlag.invariant_plane_unique W
      (fun g x hx => (mem_stabilizer_iff _ g.val.val).mp (hW g.property) x hx) hdim).trans
      Representation.SymplecticFourOrthogonalCover.SylowFlag.secondPlane_eq_plane
  · exact unipotent_hyperplane_unique W hW hdim

/-- Conjugating the standard flag by an actual symplectic matrix. -/
def movedStage (g : Sp F) (i : Fin 4) : Submodule F (Vector F) :=
  (stage i).map (toLinear g).toLinearMap

theorem movedStage_dimension (g : Sp F) (i : Fin 4) :
    Module.finrank F (movedStage g i) = i.val :=
  ((toLinear g).finrank_map_eq _).trans (stage_dimension i)

theorem movedStage_nested (g : Sp F) : Monotone (movedStage g) :=
  fun _ _ hij => Submodule.map_mono (stage_nested hij)

theorem movedStage_zero (g : Sp F) : movedStage g 0 = ⊥ := Submodule.map_bot _

private theorem action_inv (g : Sp F) (x : Vector F) :
    (toLinear g).symm x = g⁻¹ • x := by
  change ((toLinear g)⁻¹) x = _
  rw [← map_inv]
  rfl

theorem mem_movedStage (g : Sp F) (i : Fin 4) (x : Vector F) :
    x ∈ movedStage g i ↔ g⁻¹ • x ∈ stage i := by
  rw [movedStage, Submodule.mem_map_equiv, action_inv]

/-- The moved flag retains its intrinsic fixed-space filtration. -/
theorem mem_movedStage_succ_iff (g : Sp F) (i : Fin 3) (x : Vector F) :
    x ∈ movedStage g i.succ ↔
      ∀ u ∈ (unipotent (F := F)).map (MulAut.conj g).toMonoidHom,
        u • x - x ∈ movedStage g i.castSucc := by
  rw [mem_movedStage, mem_stage_succ_iff]
  constructor
  · rintro h _ ⟨u, hu, rfl⟩
    rw [mem_movedStage]
    change toLinear g⁻¹ (_ - _) ∈ _
    rw [map_sub]
    simpa only [toLinear_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      mul_smul, inv_smul_smul] using h u hu
  · intro h u hu
    have hh := (mem_movedStage g i.castSucc _).mp
      (h ((MulAut.conj g) u) ⟨u, hu, rfl⟩)
    change toLinear g⁻¹ (_ - _) ∈ _ at hh
    rw [map_sub] at hh
    simpa only [toLinear_apply, MulAut.conj_apply, mul_smul, inv_smul_smul] using hh

/-- Each dimension has exactly one invariant space for the moved Sylow. -/
theorem movedStage_unique (g : Sp F) (i : Fin 3) (W : Submodule F (Vector F))
    (hW : (unipotent (F := F)).map (MulAut.conj g).toMonoidHom ≤ stabilizer W)
    (hdim : Module.finrank F W = i.val + 1) : W = movedStage g i.succ := by
  let U := W.comap (toLinear g).toLinearMap
  have hU : unipotent ≤ stabilizer U := by
    intro u hu
    rw [mem_stabilizer_iff]
    intro x hx
    have hh := (mem_stabilizer_iff W ((MulAut.conj g) u)).mp
      (hW ⟨u, hu, rfl⟩) (g • x) hx
    change g • (u • x) ∈ W
    simpa only [MulAut.conj_apply, mul_smul, inv_smul_smul] using hh
  have he := stage_unique i U hU (by
    have hm := (toLinear g).finrank_map_eq U
    rw [Submodule.map_comap_eq_of_surjective (toLinear g).surjective] at hm
    exact hm.symm.trans hdim)
  have hm := congrArg (Submodule.map (toLinear g).toLinearMap) he
  rw [Submodule.map_comap_eq_of_surjective (toLinear g).surjective] at hm
  exact hm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Sp4.ModelFlag
