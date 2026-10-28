module
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Irreducibility of the actual radical-six conjugation action

A nontrivial subgroup of the last-column shears normalized by the four-space
parabolic contains every shear. Upper-block transvections extract each
coordinate line from any nonzero shear parameter. The same literal radical
lies in the full flag group and is normalized by the endpoint parabolic.

Source: Aschbacher--Smith, the natural module in 12.5.2(4) and its use in
12.5.10, printed pp.817,821. This is intrinsic matrix-group mathematics;
no ambient classification or actor-generation premise is used.
-/

@[expose] public noncomputable section
open Subgroup
open scoped BigOperators
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional

theorem radicalSix_le_flagGroup : parabolicResidualTwoCore 4 ≤ flagGroup := by
  rw [parabolicResidualTwoCore_four]
  intro g hg
  obtain ⟨u, rfl⟩ := (mem_shearSubgroup g).mp hg
  apply mem_iInf.mpr
  intro k
  apply (mem_parabolic_iff_lowerLeft_zero k.val _).mpr
  intro i j hi hj
  rw [matrix_shear]
  fin_cases i <;> fin_cases j <;> simp_all <;> omega

theorem parabolic_four_normalizes_radicalSix :
    parabolic 4 ≤ normalizer (parabolicResidualTwoCore 4 : Set Group) := by
  have he : parabolicResidualTwoCore 4 =
      (pCore 2 (parabolic 4)).map (parabolic 4).subtype := by
    unfold parabolicResidualTwoCore
    rw [parabolicResidualFlag_four]
  rw [he]
  exact (parabolic 4).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 (parabolic 4)))

private theorem elementary_four_mem (i j : Fin 4) (hij : i ≠ j) :
    elementary i.castSucc j.castSucc ∈ parabolic 4 := by
  rw [parabolic_eq_closure_transvections]
  apply Subgroup.subset_closure
  have hne : i.castSucc ≠ j.castSucc := fun h => hij (Fin.castSucc_injective 4 h)
  exact ⟨i.castSucc, j.castSucc, hne, 1, fun _ => i.isLt, by simp [elementary, hne]⟩

private theorem upperFourBlock_elementary (i j : Fin 4) (hij : i ≠ j)
    (v : ShearParameter) :
    (upperFourBlock (elementary i.castSucc j.castSucc)).mulVec v =
      v + v j • Pi.single i 1 := by
  have hne : i.castSucc ≠ j.castSucc := fun h => hij (Fin.castSucc_injective 4 h)
  ext k
  simp [upperFourBlock, elementary, hne, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.mulVec, dotProduct, Matrix.one_apply, Matrix.single,
    Pi.single_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib, eq_comm]
  by_cases hik : i = k <;> simp [hik]

/-- The endpoint parabolic acts irreducibly on the actual radical-six subgroup.
The proof extracts every coordinate direction using its upper-block transvections. -/
theorem shearSubgroup_le_of_normalized_nontrivial {A : Subgroup Group}
    (hA : A ≤ shearSubgroup) (hne : A ≠ ⊥)
    (hn : parabolic 4 ≤ normalizer (A : Set Group)) : shearSubgroup ≤ A := by
  obtain ⟨⟨a, ha⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have ha1 : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  obtain ⟨v, rfl⟩ := (mem_shearSubgroup a).mp (hA ha)
  have hv0 : v ≠ 0 := fun h => ha1 (h ▸ shear_zero)
  have hcoord : ∃ j, v j ≠ 0 := by
    by_contra! h
    exact hv0 (funext h)
  obtain ⟨j, hj⟩ := hcoord
  have hj1 : v j = 1 := (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _ hj
  let P := shearParameters A
  have step (i k : Fin 4) (hik : i ≠ k) (w : ShearParameter) (hw : w ∈ P) :
      w k • Pi.single i 1 ∈ P := by
    have hc := (mem_normalizer_iff.mp (hn (elementary_four_mem i k hik)) (shear w)).mp hw
    rw [conjugate_shear _ (elementary_four_mem i k hik),
      upperFourBlock_elementary i k hik] at hc
    have hh := P.sub_mem hc hw
    simpa only [add_sub_cancel_left] using hh
  have hi (i : Fin 4) (hij : i ≠ j) : Pi.single i (1 : ZMod 2) ∈ P := by
    simpa only [hj1, one_smul] using step i j hij v ha
  have hjP : Pi.single j (1 : ZMod 2) ∈ P := by
    obtain ⟨i, hij⟩ := exists_ne j
    have hh := step j i hij.symm (Pi.single i 1) (hi i hij)
    simpa only [Pi.single_eq_same, one_smul] using hh
  have hall (i : Fin 4) : Pi.single i (1 : ZMod 2) ∈ P := by
    by_cases he : i = j
    · subst i; exact hjP
    · exact hi i he
  intro x hx
  obtain ⟨w, rfl⟩ := (mem_shearSubgroup x).mp hx
  change w ∈ P
  have he : w = ∑ i : Fin 4, w i • Pi.single i (1 : ZMod 2) := by
    ext i
    simp [Pi.single_apply]
  rw [he]
  exact P.sum_mem (fun i _ => P.smul_mem _ (hall i))

end Representation.SL5ExteriorSquare
