module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.PointModels.Generation
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.ParabolicResiduals
public import Theory.Representation.SpecialLinearThreeFrameGeometry.Transitivity
public import Theory.Representation.SLHigherNaturalFirstCohomology.Elementary

/-!
# Two field-line residuals generate full SL₃

The two coordinate-vector fixers contain every elementary transvection between
them, and hence generate SL₃. Literal two-point transitivity transports this
to arbitrary distinct field lines. Every nonzero vector fixer is a conjugate
of the perfect point local, so it lies in the solvable residual of its line
stabilizer. The proof retains full SL₃ and includes q=4 and its center.

Source: Aschbacher--Smith, 11.5.3(1), printed p.779.
-/

@[expose] public noncomputable section
open Subgroup Matrix Representation
open scoped MatrixGroups
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.PointModels.LinearThree
variable {F : Type*} [Field F]

private theorem standard_fixers_generate :
    MulAction.stabilizer SL(3,F) (![1,0,0] : Fin 3 → F) ⊔
      MulAction.stabilizer SL(3,F) (![0,1,0] : Fin 3 → F) = ⊤ := by
  apply top_unique
  intro g _
  apply OneCohomology.SLHigherNatural.transvection_induction (fun g => g ∈ _) _ _ g
  · intro i j hij t
    by_cases hj : j = 0
    · apply mem_sup_right
      rw [MulAction.mem_stabilizer_iff]
      change specialLinearNatural 3 (SpecialLinearGroup.transvection hij t) _ = _
      rw [OneCohomology.SLHigherNatural.action_transvection]
      simp [hj]
    · apply mem_sup_left
      rw [MulAction.mem_stabilizer_iff]
      change specialLinearNatural 3 (SpecialLinearGroup.transvection hij t) _ = _
      rw [OneCohomology.SLHigherNatural.action_transvection]
      fin_cases j <;> simp_all
  · exact fun _ _ => Subgroup.mul_mem _

variable [Finite F]
private theorem vector_fixer_perfect (hF : 4 ≤ Nat.card F)
    {u : Fin 3 → F} (hu : u ≠ 0) : Group.IsPerfect (MulAction.stabilizer SL(3,F) u) := by
  have he0 : (![1,0,0] : Fin 3 → F) ≠ 0 := by
    intro he
    have hh := congrFun he 0
    simp at hh
  obtain ⟨g, hg⟩ := SpecialLinearGroup.exists_mulVec_eq_three _ u he0 hu
  have he : MulAction.stabilizer SL(3,F) (![1,0,0] : Fin 3 → F) =
      PSL3.LinearThree.pointLocalSL F := by
    ext a
    rw [MulAction.mem_stabilizer_iff, PSL3.LinearThree.mem_pointLocalSL_iff]
    change a.val *ᵥ ![1,0,0] = ![1,0,0] ↔ _
    have hx (i : Fin 3) : (a.val *ᵥ (![1,0,0] : Fin 3 → F)) i = a.val i 0 := by
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    constructor
    · intro h
      exact ⟨(hx 0).symm.trans (congrFun h 0),
        (hx 1).symm.trans (congrFun h 1), (hx 2).symm.trans (congrFun h 2)⟩
    · intro h
      ext i
      rw [hx]
      fin_cases i
      · exact h.1
      · exact h.2.1
      · exact h.2.2
  have hp : Group.IsPerfect (MulAction.stabilizer SL(3,F) (![1,0,0] : Fin 3 → F)) := by
    rw [he]
    exact PSL3.LinearThree.pointLocalSL_isPerfect F hF
  let := hp
  have hg' : u = g • (![1,0,0] : Fin 3 → F) := hg.symm
  let e := MulAction.stabilizerEquivStabilizer hg'
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

open CFSG.Quasithin.ChapterB.QuasisimpleSource
/-- Two distinct line residuals generate full SL₃, including its center. -/
theorem linePairGeneration (F : BinaryField) (hn : 1 < F.degree) :
    LinePairGeneration F (specialLinearNatural (k := F.Carrier) 3) := by
  intro U W hU hW hUW
  let u₀ : Fin 3 → F.Carrier := ![1,0,0]
  let w₀ : Fin 3 → F.Carrier := ![0,1,0]
  have hu₀ : u₀ ≠ 0 := by intro he; have := congrFun he 0; simp [u₀] at this
  have hw₀ : w₀ ≠ 0 := by intro he; have := congrFun he 1; simp [w₀] at this
  have hne : Submodule.span F.Carrier {u₀} ≠ Submodule.span F.Carrier {w₀} := by
    intro he
    have hh : u₀ ∈ Submodule.span F.Carrier {w₀} := he ▸ Submodule.mem_span_singleton_self u₀
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hh
    have := congrFun ht 0
    simp [u₀, w₀] at this
  obtain ⟨g, hgU, hgW⟩ := SpecialLinearGroup.FrameGeometry.exists_point_pair_map
    (Submodule.span F.Carrier {u₀}) (Submodule.span F.Carrier {w₀}) U W
    (finrank_span_singleton hu₀) (finrank_span_singleton hw₀) hU hW hne hUW
  have hu : g • u₀ ∈ U := hgU ▸ Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self u₀)
  have hw : g • w₀ ∈ W := hgW ▸ Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self w₀)
  have hgen : MulAction.stabilizer SL(3,F.Carrier) (g • u₀) ⊔
      MulAction.stabilizer SL(3,F.Carrier) (g • w₀) = ⊤ := by
    rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj,
      MulAction.stabilizer_smul_eq_stabilizer_map_conj, ← Subgroup.map_sup]
    rw [standard_fixers_generate]
    exact Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective
  have hfour : 4 ≤ Nat.card F.Carrier := by
    rw [F.card_eq]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn
  have hle (P : Submodule F.Carrier (Fin 3 → F.Carrier)) (hP : Module.finrank F.Carrier P = 1)
      (v : Fin 3 → F.Carrier) (hv : v ∈ P) (hv0 : v ≠ 0) :
      MulAction.stabilizer SL(3,F.Carrier) v ≤ residualIn
        (BinaryOffender.subspaceStabilizer
          (restrictScalars (k := ZMod 2) (specialLinearNatural (k := F.Carrier) 3))
          (P.restrictScalars (ZMod 2))) := by
    let := vector_fixer_perfect hfour hv0
    apply le_map_solvableResidual_of_isPerfect
    intro a ha x
    have hav : a • v = v := ha
    have hfix (y : Fin 3 → F.Carrier) (hy : y ∈ P) : a • y = y := by
      rw [eq_span_singleton_of_mem_of_finrank_eq_one hP hv hv0] at hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      change Matrix.mulVec a.val (c • v) = c • v
      rw [Matrix.mulVec_smul]
      change c • (a • v) = c • v
      rw [hav]
    change a • x ∈ P ↔ x ∈ P
    constructor
    · intro hx
      have he : a • (a • x) = a • x := hfix _ hx
      exact (MulAction.injective a he) ▸ hx
    · intro hx
      rw [hfix x hx]
      exact hx
  apply top_unique
  rw [← hgen]
  exact sup_le (le_sup_of_le_left (hle U hU _ hu ((smul_ne_zero_iff_ne g).mpr hu₀)))
    (le_sup_of_le_right (hle W hW _ hw ((smul_ne_zero_iff_ne g).mpr hw₀)))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.PointModels.LinearThree
