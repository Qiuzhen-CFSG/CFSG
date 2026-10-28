module

public import Theory.Representation.PSL3Two.IrreducibleCatalogue.FanoDecomposition.Transitive
public import Theory.Representation.PSL3Two.NaturalOrbits

/-!
# Sylow stabilizers of natural binary subspaces

An adapted basis carries each subspace of the natural three-space to an
initial coordinate space. Upper triangular matrices preserve every such
space; conjugating the marked flag Sylow gives a Sylow stabilizer of the
original subspace. Over the binary field the change of basis has determinant
one, so the conjugator lies in the actual SL₃(2) model.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
J.2.3(6), printed p.433 (PDF p.444), the natural-parabolic step.
-/

@[expose] public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender Matrix.PSL3Two
open BinaryLinearThree
namespace BinaryLinearThree.SteinbergStructure.PointRadicalFixedSpace

private def initial (n : Fin 4) : Submodule (ZMod 2) Vector where
  carrier := {v | ∀ i : Fin 3, n.val ≤ i.val → v i = 0}
  zero_mem' := by intro i hi; rfl
  add_mem' := by intro x y hx hy i hi; change x i + y i = 0; rw [hx i hi, hy i hi, zero_add]
  smul_mem' := by intro a v hv i hi; change a * v i = 0; rw [hv i hi, mul_zero]
private theorem initial_card (n : Fin 4) : Nat.card (initial n) = 2 ^ n.val := by
  change Nat.card {v : Vector // ∀ i : Fin 3, n.val ≤ i.val → v i = 0} = _
  rw [Nat.card_eq_fintype_card]
  fin_cases n <;> decide +kernel
private theorem initial_rank (n : Fin 4) : Module.finrank (ZMod 2) (initial n) = n.val := by
  apply Nat.pow_right_injective (by decide : 1 < 2)
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := initial n)
  rw [Nat.card_zmod, initial_card] at h
  exact h.symm
private theorem initial_stable (n : Fin 4) (a : Group) (ha : a ∈ borelSL)
    (v : Vector) (hv : v ∈ initial n) : W a v ∈ initial n := by
  change ∀ i : Fin 3, n.val ≤ i.val → (a.val.mulVec v) i = 0
  change ∀ i : Fin 3, n.val ≤ i.val → v i = 0 at hv
  have htri := (mem_borelSL_iff a).mp ha
  fin_cases n <;> simp only [Fin.forall_fin_succ] at hv ⊢ <;>
    simp_all [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- Every natural subspace is invariant under an actual Sylow two-subgroup. -/
theorem natural_subspace_sylow (A : Submodule (ZMod 2) Vector) :
    ∃ P : Sylow 2 Group, ∀ g ∈ (P : Subgroup Group), ∀ v ∈ A, W g v ∈ A := by
  have hr : Module.finrank (ZMod 2) A ≤ 3 := by
    simpa only [Vector, Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one] using A.finrank_le
  let n : Fin 4 := ⟨Module.finrank (ZMod 2) A, by omega⟩
  let e : initial n ≃ₗ[ZMod 2] A := LinearEquiv.ofFinrankEq _ _ (initial_rank n)
  obtain ⟨f, hf⟩ := Submodule.exists_linearEquiv_restrict_eq e
  have hm (v : Vector) : f v ∈ A ↔ v ∈ initial n := by
    constructor
    · intro hv
      let w := e.symm ⟨f v, hv⟩
      have hw : f w = f v := (hf w).symm.trans (congrArg Subtype.val (e.apply_symm_apply _))
      exact (f.injective hw) ▸ w.property
    · intro hv
      rw [← hf ⟨v,hv⟩]
      exact (e ⟨v,hv⟩).property
  let g : Group := ⟨LinearMap.toMatrix' f.toLinearMap, by
    rw [LinearMap.det_toMatrix']
    exact (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _ f.isUnit_det'.ne_zero⟩
  have hg (v : Vector) : W g v = f v := by
    change Matrix.toLin' (LinearMap.toMatrix' f.toLinearMap) v = f v
    rw [Matrix.toLin'_toMatrix']
    rfl
  refine ⟨g • FanoDecomposition.flagSylow, ?_⟩
  intro a ha v hv
  have ha' : a ∈ borelSL.map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul, FanoDecomposition.flagSylow_coe,
      FanoDecomposition.markedFlag_stabilizer] at ha
    exact ha
  obtain ⟨b,hb,rfl⟩ := ha'
  have hv' : W g⁻¹ v ∈ initial n := (hm _).mp (by rw [← hg, Representation.self_inv_apply]; exact hv)
  change W (g * b * g⁻¹) v ∈ A
  rw [map_mul, map_mul]
  change W g (W b (W g⁻¹ v)) ∈ A
  rw [hg]
  exact (hm _).mpr (initial_stable n b hb _ hv')


end BinaryLinearThree.SteinbergStructure.PointRadicalFixedSpace
