module

public import Theory.Representation.BinaryNaturalDual.ModelOrbits.AutomorphismModel
public import Theory.Representation.BinaryNaturalDual.ModelOrbits.MarkedComparison.Transport

/-!
# Aligning the source layer and its marked natural module

An arbitrary identification of M with Aut(PSLₙ(2)) identifies E(M) with the
inner subgroup. Its induced marking of E(M) need not agree with the marking
that makes the first module summand natural. Conjugating the automorphism
model by the difference of these two markings constructs a compatible group
isomorphism. The marked comparison then constructs the dual and whole-module
linear equivalences from the outer-image condition alone.

Source: Aschbacher–Smith, H.9 setup and H.9.1(1–2), printed pp.389–390.
-/

public section

open BinaryNaturalDual BinaryNaturalDual.ModelOrbits BinaryNaturalDual.ModelOrbits.AutomorphismModel
open BinaryLinear.OuterCyclic Theory.GroupTheory
open scoped MatrixGroups

namespace BinaryNaturalDual.ModelOrbits.SourceComparison

private theorem map_layer_le {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (componentLayer G).map e.toMonoidHom ≤ componentLayer H := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply sSup_le
  intro K hK
  exact Subgroup.map_le_iff_le_comap.mp (le_sSup (hK.map_equiv e))

/-- Group isomorphisms preserve the actual component layer. -/
theorem map_componentLayer {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (componentLayer G).map e.toMonoidHom = componentLayer H := by
  apply le_antisymm (map_layer_le e)
  rw [Subgroup.map_equiv_eq_comap_symm']
  exact Subgroup.map_le_iff_le_comap.mp (map_layer_le e.symm)

/-- The source group isomorphism carries the actual layer to the projective inner subgroup. -/
theorem componentLayer_map_projective {n : ℕ} (hn : 3 ≤ n)
    {M : Type*} [Group M] (eM : M ≃* MulAut PSL(n, ZMod 2)) :
    (componentLayer M).map eM.toMonoidHom = MulAut.innerSubgroup PSL(n, ZMod 2) := by
  rw [map_componentLayer, projective_layer_eq_inner hn]

/-- The layer of a source group has index exactly two. -/
theorem componentLayer_index {n : ℕ} (hn : n = 4 ∨ n = 5)
    {M : Type*} [Group M] (eM : M ≃* MulAut PSL(n, ZMod 2)) :
    (componentLayer M).index = 2 := by
  have h := Subgroup.index_map_of_bijective (f := eM.toMonoidHom)
    eM.bijective (componentLayer M)
  rw [componentLayer_map_projective (by omega : 3 ≤ n), projective_inner_index hn] at h
  exact h.symm

/-- Align the actual automorphism model with any specified marking of the layer. -/
theorem exists_layerCompatible {n : ℕ} (hn : n = 4 ∨ n = 5)
    {M : Type*} [Group M] (eM : M ≃* MulAut PSL(n, ZMod 2))
    (eL : componentLayer M ≃* LinearGroup n) :
    ∃ e : M ≃* MulAut (LinearGroup n),
      (∀ l : componentLayer M, e l = MulAut.conj (eL l)) ∧
      (∀ m : M, e m ∈ MulAut.innerSubgroup (LinearGroup n) ↔ m ∈ componentLayer M) := by
  let e₀ := eM.trans (projectiveAutEquiv (by omega : 0 < n))
  have hmap : (componentLayer M).map e₀.toMonoidHom =
      MulAut.innerSubgroup (LinearGroup n) := by
    rw [map_componentLayer, layer_eq_inner (by omega : 3 ≤ n)]
  let f : componentLayer M ≃* MulAut.innerSubgroup (LinearGroup n) :=
    (e₀.subgroupMap (componentLayer M)).trans (MulEquiv.subgroupCongr hmap)
  let β : LinearGroup n ≃* LinearGroup n :=
    (innerEquiv (by omega : 0 < n)).trans (f.symm.trans eL)
  let e := e₀.trans (MulAut.congr β)
  have he (l : componentLayer M) : e l = MulAut.conj (eL l) := by
    have hi : e₀ l = MulAut.conj ((innerEquiv (by omega : 0 < n)).symm (f l)) := by
      rw [← innerEquiv_apply]
      exact (congrArg Subtype.val ((innerEquiv (by omega : 0 < n)).apply_symm_apply (f l))).symm
    change MulAut.congr β (e₀ l) = _
    rw [hi, MulAut.congr_conj]
    simp [β]
  refine ⟨e, he, ?_⟩
  intro m
  constructor
  · rintro ⟨g, hg⟩
    have heq : ((eL.symm g : componentLayer M) : M) = m := by
      apply e.injective
      rw [he, eL.apply_symm_apply, hg]
    exact heq ▸ (eL.symm g).property
  · intro hm
    exact ⟨eL ⟨m, hm⟩, (he ⟨m, hm⟩).symm⟩

/-- Construct both marked linear equivalences and their full equivariance; only
the natural action on the first summand and its outer image are assumed. -/
theorem exists_marked_equiv {n : ℕ} (hn : n = 4 ∨ n = 5) (A : CoordinateAction n)
    {M V : Type*} [Group M] [AddCommGroup V] [Module (ZMod 2) V]
    (eM : M ≃* MulAut PSL(n, ZMod 2))
    (eL : componentLayer M ≃* LinearGroup n)
    (ρ : Representation (ZMod 2) M V)
    {U W : Submodule (ZMod 2) V} (hUW : IsCompl U W)
    (eU : U ≃ₗ[ZMod 2] BinaryLinear.OuterCyclic.Space n)
    (hU : ∀ (l : componentLayer M) (x : BinaryLinear.OuterCyclic.Space n),
      ρ l (eU.symm x : V) = (eU.symm (eL l x) : V))
    (hout : ∃ t : M, t ∉ componentLayer M ∧ U.map (ρ t) = W) :
    ∃ (e : M ≃* MulAut (LinearGroup n))
      (eW : W ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n))
      (eV : V ≃ₗ[ZMod 2] CoordinateSpace n),
      (∀ l : componentLayer M, e l = MulAut.conj (eL l)) ∧
      (∀ m : M, e m ∈ MulAut.innerSubgroup (LinearGroup n) ↔ m ∈ componentLayer M) ∧
      (∀ u : U, eV u = (eU u, 0)) ∧
      (∀ w : W, eV w = (0, eW w)) ∧
      (∀ m v, eV (ρ m v) = A.representation (e m) (eV v)) := by
  obtain ⟨e, hel, hem⟩ := exists_layerCompatible hn eM eL
  have hnat (g : LinearGroup n) (x : BinaryLinear.OuterCyclic.Space n) :
      ρ (e.symm (MulAut.conj g)) (eU.symm x : V) = (eU.symm (g x) : V) := by
    have he : e.symm (MulAut.conj g) = (eL.symm g : M) := by
      apply e.injective
      rw [e.apply_symm_apply, hel, eL.apply_symm_apply]
    rw [he, hU, eL.apply_symm_apply]
  have ho : ∃ t : M, e t ∉ MulAut.innerSubgroup (LinearGroup n) ∧ U.map (ρ t) = W := by
    obtain ⟨t, ht, hw⟩ := hout
    exact ⟨t, fun hi => ht ((hem t).mp hi), hw⟩
  obtain ⟨eW, eV, hnat', hdual, hact⟩ :=
    MarkedComparison.exists_equiv_of_groupEquiv hn A ρ e hUW eU hnat ho
  exact ⟨e, eW, eV, hel, hem, hnat', hdual, hact⟩

end BinaryNaturalDual.ModelOrbits.SourceComparison
