module

public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.RadicalOrientation.Duality
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Actual inverse transpose on binary subspace stabilizers

The coordinate dot product is nondegenerate. Its orthogonal complement
reverses subspace dimensions and is involutive. The established pairing
identity for `OuterCyclic.graphLinear` therefore identifies its image of
every geometric stabilizer with the orthogonal-complement stabilizer.
For `graphLinear * MulAut.conj g`, the subspace first moves by `g`, and then
its orthogonal complement is taken. This explicitly retains the inner
adjustment in the specified automorphism product.

This is the duality calculation used for Aschbacher–Smith 13.8.25,
printed pp.959–960 of `refs/quasithin.pdf`; see also GLS3 §2.7 for the
inverse-transpose matrix formula. No diagram action is assumed.
-/

public section

namespace BinaryLinear.InvariantNodeActions
open OuterCyclic Matrix

private def flagPairing (n : ℕ) : LinearMap.BilinForm (ZMod 2) (Space n) :=
  dotProductBilin (ZMod 2) (ZMod 2)

private theorem flagPairing_nondegenerate (n : ℕ) : (flagPairing n).Nondegenerate := by
  constructor
  · intro x hx
    funext i
    change x i = 0
    have h := hx (Pi.single i 1)
    change dotProduct x (Pi.single i 1) = 0 at h
    simpa only [dotProduct_single, mul_one] using h
  · intro x hx
    funext i
    change x i = 0
    have h := hx (Pi.single i 1)
    change dotProduct (Pi.single i 1) x = 0 at h
    simpa only [single_dotProduct, one_mul] using h

private theorem flagPairing_refl (n : ℕ) : (flagPairing n).IsRefl := by
  intro x y h
  change dotProduct y x = 0
  change dotProduct x y = 0 at h
  rwa [dotProduct_comm]

/-- Orthogonal complement for the coordinate dot product used by inverse transpose. -/
def flagOrthogonal {n : ℕ} (W : Submodule (ZMod 2) (Space n)) :
    Submodule (ZMod 2) (Space n) := (flagPairing n).orthogonal W

theorem mem_flagOrthogonal {n : ℕ} (W : Submodule (ZMod 2) (Space n)) (x : Space n) :
    x ∈ flagOrthogonal W ↔ ∀ w ∈ W, dotProduct w x = 0 := Iff.rfl

theorem flagOrthogonal_finrank {n : ℕ} (W : Submodule (ZMod 2) (Space n)) :
    Module.finrank (ZMod 2) (flagOrthogonal W) = n - Module.finrank (ZMod 2) W := by
  rw [flagOrthogonal, LinearMap.BilinForm.finrank_orthogonal (flagPairing_nondegenerate n)]
  rw [Module.finrank_fin_fun]

theorem flagOrthogonal_involutive {n : ℕ} (W : Submodule (ZMod 2) (Space n)) :
    flagOrthogonal (flagOrthogonal W) = W :=
  LinearMap.BilinForm.orthogonal_orthogonal (flagPairing_nondegenerate n) (flagPairing_refl n) W

private theorem graph_involutive {n : ℕ} (s : LinearGroup n) :
    graphLinear n (graphLinear n s) = s := by
  have h := congrArg (fun a : MulAut (LinearGroup n) => a s) (graphLinear_sq n)
  exact h

private theorem graph_pairing {n : ℕ} (s : LinearGroup n) (x y : Space n) :
    dotProduct y (graphLinear n s x) = dotProduct (s⁻¹ y) x := by
  rw [dotProduct_comm y, dotProduct_comm (s⁻¹ y)]
  simpa only [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] using
    graphLinear_dotProduct s x (s⁻¹ y)

private theorem graph_parabolic_le {n : ℕ} (W : Submodule (ZMod 2) (Space n)) :
    (parabolic W).map (graphLinear n).toMonoidHom ≤ parabolic (flagOrthogonal W) := by
  have hpres (s : LinearGroup n) (hs : s ∈ parabolic W) (v : Space n)
      (hv : v ∈ flagOrthogonal W) : graphLinear n s v ∈ flagOrthogonal W := by
    intro w hw
    change dotProduct w (graphLinear n s v) = 0
    rw [graph_pairing]
    exact hv _ (((parabolic W).inv_mem hs w).mpr hw)
  rintro _ ⟨s, hs, rfl⟩ v
  change graphLinear n s v ∈ flagOrthogonal W ↔ v ∈ flagOrthogonal W
  refine ⟨?_, hpres s hs v⟩
  intro hv
  have h := hpres s⁻¹ ((parabolic W).inv_mem hs) (graphLinear n s v) hv
  simpa only [map_inv, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] using h

/-- The actual inverse transpose sends every subspace stabilizer to the
stabilizer of its coordinate orthogonal complement. -/
theorem graph_map_parabolic {n : ℕ} (W : Submodule (ZMod 2) (Space n)) :
    (parabolic W).map (graphLinear n).toMonoidHom = parabolic (flagOrthogonal W) := by
  apply le_antisymm (graph_parabolic_le W)
  intro s hs
  have ht : graphLinear n s ∈ parabolic W := by
    rw [← flagOrthogonal_involutive W]
    exact graph_parabolic_le (flagOrthogonal W) (Subgroup.mem_map.mpr ⟨s, hs, rfl⟩)
  exact Subgroup.mem_map.mpr ⟨graphLinear n s, ht, graph_involutive s⟩

theorem inner_map_parabolic {n : ℕ} (W : Submodule (ZMod 2) (Space n))
    (g : LinearGroup n) :
    (parabolic W).map (MulAut.conj g).toMonoidHom = parabolic (W.map g.toLinearMap) := by
  ext s
  rw [Subgroup.mem_map_equiv]
  change (∀ v, ((MulAut.conj g).symm s) v ∈ W ↔ v ∈ W) ↔
    ∀ v, s v ∈ W.map g.toLinearMap ↔ v ∈ W.map g.toLinearMap
  simp_rw [Submodule.mem_map_equiv]
  constructor
  · intro hs v
    have h := hs (g.symm v)
    simpa only [MulAut.conj_symm_apply, LinearEquiv.mul_apply,
      LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] using h
  · intro hs v
    have h := hs (g v)
    simpa only [MulAut.conj_symm_apply, LinearEquiv.mul_apply,
      LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] using h

/-- The inner adjustment acts on the original subspace before taking the
orthogonal complement; this is the specified product `graphLinear * conj g`. -/
theorem graph_inner_map_parabolic {n : ℕ} (W : Submodule (ZMod 2) (Space n))
    (g : LinearGroup n) :
    (parabolic W).map (graphLinear n * MulAut.conj g).toMonoidHom =
      parabolic (flagOrthogonal (W.map g.toLinearMap)) := by
  change (parabolic W).map ((graphLinear n).toMonoidHom.comp (MulAut.conj g).toMonoidHom) = _
  rw [← Subgroup.map_map, inner_map_parabolic, graph_map_parabolic]

end BinaryLinear.InvariantNodeActions
