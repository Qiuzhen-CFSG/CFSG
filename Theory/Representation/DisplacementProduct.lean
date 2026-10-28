module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.Tactic.Abel
public meta import Lean.Elab.Tactic.Omega

/-!
# Saturation of displacement ranks

If the displacement ranks of two group elements have bounds r and s,
while a subspace containing every fixed vector of their product has
codimension at least r+s, both bounds are saturated. The displacement
spaces are disjoint, so that subspace is fixed by each factor.

The proof uses rank-nullity and the dimension formula for a sum of subspaces.
It applies over any field and does not require complete reducibility.

Source application: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs
of rank two* (1993), (4.6.12)(4), printed p.911. The source consumer uses
r=s=2 and a cubic product in the marked SL3(2) parabolic.
-/

public section

namespace Representation

variable {k G W : Type*} [Field k] [Group G] [AddCommGroup W]
  [Module k W] [FiniteDimensional k W]

/-- Equality in the product displacement budget identifies the supplied
subspace with the common fixed space of both factors. -/
theorem fixed_of_product_displacement_budget
    (ρ : Representation k G W) (Y : Submodule k W) (a b : G) (r s : ℕ)
    (ha : Module.finrank k (LinearMap.range (ρ a - LinearMap.id)) ≤ r)
    (hb : Module.finrank k (LinearMap.range (ρ b - LinearMap.id)) ≤ s)
    (hker : LinearMap.ker (ρ (a * b) - LinearMap.id) ≤ Y)
    (hcodim : r + s ≤ Module.finrank k (W ⧸ Y)) :
    Y ≤ LinearMap.ker (ρ a - LinearMap.id) ⊓
      LinearMap.ker (ρ b - LinearMap.id) := by
  let A := LinearMap.range (ρ a - LinearMap.id)
  let B := LinearMap.range (ρ b - LinearMap.id)
  let C := LinearMap.range (ρ (a * b) - LinearMap.id)
  have hC : C ≤ A ⊔ B := by
    rintro _ ⟨v, rfl⟩
    have he : ρ (a * b) v - v =
        (ρ a (ρ b v) - ρ b v) + (ρ b v - v) := by
      simp only [map_mul, Module.End.mul_apply]
      abel
    change ρ (a * b) v - v ∈ _
    rw [he]
    exact Submodule.add_mem _ (Submodule.mem_sup_left ⟨ρ b v, rfl⟩)
      (Submodule.mem_sup_right ⟨v, rfl⟩)
  have hmono := Submodule.finrank_mono hC
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq A B
  have hdim := (ρ (a * b) - LinearMap.id).finrank_range_add_finrank_ker
  have hYdim := Y.finrank_quotient_add_finrank
  have hkerdim := Submodule.finrank_mono hker
  have hY : LinearMap.ker (ρ (a * b) - LinearMap.id) = Y := by
    apply Submodule.eq_of_le_of_finrank_le hker
    change Module.finrank k A ≤ r at ha
    change Module.finrank k B ≤ s at hb
    change Module.finrank k C + _ = _ at hdim
    omega
  have hAB : Disjoint A B := by
    rw [disjoint_iff]
    apply Submodule.finrank_eq_zero.mp
    change Module.finrank k A ≤ r at ha
    change Module.finrank k B ≤ s at hb
    change Module.finrank k C + _ = _ at hdim
    omega
  intro v hv
  have hvfix : ρ (a * b) v = v := by
    have h := hY.symm.le hv
    exact sub_eq_zero.mp h
  have hvB : ρ b v = v := by
    apply sub_eq_zero.mp
    apply (Submodule.disjoint_def.mp hAB) (ρ b v - v)
    · refine ⟨-(ρ b v), ?_⟩
      change ρ a (-(ρ b v)) - -(ρ b v) = ρ b v - v
      rw [map_neg]
      have he : ρ a (ρ b v) = v := by
        simpa only [map_mul, Module.End.mul_apply] using hvfix
      rw [he]
      abel
    · exact ⟨v, rfl⟩
  have hvA : ρ a v = v := by
    simpa only [map_mul, Module.End.mul_apply, hvB] using hvfix
  exact ⟨sub_eq_zero.mpr hvA, sub_eq_zero.mpr hvB⟩

end Representation
