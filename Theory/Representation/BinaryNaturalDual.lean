module

public import Mathlib.LinearAlgebra.QuadraticForm.Dual
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.CharP.Two
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.GroupTheory.IndexNormal

/-!
# Binary natural-plus-dual linear algebra

On `V × V*`, evaluation gives the hyperbolic quadratic form. Testing its polar
form against pure vectors proves nondegeneracy, and the contragredient formula
proves invariance under the natural linear group.

An involution exchanging complementary summands has fixed space equal to its
displacement image. The literal map `u ↦ u + s u` is a linear equivalence from
either summand to that fixed space and commutes with the centralizer of `s`.
The final group-action lemma records fixation of an orbit sum when the point
stabilizer has index two.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9.1(1),
H.9.2(1), H.9.3(2), printed pp.389–391. These are the underlying linear
calculations; they do not assert the remaining source classifications.
-/

@[expose] public section

namespace BinaryNaturalDual
open scoped CharTwo
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

abbrev Space (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] :=
  V × Module.Dual (ZMod 2) V

def quadratic : QuadraticForm (ZMod 2) (Space V) :=
  (QuadraticForm.dualProd (ZMod 2) V).comp
    (LinearEquiv.prodComm (ZMod 2) V (Module.Dual (ZMod 2) V)).toLinearMap

@[simp] theorem quadratic_apply (v : Space V) : quadratic v = v.2 v.1 := rfl

@[simp] theorem quadratic_natural (v : V) : quadratic (v, 0) = 0 := rfl

@[simp] theorem quadratic_dual (f : Module.Dual (ZMod 2) V) : quadratic (0, f) = 0 :=
  map_zero f

theorem polar_apply (v w : Space V) :
    quadratic.polarBilin v w = v.2 w.1 + w.2 v.1 := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, quadratic_apply,
    Prod.fst_add, Prod.snd_add, LinearMap.add_apply, map_add]
  ring

theorem polar_nondegenerate : (quadratic (V := V)).polarBilin.Nondegenerate := by
  have hleft : (quadratic (V := V)).polarBilin.SeparatingLeft := by
    intro v hv
    apply Prod.ext
    · apply (Module.forall_dual_apply_eq_zero_iff (ZMod 2) v.1).mp
      intro f
      simpa only [polar_apply, map_zero, zero_add] using hv (0, f)
    · apply LinearMap.ext
      intro x
      change v.2 x = 0
      simpa only [polar_apply, LinearMap.zero_apply, add_zero, zero_add] using hv (x, 0)
  exact ⟨hleft, fun v hv => hleft v (fun w => by
    simpa only [polar_apply, add_comm] using hv w)⟩

/-- The evaluation form is invariant under the natural and contragredient actions. -/
theorem quadratic_invariant (g : V ≃ₗ[ZMod 2] V) (v : Space V) :
    quadratic ((g.prodCongr g.symm.dualMap) v) = quadratic v := by
  change v.2 (g.symm (g v.1)) = v.2 v.1
  rw [g.symm_apply_apply]

/-- If a linear automorphism exchanges the summands and fixes their sum, it
exchanges the two components of that sum. -/
theorem swaps_components {U W : Submodule (ZMod 2) V} (hUW : IsCompl U W)
    (s : V ≃ₗ[ZMod 2] V) (hU : ∀ u ∈ U, s u ∈ W) (hW : ∀ w ∈ W, s w ∈ U)
    {u w : V} (hu : u ∈ U) (hw : w ∈ W) (hfix : s (u + w) = u + w) :
    s u = w ∧ s w = u := by
  have he : (Submodule.prodEquivOfIsCompl U W hUW)
      (⟨s w, hW w hw⟩, ⟨s u, hU u hu⟩) =
      (Submodule.prodEquivOfIsCompl U W hUW) (⟨u, hu⟩, ⟨w, hw⟩) := by
    change s w + s u = u + w
    rw [add_comm, ← map_add, hfix]
  have hh := (Submodule.prodEquivOfIsCompl U W hUW).injective he
  exact ⟨congrArg (fun p : U × W => (p.2 : V)) hh,
    congrArg (fun p : U × W => (p.1 : V)) hh⟩

/-- Fixed vectors for an involution interchanging two complementary summands
are exactly the diagonal vectors. -/
theorem fixed_iff_diagonal {U W : Submodule (ZMod 2) V} (hUW : IsCompl U W)
    (s : V ≃ₗ[ZMod 2] V) (hs : ∀ v, s (s v) = v)
    (hU : ∀ u ∈ U, s u ∈ W) (hW : ∀ w ∈ W, s w ∈ U) (v : V) :
    s v = v ↔ ∃ u : U, (u : V) + s u = v := by
  constructor
  · intro hv
    obtain ⟨u, w, hu, hw, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hUW.codisjoint v
    exact ⟨⟨u, hu⟩, by rw [(swaps_components hUW s hU hW hu hw hv).1]⟩
  · rintro ⟨u, rfl⟩
    rw [map_add, hs, add_comm]

private theorem binary_neg (v : V) : -v = v := by
  simpa only [CharTwo.neg_eq, one_smul] using (neg_smul (1 : ZMod 2) v).symm

/-- In characteristic two the fixed space of a swapping involution is its
actual displacement image. -/
theorem fixed_iff_displacement {U W : Submodule (ZMod 2) V} (hUW : IsCompl U W)
    (s : V ≃ₗ[ZMod 2] V) (hs : ∀ v, s (s v) = v)
    (hU : ∀ u ∈ U, s u ∈ W) (hW : ∀ w ∈ W, s w ∈ U) (v : V) :
    s v = v ↔ ∃ w : V, s w - w = v := by
  constructor
  · intro hv
    obtain ⟨u, rfl⟩ := (fixed_iff_diagonal hUW s hs hU hW v).mp hv
    exact ⟨u, by simp only [sub_eq_add_neg, binary_neg, add_comm]⟩
  · rintro ⟨w, rfl⟩
    rw [map_sub, hs]
    simp only [sub_eq_add_neg, binary_neg, add_comm]

/-- The fixed space of a linear operator, as an actual kernel. -/
def fixedSpace (s : V ≃ₗ[ZMod 2] V) : Submodule (ZMod 2) V :=
  LinearMap.ker (s.toLinearMap - LinearMap.id)

@[simp] theorem mem_fixedSpace (s : V ≃ₗ[ZMod 2] V) (v : V) :
    v ∈ fixedSpace s ↔ s v = v := by
  change s v - v = 0 ↔ s v = v
  exact sub_eq_zero

/-- The literal map in H.9.2(1) and H.9.3(2), with codomain the fixed space. -/
def diagonalMap (U : Submodule (ZMod 2) V) (s : V ≃ₗ[ZMod 2] V)
    (hs : ∀ v, s (s v) = v) : U →ₗ[ZMod 2] fixedSpace s :=
  (U.subtype + s.toLinearMap.comp U.subtype).codRestrict (fixedSpace s) (by
    intro u
    apply (mem_fixedSpace s _).mpr
    change s ((u : V) + s u) = (u : V) + s u
    rw [map_add, hs, add_comm])

@[simp] theorem diagonalMap_apply (U : Submodule (ZMod 2) V)
    (s : V ≃ₗ[ZMod 2] V) (hs : ∀ v, s (s v) = v) (u : U) :
    (diagonalMap U s hs u : V) = (u : V) + s u := rfl

/-- Complementary swapped summands identify either summand with the fixed space. -/
noncomputable def diagonalEquiv {U W : Submodule (ZMod 2) V} (hUW : IsCompl U W)
    (s : V ≃ₗ[ZMod 2] V) (hs : ∀ v, s (s v) = v)
    (hU : ∀ u ∈ U, s u ∈ W) (hW : ∀ w ∈ W, s w ∈ U) :
    U ≃ₗ[ZMod 2] fixedSpace s :=
  LinearEquiv.ofBijective (diagonalMap U s hs) ⟨by
    intro u u' he
    have hh : (Submodule.prodEquivOfIsCompl U W hUW)
        (u, ⟨s u, hU u u.property⟩) =
        (Submodule.prodEquivOfIsCompl U W hUW)
        (u', ⟨s u', hU u' u'.property⟩) := by
      change (u : V) + s u = (u' : V) + s u'
      exact congrArg (fun z : fixedSpace s => (z : V)) he
    exact congrArg Prod.fst ((Submodule.prodEquivOfIsCompl U W hUW).injective hh), by
    intro v
    obtain ⟨u, hu⟩ := (fixed_iff_diagonal hUW s hs hU hW v).mp
      ((mem_fixedSpace s v).mp v.property)
    exact ⟨u, Subtype.ext hu⟩⟩

@[simp] theorem diagonalEquiv_apply {U W : Submodule (ZMod 2) V} (hUW : IsCompl U W)
    (s : V ≃ₗ[ZMod 2] V) (hs : ∀ v, s (s v) = v)
    (hU : ∀ u ∈ U, s u ∈ W) (hW : ∀ w ∈ W, s w ∈ U) (u : U) :
    (diagonalEquiv hUW s hs hU hW u : V) = (u : V) + s u := rfl

/-- The map to fixed vectors commutes with every linear operator commuting with the swap. -/
theorem diagonal_equivariant (s g : V ≃ₗ[ZMod 2] V)
    (hcomm : Function.Commute g s) (v : V) :
    g (v + s v) = g v + s (g v) := by
  rw [map_add, hcomm v]

/-- The dimension of the fixed space is the dimension of one summand. -/
theorem finrank_fixedSpace {U W : Submodule (ZMod 2) V} (hUW : IsCompl U W)
    (s : V ≃ₗ[ZMod 2] V) (hs : ∀ v, s (s v) = v)
    (hU : ∀ u ∈ U, s u ∈ W) (hW : ∀ w ∈ W, s w ∈ U) :
    Module.finrank (ZMod 2) (fixedSpace s) = Module.finrank (ZMod 2) U :=
  (diagonalEquiv hUW s hs hU hW).finrank_eq.symm

/-- Equality with the actual commutator image, not just equality of dimensions. -/
theorem fixedSpace_eq_displacement {U W : Submodule (ZMod 2) V} (hUW : IsCompl U W)
    (s : V ≃ₗ[ZMod 2] V) (hs : ∀ v, s (s v) = v)
    (hU : ∀ u ∈ U, s u ∈ W) (hW : ∀ w ∈ W, s w ∈ U) :
    fixedSpace s = LinearMap.range (s.toLinearMap - LinearMap.id) := by
  ext v
  exact (mem_fixedSpace s v).trans (fixed_iff_displacement hUW s hs hU hW v)

variable {G : Type*} [Group G]

/-- The sum of the two vectors in an orbit of size two is fixed by the group. -/
theorem fixed_by_index_two_swap (ρ : G →* (V ≃ₗ[ZMod 2] V))
    (H : Subgroup G) (hindex : H.index = 2)
    {t : G} (ht : t ∉ H) {u w : V}
    (hu : ∀ h ∈ H, ρ h u = u) (hswap : ρ t u = w) :
    ∀ g : G, ρ g (u + w) = u + w := by
  let : H.Normal := H.normal_of_index_eq_two hindex
  have ht2 : t * t ∈ H := (Subgroup.mul_mem_iff_of_index_two hindex).mpr Iff.rfl
  have htw : ρ t w = u := by
    rw [← hswap, ← LinearEquiv.mul_apply, ← map_mul, hu _ ht2]
  have hfix : ρ t (u + w) = u + w := by rw [map_add, hswap, htw, add_comm]
  have hw : ∀ h ∈ H, ρ h w = w := by
    intro h hh
    have hc : t⁻¹ * h * t ∈ H := by
      simpa only [inv_inv] using (inferInstance : H.Normal).conj_mem h hh t⁻¹
    have he : ρ h (ρ t u) = ρ t (ρ (t⁻¹ * h * t) u) := by
      simp only [← LinearEquiv.mul_apply, ← map_mul]
      congr 2
      group
    rw [hu _ hc] at he
    simpa only [hswap] using he
  have hH : ∀ h ∈ H, ρ h (u + w) = u + w := by
    intro h hh
    rw [map_add, hu h hh, hw h hh]
  intro g
  by_cases hg : g ∈ H
  · exact hH g hg
  · have ht' : t⁻¹ ∉ H := by simpa only [H.inv_mem_iff] using ht
    have hm : g * t⁻¹ ∈ H :=
      (Subgroup.mul_mem_iff_of_index_two hindex).mpr (iff_of_false hg ht')
    have he : ρ g (u + w) = ρ (g * t⁻¹) (ρ t (u + w)) := by
      simp only [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel_right]
    rw [he, hfix, hH _ hm]

end BinaryNaturalDual
