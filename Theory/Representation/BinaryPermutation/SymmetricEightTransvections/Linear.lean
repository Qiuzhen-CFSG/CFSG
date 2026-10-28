module

public import Mathlib.LinearAlgebra.Transvection.Basic
import Mathlib.Tactic

/-!
# Binary rank-one operator obstructions

A product of two binary transvections has cube or fourth power one. If two
nonidentity transvections and their product are transvections, the pair has
a common direction or a common form. A linear automorphism centralizing the
first transvection preserves both its direction and its form. Consequently
the second transvection commutes with its conjugate by that automorphism.

These facts apply in any binary vector space. They supply the intrinsic
involution obstruction needed for Aschbacher–Smith, *The Classification of
Quasithin Groups*, 13.8.25, printed p.960 (PDF p.977), without classifying the
module. The rank-one and product calculations adapt the private proofs in
`Theory.Representation.SixLetterTransvections`; the common-direction/form
argument adapts `BinaryLinear.OuterCyclic.RadicalOrientation.TransvectionSubgroups`.
-/

public section

namespace Representation.SymmetricEightTransvections.Linear
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem binary (x : ZMod 2) : x = 0 ∨ x = 1 := (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) x

/-- Every binary linear automorphism moving at most one dimension is a transvection
(including the identity, as in Mathlib’s convention). -/
theorem of_small_displacement [Module.Finite (ZMod 2) V] (e : V ≃ₗ[ZMod 2] V)
    (h : Module.finrank (ZMod 2) (LinearMap.range (e.toLinearMap - LinearMap.id)) ≤ 1) :
    e ∈ LinearEquiv.transvections (ZMod 2) V := by
  obtain ⟨f, v, he⟩ := LinearEquiv.mem_dilatransvections_iff_finrank.mpr h
  have hfv : f v = 0 := by
    rcases binary (f v) with hz | ho
    · exact hz
    have hev : e v = 0 := by
      change e.toLinearMap v = 0
      rw [he, LinearMap.transvection.apply, ho, one_smul, ZModModule.add_self]
    have hv := e.map_eq_zero_iff.mp hev
    rw [hv, map_zero] at ho
    exact (zero_ne_one ho).elim
  exact LinearEquiv.mem_transvections_iff.mpr ⟨f, v, hfv, by ext x; exact congrArg (fun l : V →ₗ[ZMod 2] V => l x) he⟩

/-- Products of binary transvections have order dividing three or four. -/
theorem product_cube_or_fourth (t u : V ≃ₗ[ZMod 2] V)
    (ht : t ∈ LinearEquiv.transvections (ZMod 2) V)
    (hu : u ∈ LinearEquiv.transvections (ZMod 2) V) :
    (t * u) ^ 3 = 1 ∨ (t * u) ^ 4 = 1 := by
  obtain ⟨f, v, hfv, rfl⟩ := LinearEquiv.mem_transvections_iff.mp ht
  obtain ⟨g, w, hgw, rfl⟩ := LinearEquiv.mem_transvections_iff.mp hu
  rcases binary (f w) with hfw | hfw <;> rcases binary (g v) with hgv | hgv
  · right; ext x
    simp [pow_succ, LinearMap.transvection.apply, hfv, hgw, hfw, hgv]
    match_scalars <;> simp [ZModModule.add_self]
  · right; ext x
    simp [pow_succ, LinearMap.transvection.apply, hfv, hgw, hfw, hgv]
    match_scalars <;> simp [ZModModule.add_self, add_comm, add_left_comm]
  · right; ext x
    simp [pow_succ, LinearMap.transvection.apply, hfv, hgw, hfw, hgv]
    match_scalars <;> simp [ZModModule.add_self, add_comm, add_left_comm]
  · left; ext x
    simp [pow_succ, LinearMap.transvection.apply, hfv, hgw, hfw, hgv]
    match_scalars <;> simp [ZModModule.add_self, add_comm, add_left_comm]

/-- Linear conjugation preserves transvections. -/
theorem conjugate (e t : V ≃ₗ[ZMod 2] V)
    (ht : t ∈ LinearEquiv.transvections (ZMod 2) V) :
    e * t * e⁻¹ ∈ LinearEquiv.transvections (ZMod 2) V := by
  obtain ⟨f, v, hfv, rfl⟩ := LinearEquiv.mem_transvections_iff.mp ht
  let g := f.comp e.symm.toLinearMap
  have hgv : g (e v) = 0 := by simpa [g] using hfv
  apply LinearEquiv.mem_transvections_iff.mpr
  refine ⟨g, e v, hgv, ?_⟩
  ext x
  simp [g, LinearMap.transvection.apply]

private theorem scalar_one {a : ZMod 2} (ha : a ≠ 0) : a = 1 :=
  (binary a).resolve_left ha

private theorem exists_value_one {f : V →ₗ[ZMod 2] ZMod 2} (hf : f ≠ 0) :
    ∃ x, f x = 1 := by
  have h : ∃ x, f x ≠ 0 := by
    by_contra! h
    exact hf (LinearMap.ext h)
  obtain ⟨x, hx⟩ := h
  exact ⟨x, scalar_one hx⟩

/-- Different nonzero binary forms can be separated by a vector. -/
private theorem exists_one_zero {f g : V →ₗ[ZMod 2] ZMod 2}
    (hf : f ≠ 0) (hfg : f ≠ g) : ∃ x, f x = 1 ∧ g x = 0 := by
  by_contra! h
  have h1 (x : V) (hx : f x = 1) : g x = 1 := scalar_one (h x hx)
  obtain ⟨y, hy⟩ := exists_value_one hf
  have hgy := h1 y hy
  apply hfg
  ext x
  rcases binary (f x) with hx | hx
  · rcases binary (g x) with hgx | hgx
    · exact hx.trans hgx.symm
    · have hsum := h1 (x + y) (by simp [hx, hy])
      simp only [map_add, hgx, hgy] at hsum
      exact False.elim (by revert hsum; decide)
  · exact hx.trans (h1 x hx).symm

/-- Two transvections whose product is trivial or a transvection share a direction
or a form. -/
private theorem transvection_pair {v w : V} {f g : V →ₗ[ZMod 2] ZMod 2}
    (hv : v ≠ 0) (hw : w ≠ 0) (hf : f ≠ 0) (hg : g ≠ 0)
    (hfv : f v = 0) (hgw : g w = 0)
    (hprod : LinearEquiv.transvection hfv * LinearEquiv.transvection hgw = 1 ∨
      (LinearEquiv.transvection hfv * LinearEquiv.transvection hgw) ∈ LinearEquiv.transvections (ZMod 2) V) :
    v = w ∨ f = g := by
  by_cases hfg : f = g
  · exact Or.inr hfg
  left
  obtain ⟨x, hfx, hgx⟩ := exists_one_zero hf hfg
  obtain ⟨y, hgy, hfy⟩ := exists_one_zero hg (Ne.symm hfg)
  have hx : (LinearEquiv.transvection hfv * LinearEquiv.transvection hgw) x = x + v := by
    change (x + g x • w) + f (x + g x • w) • v = x + v
    simp [hgx, hfx]
  have hy : (LinearEquiv.transvection hfv * LinearEquiv.transvection hgw) y =
      y + (w + f w • v) := by
    change (y + g y • w) + f (y + g y • w) • v = y + (w + f w • v)
    simp [hgy, hfy, add_assoc]
  rcases hprod with hprod | hprod
  · have hz : x + v = x := by simpa [hprod] using hx.symm
    exact False.elim (hv (add_eq_left.mp hz))
  · obtain ⟨k, u, hku, he⟩ := LinearEquiv.mem_transvections_iff.mp hprod
    have hx' : v = k x • u := by
      have h := hx
      rw [he] at h
      change x + k x • u = x + v at h
      exact (add_left_cancel h).symm
    have hkx : k x = 1 := by
      apply scalar_one
      intro hz
      exact hv (by simpa [hz] using hx')
    have hvu : v = u := by simpa [hkx] using hx'
    have hy' : w + f w • v = k y • v := by
      have h := hy
      rw [he] at h
      change y + k y • u = y + (w + f w • v) at h
      rw [← hvu] at h
      exact (add_left_cancel h).symm
    have hwv : w = (k y - f w) • v := by
      rw [sub_smul]
      exact eq_sub_iff_add_eq.mpr hy'
    rcases binary (k y - f w) with hz | ho
    · exact False.elim (hw (by simpa [hz] using hwv))
    · simpa [ho] using hwv.symm

private theorem centralizer_data {v : V} {f : V →ₗ[ZMod 2] ZMod 2}
    (hv : v ≠ 0) (hf : f ≠ 0) (hfv : f v = 0)
    (e : V ≃ₗ[ZMod 2] V) (he : Commute e (LinearEquiv.transvection hfv)) :
    e v = v ∧ ∀ x, f (e x) = f x := by
  have h (x : V) : f x • e v = f (e x) • v := by
    have hx := congrArg (fun t : V ≃ₗ[ZMod 2] V => t x) he.eq
    change e (x + f x • v) = e x + f (e x) • v at hx
    simpa only [map_add, map_smul, add_right_inj] using hx
  obtain ⟨x, hx⟩ := exists_value_one hf
  have hx' := h x
  rw [hx, one_smul] at hx'
  have hfx : f (e x) = 1 := by
    apply scalar_one
    intro hz
    have hev : e v = 0 := by simpa [hz] using hx'
    exact hv (e.map_eq_zero_iff.mp hev)
  have hev : e v = v := by simpa [hfx] using hx'
  refine ⟨hev, fun y => ?_⟩
  have hy := h y
  rw [hev] at hy
  exact (smul_left_injective (ZMod 2) hv hy).symm

/-- A transvection triple forces commuting conjugates under the centralizer
of its first member. -/
theorem commute_conjugate_of_triple (t u e : V ≃ₗ[ZMod 2] V)
    (ht : t ∈ LinearEquiv.transvections (ZMod 2) V)
    (hu : u ∈ LinearEquiv.transvections (ZMod 2) V)
    (htu : t * u ∈ LinearEquiv.transvections (ZMod 2) V)
    (ht1 : t ≠ 1) (hu1 : u ≠ 1) (het : Commute e t) :
    Commute u (e * u * e⁻¹) := by
  obtain ⟨f, v, hfv, rfl⟩ := LinearEquiv.mem_transvections_iff.mp ht
  obtain ⟨g, w, hgw, rfl⟩ := LinearEquiv.mem_transvections_iff.mp hu
  have hv : v ≠ 0 := by intro h; subst v; exact ht1 (by ext x; simp)
  have hf : f ≠ 0 := by intro h; subst f; exact ht1 (by ext x; simp)
  have hw : w ≠ 0 := by intro h; subst w; exact hu1 (by ext x; simp)
  have hg : g ≠ 0 := by intro h; subst g; exact hu1 (by ext x; simp)
  obtain ⟨hev, hef⟩ := centralizer_data hv hf hfv e het
  have hef' (x : V) : f (e.symm x) = f x := by
    simpa using (hef (e.symm x)).symm
  rcases transvection_pair hv hw hf hg hfv hgw (Or.inr htu) with hvw | hfg
  · subst w
    have heiv : e.symm v = v := by apply e.injective; simpa using hev.symm
    apply LinearEquiv.ext
    intro x
    simp [LinearMap.transvection.apply, hev, heiv, hgw]
    abel
  · subst g
    apply LinearEquiv.ext
    intro x
    simp [LinearMap.transvection.apply, hef, hef', hgw]
    abel

end Representation.SymmetricEightTransvections.Linear
