module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Tactic.Group

/-!
# Involution fibers and the action on a normal subgroup

Transport conjugation on a normal subgroup through an explicit group
isomorphism. Its fixed subgroup is the original centralizer intersection.
If every cocycle for an involution action is a coboundary, the involutions
in that coset are conjugate by the normal subgroup. Self-centrality also
detects precisely when the transported action is inner.

These are the transport steps in the quaternion rotation-fiber argument of
Janko–Thompson, Math. Z. 113 (1970), §4, printed pp.391–392. The finite
quaternion automorphism calculations are separate from this general result.
-/

namespace Subgroup

variable {T H : Type*} [Group T] [Group H]

/-- Conjugation on a normal subgroup, expressed in a supplied model. -/
@[expose] public noncomputable def normalConjThrough (P : Subgroup T) [P.Normal]
    (e : P ≃* H) : T →* MulAut H :=
  (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal

public theorem normalConjThrough_apply (P : Subgroup T) [P.Normal]
    (e : P ≃* H) (g : T) (x : P) :
    normalConjThrough P e g (e x) = e (MulAut.conjNormal g x) := by
  simp [normalConjThrough, MulAut.congr_apply]

public theorem normalConjThrough_coe (P : Subgroup T) [P.Normal]
    (e : P ≃* H) (p : P) :
    normalConjThrough P e (p : T) = MulAut.conj (e p) := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [normalConjThrough_apply]
  simp only [MulAut.conjNormal_val, MulAut.conj_apply, map_mul, map_inv]

/-- In a self-centralizing normal subgroup, an outside element acts outerly. -/
public theorem normalConjThrough_not_inner (P : Subgroup T) [P.Normal]
    (e : P ≃* H) (hcentral : centralizer (P : Set T) ≤ P)
    (u : T) (hu : u ∉ P) :
    ¬ ∃ q : H, normalConjThrough P e u = MulAut.conj q := by
  rintro ⟨q, hq⟩
  let p := e.symm q
  have hact : MulAut.conjNormal u = MulAut.conj p := by
    apply MulEquiv.ext
    intro x
    apply e.injective
    have hh := DFunLike.congr_fun hq (e x)
    rw [normalConjThrough_apply] at hh
    simpa only [MulAut.conj_apply, map_mul, map_inv, p,
      MulEquiv.apply_symm_apply] using hh
  have hc : (p : T)⁻¹ * u ∈ centralizer (P : Set T) := by
    intro x hx
    have hh := congrArg (fun a : MulAut P => (a ⟨x, hx⟩ : T)) hact
    change u * x * u⁻¹ = (p : T) * x * (p : T)⁻¹ at hh
    have he := congrArg (fun y : T => (p : T)⁻¹ * y * u) hh
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using he.symm
  exact hu ((P.mul_mem_cancel_left (P.inv_mem p.property)).mp (hcentral hc))

/-- The model's fixed subgroup maps to the original centralizer intersection. -/
public theorem normalConjThrough_fixed_map (P : Subgroup T) [P.Normal]
    (e : P ≃* H) (u : T) :
    ((normalConjThrough P e u).toMonoidHom.eqLocus (MonoidHom.id H)).map
      (P.subtype.comp e.symm.toMonoidHom) = P ⊓ centralizer ({u} : Set T) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(e.symm x).property, mem_centralizer_singleton_iff.mpr ?_⟩
    change normalConjThrough P e u x = x at hx
    have hh : MulAut.conjNormal u (e.symm x) = e.symm x := by
      apply e.injective
      simpa only [← normalConjThrough_apply, MulEquiv.apply_symm_apply] using hx
    have hv := congrArg (fun a : P => (a : T)) hh
    change u * (e.symm x : T) * u⁻¹ = (e.symm x : T) at hv
    exact (mul_inv_eq_iff_eq_mul.mp hv).symm
  · rintro ⟨hy, hc⟩
    refine ⟨e ⟨y, hy⟩, ?_, ?_⟩
    · change normalConjThrough P e u (e ⟨y, hy⟩) = e ⟨y, hy⟩
      rw [normalConjThrough_apply]
      congr 1
      apply Subtype.ext
      change u * y * u⁻¹ = y
      rw [← mem_centralizer_singleton_iff.mp hc, mul_inv_cancel_right]
    · simp

/-- Elementary fixed subgroups and their order transport back to the ambient group. -/
public theorem normalConjThrough_fixed_elementary_card (P : Subgroup T) [P.Normal]
    (e : P ≃* H) (u : T) (n : ℕ)
    (helem : IsElementaryAbelian 2
      ((normalConjThrough P e u).toMonoidHom.eqLocus (MonoidHom.id H)))
    (hcard : Nat.card
      ((normalConjThrough P e u).toMonoidHom.eqLocus (MonoidHom.id H)) = n) :
    IsElementaryAbelian 2 (P ⊓ centralizer ({u} : Set T) : Subgroup T) ∧
      Nat.card (P ⊓ centralizer ({u} : Set T) : Subgroup T) = n := by
  let _ := helem
  have hinj : Function.Injective (P.subtype.comp e.symm.toMonoidHom) :=
    P.subtype_injective.comp e.symm.injective
  constructor
  · rw [← normalConjThrough_fixed_map P e u]
    exact IsElementaryAbelian.map _
  · rw [← normalConjThrough_fixed_map P e u, card_map_of_injective hinj]
    exact hcard

/-- Triviality of the involution cocycles gives conjugacy throughout its coset. -/
public theorem normalConjThrough_involution_orbit (P : Subgroup T) [P.Normal]
    (e : P ≃* H) (u : T) (hu : u ^ 2 = 1)
    (hcocycle : ∀ x : H, x * normalConjThrough P e u x = 1 →
      ∃ p : H, x = p * normalConjThrough P e u p⁻¹)
    (v : T) (hv : v ^ 2 = 1) (hcoset : v * u⁻¹ ∈ P) :
    ∃ p : P, (p : T) * u * (p : T)⁻¹ = v := by
  let x : P := ⟨v * u⁻¹, hcoset⟩
  have hx : x * MulAut.conjNormal u x = 1 := by
    apply Subtype.ext
    change (v * u⁻¹) * (u * (v * u⁻¹) * u⁻¹) = 1
    calc
      _ = v ^ 2 * (u ^ 2)⁻¹ := by simp only [pow_two]; group
      _ = 1 := by rw [hu, hv]; simp
  have hxe : e x * normalConjThrough P e u (e x) = 1 := by
    rw [normalConjThrough_apply, ← map_mul, hx, map_one]
  obtain ⟨p, hp⟩ := hcocycle (e x) hxe
  let q := e.symm p
  have hh : x = q * MulAut.conjNormal u q⁻¹ := by
    apply e.injective
    simpa only [map_mul, ← normalConjThrough_apply, map_inv, q,
      MulEquiv.apply_symm_apply] using hp
  have hh' := congrArg (fun a : P => (a : T)) hh
  change v * u⁻¹ = (q : T) * (u * (q : T)⁻¹ * u⁻¹) at hh'
  refine ⟨q, ?_⟩
  have he := congrArg (fun a : T => a * u) hh'
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using he.symm

end Subgroup
