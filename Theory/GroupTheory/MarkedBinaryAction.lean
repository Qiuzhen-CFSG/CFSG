module

public import Theory.LinearAlgebra.BinaryFivePointStabilizer.Basic
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Ambient conjugation in marked binary coordinates

A coordinate isomorphism onto a normal elementary abelian subgroup turns
ambient conjugation into linear automorphisms. A central marked element
forces the image into its vector stabilizer. The kernel is exactly the
centralizer, giving the faithful quotient action used in Aschbacher--Smith
14.2.21, printed p.989. Both the map and its conjugation equation are constructed.
-/

public section

open Subgroup
open Theory.LinearAlgebra.BinaryFivePointStabilizer
noncomputable section
namespace Theory.GroupTheory.MarkedBinaryAction
variable {M V : Type*} [Group M] [AddCommGroup V] [Module (ZMod 2) V]
variable (E : Subgroup M) [E.Normal] (e : Multiplicative V ≃* E)

private def coordinates : M →* MulAut (Multiplicative V) :=
  (MulAut.congr e.symm).toMonoidHom.comp MulAut.conjNormal

private def additive (g : M) : V ≃+ V where
  toFun v := (coordinates E e g (Multiplicative.ofAdd v)).toAdd
  invFun v := ((coordinates E e g).symm (Multiplicative.ofAdd v)).toAdd
  left_inv v := (coordinates E e g).symm_apply_apply v
  right_inv v := (coordinates E e g).apply_symm_apply v
  map_add' v w := (coordinates E e g).map_mul v w

/-- Conjugation expressed in the supplied binary coordinates. -/
def linear : M →* (V ≃ₗ[ZMod 2] V) where
  toFun g := (additive E e g).toLinearEquiv (ZMod.map_smul (additive E e g))
  map_one' := by
    ext v
    exact congrArg Multiplicative.toAdd
      (DFunLike.congr_fun (coordinates E e).map_one (Multiplicative.ofAdd v))
  map_mul' g h := by
    ext v
    exact congrArg Multiplicative.toAdd
      (DFunLike.congr_fun ((coordinates E e).map_mul g h) (Multiplicative.ofAdd v))

theorem conjugation (g : M) (v : V) :
    (e (Multiplicative.ofAdd (linear E e g v)) : M) =
      g * (e (Multiplicative.ofAdd v) : M) * g⁻¹ := by
  change (e (e.symm (MulAut.conjNormal g (e (Multiplicative.ofAdd v)))) : M) = _
  rw [e.apply_symm_apply]
  rfl

variable (z : V) (hz : (e (Multiplicative.ofAdd z) : M) ∈ center M)

include hz in
theorem fixes (g : M) : linear E e g z = z := by
  apply Multiplicative.ofAdd.injective
  apply e.injective
  apply Subtype.ext
  rw [conjugation, mem_center_iff.mp hz g, mul_inv_cancel_right]

/-- The ambient representation into the literal marked-vector stabilizer. -/
def representation : M →* stabilizer z :=
  (linear E e).codRestrict (stabilizer z) (fixes E e z hz)

theorem representation_conjugation (g : M) (v : V) :
    (e (Multiplicative.ofAdd ((representation E e z hz g).val v)) : M) =
      g * (e (Multiplicative.ofAdd v) : M) * g⁻¹ := conjugation E e g v

theorem representation_ker : (representation E e z hz).ker = centralizer (E : Set M) := by
  ext g
  rw [MonoidHom.mem_ker, mem_centralizer_iff]
  constructor
  · intro hg x hx
    obtain ⟨v, hv⟩ := e.surjective ⟨x,hx⟩
    have h := representation_conjugation E e z hz g v.toAdd
    rw [hg] at h
    change (e v : M) = g * (e v : M) * g⁻¹ at h
    rw [hv] at h
    exact (mul_inv_eq_iff_eq_mul.mp h.symm).symm
  · intro hg
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    apply Multiplicative.ofAdd.injective
    apply e.injective
    apply Subtype.ext
    rw [representation_conjugation, ← hg _ (e (Multiplicative.ofAdd v)).property,
      mul_inv_cancel_right]
    rfl

/-- Faithful conjugation of the quotient by the actual centralizer. -/
def faithful : M ⧸ centralizer (E : Set M) →* stabilizer z :=
  QuotientGroup.lift _ (representation E e z hz) (by rw [representation_ker])

theorem faithful_mk (g : M) :
    faithful E e z hz (QuotientGroup.mk' _ g) = representation E e z hz g := by rfl

theorem faithful_injective : Function.Injective (faithful E e z hz) :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr (representation_ker E e z hz).symm
end Theory.GroupTheory.MarkedBinaryAction
