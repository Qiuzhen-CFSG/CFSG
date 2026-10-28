module

public import Theory.ElementaryAbelian.ExtraspecialCommutatorPairing
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms
public import Theory.GroupTheory.NormalCenterQuotient
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Invariant elementary images of an extraspecial group

If an ambient action has no fixed points on an extraspecial two-group modulo
its center, an invariant homomorphism from that group to an elementary abelian
two-group is trivial. A nonzero image admits a separating binary functional;
commutator duality represents this functional by an element fixed modulo the
center, giving a contradiction.

This is the commutator-duality step used to place the marked quaternion core
inside the two-residual in the solvable argument of Aschbacher--Smith E.2.17.
-/

public section
open Subgroup
open scoped IsMulCommutative commutatorElement

namespace Theory.GroupTheory
variable {G E : Type*} [Group G] [Group E] [IsElementaryAbelian 2 E]

theorem invariant_hom_eq_one_of_extraspecial_fixed_center
    (P : Subgroup G) [Finite P] [P.Normal] [IsExtraspecial 2 P]
    (hfix : ∀ r : P,
      (∀ g : G, (MulAut.conjNormal g : MulAut P) r * r⁻¹ ∈ center P) → r ∈ center P)
    (f : P →* E)
    (hf : ∀ (g : G) (p : P), f ((MulAut.conjNormal g : MulAut P) p) = f p) :
    f = 1 := by
  classical
  let : IsElementaryAbelian 2 (center P) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun z => by
      simpa only [IsExtraspecial.center_order_p 2 P] using (pow_card_eq_one' (x := z)) }
  have hcentral : (center P).map P.subtype ≤ center G :=
    central_of_normal_card_two _ (by
      rw [card_map_of_injective P.subtype_injective, IsExtraspecial.center_order_p 2 P])
  have hαz (g : G) (z : center P) : (MulAut.conjNormal g : MulAut P) z = z := by
    apply Subtype.ext
    change g * P.subtype z * g⁻¹ = P.subtype z
    rw [mem_center_iff.mp (hcentral (mem_map_of_mem P.subtype z.property)) g,
      mul_inv_cancel_right]
  obtain ⟨z,hz,_⟩ := (Nat.card_eq_two_iff' (1 : center P)).mp
    (IsExtraspecial.center_order_p 2 P)
  apply MonoidHom.ext
  intro p
  by_contra hp
  have hp0 : Additive.ofMul (f p) ≠ 0 := hp
  obtain ⟨ℓ,hℓ⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hp0
  let ψ : P →* center P := {
    toFun x := (ℓ (Additive.ofMul (f x)) • Additive.ofMul z).toMul
    map_one' := by simp
    map_mul' x y := by
      change (ℓ (Additive.ofMul (f (x*y))) • Additive.ofMul z).toMul = _
      rw [map_mul, ofMul_mul, map_add, add_smul, toMul_add] }
  have hψ (g : G) (x : P) : ψ ((MulAut.conjNormal g : MulAut P) x) = ψ x := by
    change (ℓ (Additive.ofMul (f ((MulAut.conjNormal g : MulAut P) x))) • Additive.ofMul z).toMul = _
    rw [hf]
    rfl
  have hk : center P ≤ ψ.ker := by
    exact (IsExtraspecial.commutator_eq_center (p := 2)).ge.trans
      (Abelianization.commutator_subset_ker ψ)
  obtain ⟨r,hr⟩ := extraspecial_two_commutator_represents_hom
    (QuotientGroup.lift (center P) ψ hk)
  change ∀ q : P, (ψ q : P) = ⁅r,q⁆ at hr
  have hrc : r ∈ center P := by
    apply hfix r
    intro g
    let α : MulAut P := MulAut.conjNormal g
    have he (x : P) : ⁅α r,x⁆ = ⁅r,x⁆ := by
      calc
        ⁅α r,x⁆ = α ⁅r,α.symm x⁆ := by rw [map_commutatorElement, α.apply_symm_apply]
        _ = α (ψ (α.symm x)) := congrArg α (hr _).symm
        _ = ψ (α.symm x) := hαz g _
        _ = ψ x := by
          have hh := hψ g (α.symm x)
          rw [show (MulAut.conjNormal g : MulAut P) (α.symm x) = x from α.apply_symm_apply x] at hh
          exact congrArg Subtype.val hh.symm
        _ = ⁅r,x⁆ := hr x
    have hconj : MulAut.conj (α r) = MulAut.conj r := by
      apply MulEquiv.ext
      intro x
      have hh := congrArg (fun y : P => y*x) (he x)
      simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one,
        MulAut.conj_apply] using hh
    have hh : MulAut.conj (α r * r⁻¹) = 1 := by
      rw [map_mul,map_inv,hconj,mul_inv_cancel]
    apply mem_center_iff.mpr
    intro x
    have hx := DFunLike.congr_fun hh x
    change (α r * r⁻¹) * x * (α r * r⁻¹)⁻¹ = x at hx
    exact (mul_inv_eq_iff_eq_mul.mp hx).symm
  have hψp : ψ p = 1 := by
    apply Subtype.ext
    rw [hr p]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hrc p).symm
  apply hz
  have hpz : ψ p = z := by
    change (ℓ (Additive.ofMul (f p)) • Additive.ofMul z).toMul = z
    rw [hℓ,one_smul]
    rfl
  exact hpz.symm.trans hψp
end Theory.GroupTheory
