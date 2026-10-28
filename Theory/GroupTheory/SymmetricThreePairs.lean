module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Perm.Fin

/-!
# Conjugate involution pairs generating S₃

The exact pair condition passes to an injectively embedded group and is
preserved by isomorphism and conjugacy. A non-two-group pair of involutions
then has product of order dividing three, by the actual S₃ multiplication.
These transport lemmas retain both generators and the conjugating element.

Source application: Aschbacher–Smith, 13.5.21(iv), printed pp.923–924.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory
variable {G H : Type*} [Group G] [Group H]

def SymmetricThreePairs (v : G) : Prop :=
  ∀ g : G, ¬ IsPGroup 2 (zpowers v ⊔ zpowers (MulAut.conj g v) : Subgroup G) →
    Nonempty ((zpowers v ⊔ zpowers (MulAut.conj g v) : Subgroup G) ≃*
      Equiv.Perm (Fin 3))

theorem SymmetricThreePairs.of_injective (f : H →* G) (hf : Function.Injective f)
    {v : H} (h : SymmetricThreePairs (f v)) : SymmetricThreePairs v := by
  intro g hnot
  let P : Subgroup H := zpowers v ⊔ zpowers (MulAut.conj g v)
  have he : P.map f = zpowers (f v) ⊔ zpowers (MulAut.conj (f g) (f v)) := by
    simp only [P, Subgroup.map_sup, MonoidHom.map_zpowers, MulAut.conj_apply, map_mul, map_inv]
  let e := (P.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr he)
  obtain ⟨j⟩ := h (f g) (fun hh => hnot (hh.of_equiv e.symm))
  exact ⟨e.trans j⟩

private theorem symmetric_three_involutions (a b : Equiv.Perm (Fin 3))
    (ha : a ≠ 1) (ha2 : a ^ 2 = 1) (hb : b ≠ 1) (hb2 : b ^ 2 = 1) :
    (a * b) ^ 3 = 1 := by
  revert a b
  decide +kernel

theorem SymmetricThreePairs.cube {v : G} (h : SymmetricThreePairs v)
    (hv : orderOf v = 2) (g : G)
    (hnot : ¬ IsPGroup 2 (zpowers v ⊔ zpowers (MulAut.conj g v) : Subgroup G)) :
    (v * MulAut.conj g v) ^ 3 = 1 := by
  let P : Subgroup G := zpowers v ⊔ zpowers (MulAut.conj g v)
  let a : P := ⟨v, (show zpowers v ≤ P from le_sup_left) (mem_zpowers v)⟩
  let b : P := ⟨MulAut.conj g v, (show zpowers (MulAut.conj g v) ≤ P from le_sup_right) (mem_zpowers _) ⟩
  obtain ⟨e⟩ := h g hnot
  have ha : orderOf (e a) = 2 := (e.orderOf_eq a).trans ((orderOf_injective P.subtype
    P.subtype_injective a).symm.trans hv)
  have hb : orderOf (e b) = 2 := (e.orderOf_eq b).trans ((orderOf_injective P.subtype
    P.subtype_injective b).symm.trans (((MulAut.conj g).orderOf_eq v).trans hv))
  have hh := symmetric_three_involutions (e a) (e b)
    (orderOf_eq_prime_iff.mp ha).2 (orderOf_eq_prime_iff.mp ha).1
    (orderOf_eq_prime_iff.mp hb).2 (orderOf_eq_prime_iff.mp hb).1
  have hp : (a * b) ^ 3 = 1 := e.injective (by simpa only [map_pow, map_mul, map_one] using hh)
  exact congrArg Subtype.val hp
end Theory.GroupTheory


namespace Theory.GroupTheory
open Subgroup
variable {G H : Type*} [Group G] [Group H]

/-- Transport the literal conjugate pairs by an actual group isomorphism. -/
theorem SymmetricThreePairs.map_equiv {v : G} (h : SymmetricThreePairs v)
    (e : G ≃* H) : SymmetricThreePairs (e v) := by
  apply SymmetricThreePairs.of_injective e.symm.toMonoidHom e.symm.injective
  simpa only [MulEquiv.coe_toMonoidHom, e.symm_apply_apply] using h

/-- Replacing the marked involution by a conjugate preserves the pair condition. -/
theorem SymmetricThreePairs.of_isConj {v w : G} (h : SymmetricThreePairs v)
    (hc : IsConj v w) : SymmetricThreePairs w := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hc
  exact hg ▸ h.map_equiv (MulAut.conj g)
end Theory.GroupTheory

