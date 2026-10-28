module

public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Odd displacement under an involutory automorphism

In a simple perfect group whose elements have order two or odd order, every
nonidentity involutory automorphism has a nonidentity odd-order displacement.
Otherwise the involution's normal closure in its semidirect product is abelian;
component centralization then forces the automorphism to be trivial.

This supplies the group-theoretic displacement used in GLS2, Chapter G,
Theorem 26.24, after the binary PSL₂ recognition of Theorem 25.14.
-/

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Theory.GroupTheory

private theorem normalClosure_involution_commutative {G : Type*} [Group G]
    (a : G) (ha : a ^ 2 = 1)
    (h : ∀ g : G, (a * (g * a * g⁻¹)) ^ 2 = 1) :
    IsMulCommutative (normalClosure ({a} : Set G)) := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ha)
  have hc (g : G) : Commute a (g * a * g⁻¹) := by
    have hbi : (g * a * g⁻¹)⁻¹ = g * a * g⁻¹ := by simp [hai, mul_assoc]
    have hi : (a * (g * a * g⁻¹))⁻¹ = a * (g * a * g⁻¹) :=
      inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using h g)
    rw [mul_inv_rev, hai, hbi] at hi
    exact hi.symm
  have hpair (g k : G) : Commute (g * a * g⁻¹) (k * a * k⁻¹) := by
    have hh := (hc (g⁻¹ * k)).map (MulAut.conj g).toMonoidHom
    simpa [MulAut.conj_apply, mul_assoc] using hh
  apply isMulCommutative_closure
  intro x hx y hy
  obtain ⟨_, ha', gx⟩ := Group.mem_conjugatesOfSet_iff.mp hx
  obtain ⟨_, hb', gy⟩ := Group.mem_conjugatesOfSet_iff.mp hy
  obtain rfl := Set.mem_singleton_iff.mp ha'
  obtain rfl := Set.mem_singleton_iff.mp hb'
  obtain ⟨g,rfl⟩ := isConj_iff.mp gx
  obtain ⟨k,rfl⟩ := isConj_iff.mp gy
  exact (hpair g k).eq

public theorem exists_odd_displacement_of_involutory_automorphism {J : Type*} [Group J] [IsSimpleGroup J] [Group.IsPerfect J]
    (hs : ∀ x : J, orderOf x = 2 ∨ Odd (orderOf x)) (α : MulAut J) (hα : α ^ 2 = 1) (hne : α ≠ 1) :
    ∃ x : J, Odd (orderOf (α x * x⁻¹)) ∧ α x * x⁻¹ ≠ 1 := by
  by_contra! hn
  have hsq (x : J) : (α x * x⁻¹) ^ 2 = 1 := by
    rcases hs (α x * x⁻¹) with he | ho
    · rw [← he]; exact pow_orderOf_eq_one _
    · rw [hn x ho, one_pow]
  let A := zpowers α
  let φ : A →* MulAut J := A.subtype
  let S := SemidirectProduct J A φ
  let f : J →* S := SemidirectProduct.inl
  let j : A →* S := SemidirectProduct.inr
  let a : S := j ⟨α,mem_zpowers α⟩
  have ha : a ^ 2 = 1 := by
    change j (⟨α,mem_zpowers α⟩ : A) ^ 2 = 1
    rw [← map_pow]
    have hh : (⟨α,mem_zpowers α⟩ : A) ^ 2 = 1 := Subtype.ext hα
    rw [hh,map_one]
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ha)
  have haf (x : J) : a * f x * a⁻¹ = f (α x) :=
    by simpa [a, f, j, φ] using
      (SemidirectProduct.inl_aut (φ := φ) (⟨α,mem_zpowers α⟩ : A) x).symm
  have hconj (s : S) : s * a * s⁻¹ = f s.left * a * (f s.left)⁻¹ := by
    have hc : Commute (j s.right) a :=
      (Commute.all s.right (⟨α,mem_zpowers α⟩ : A)).map j
    have he : s = f s.left * j s.right :=
      (SemidirectProduct.inl_left_mul_inr_right s).symm
    conv_lhs => rw [he, mul_inv_rev]
    calc
      _ = f s.left * (j s.right * a) * (j s.right)⁻¹ * (f s.left)⁻¹ := by simp only [mul_assoc]
      _ = _ := by rw [hc.eq]; simp only [← mul_assoc, mul_inv_cancel_right]
  have hprod (s : S) : (a * (s * a * s⁻¹)) ^ 2 = 1 := by
    have hh : a * (s * a * s⁻¹) = f (α s.left * s.left⁻¹) := by
      rw [hconj, map_mul, map_inv]
      rw [← haf, hai]
      simp only [mul_assoc]
    rw [hh, ← map_pow, hsq, map_one]
  let C := normalClosure ({a} : Set S)
  let : IsMulCommutative C := normalClosure_involution_commutative a ha hprod
  let L := f.range
  have hz : center J = ⊥ := by
    rcases (inferInstance : (center J).Normal).eq_bot_or_eq_top with hh | hh
    · exact hh
    · exact (Group.IsPerfect.not_isMulCommutative J (center_eq_top_iff.mp hh)).elim
  let : IsQuasisimple J := {
    simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup }
  have hf : Function.Injective f := SemidirectProduct.inl_injective
  let e : J ≃* L := MonoidHom.ofInjective hf
  let : Nontrivial L := e.symm.surjective.nontrivial
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv e
  let : L.Normal := by
    change f.range.Normal
    rw [show f.range = (SemidirectProduct.rightHom : S →* A).ker from
      SemidirectProduct.range_inl_eq_ker_rightHom]
    infer_instance
  have hL : IsComponent S L := ⟨(inferInstance : L.Normal).isSubnormal,inferInstance⟩
  have hLC : ⁅L,C⁆ = ⊥ := by
    rcases hL.normal_dichotomy C with hh | hh
    · have hcomm : L ≤ centralizer (L : Set S) :=
        hh.trans ((le_centralizer C).trans (centralizer_le hh))
      exact (Group.IsPerfect.not_isMulCommutative L
        (le_centralizer_iff_isMulCommutative.mp hcomm)).elim
    · exact hh
  have haC : a ∈ C := subset_normalClosure (Set.mem_singleton a)
  apply hne
  ext x
  have hcomm := mem_centralizer_iff.mp ((commutator_eq_bot_iff_le_centralizer.mp hLC)
    (show f x ∈ L from ⟨x,rfl⟩)) a haC
  apply hf
  rw [← haf, hcomm, mul_assoc, mul_inv_cancel, mul_one]
  rfl
end Theory.GroupTheory
