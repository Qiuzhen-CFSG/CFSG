module

public import Theory.GroupTheory.Involution.Basic
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.GroupTheory.OddKernelInvolutionFibers
public import Theory.ElementaryAbelian.Join

/-!
# Product closure of involution sets through odd kernels

A surjective homomorphism with odd kernel preserves product closure for
conjugacy-invariant sets of involutions, where the products concern distinct
commuting elements. The commuting image involutions generate an elementary
abelian two-subgroup. A Sylow subgroup of its preimage lifts it isomorphically.
Involutions in the same fiber are conjugate by a kernel element, so these
commuting lifts belong to the original set.

The lifting and fiber conjugacy are proved in
`Theory.GroupTheory.CoprimeQuotientSubgroups` and
`Theory.GroupTheory.OddKernelInvolutionFibers`, respectively. This elementary
argument supplies the odd-kernel descent in the central-factor reduction of
Aschbacher--Smith, *The Classification of Quasithin Groups*, Theorem I.8.2,
printed pp. 429--430; no classification hypotheses are needed here.
-/

open BenderSuzuki.PFAppendixIII
open scoped IsMulCommutative

namespace Theory.GroupTheory

private theorem image_involution {A Q : Type*} [Group A] [Finite A] [Group Q]
    (f : A →* Q) (hker : Odd (Nat.card f.ker)) {a : A} (ha : IsInvolution a) :
    IsInvolution (f a) := by
  let := IsElementaryAbelian.zpowers_of_pow_eq_one ha.sq_eq_one
  have hinj := Subgroup.injective_comp_subtype_of_coprime_ker f hker.coprime_two_left
    (Subgroup.zpowers a) (IsElementaryAbelian.isPGroup 2 _)
  refine ⟨?_, by rw [← map_pow, ha.sq_eq_one, map_one]⟩
  intro h
  have he : (⟨a, Subgroup.mem_zpowers a⟩ : Subgroup.zpowers a) = 1 :=
    hinj (by simpa using h)
  exact ha.ne_one (congrArg Subtype.val he)

private theorem pair_elementary {Q : Type*} [Group Q] {a b : Q}
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : Commute a b) :
    IsElementaryAbelian 2 (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup Q) := by
  let := IsElementaryAbelian.zpowers_of_pow_eq_one ha
  let := IsElementaryAbelian.zpowers_of_pow_eq_one hb
  apply IsElementaryAbelian.sup_of_le_centralizer
  rintro _ ⟨n, rfl⟩ _ ⟨m, rfl⟩
  exact (hab.zpow_zpow m n).eq

/-- Product closure of a conjugacy-invariant involution set descends through a
surjective homomorphism with odd kernel. -/
public theorem image_product_closed_of_odd_kernel
    {A Q : Type*} [Group A] [Finite A] [Group Q] [Finite Q]
    (f : A →* Q) (hf : Function.Surjective f) (hker : Odd (Nat.card f.ker))
    (Z : Set A) (hInv : ∀ z ∈ Z, IsInvolution z)
    (hConj : ∀ g z, z ∈ Z → MulAut.conj g z ∈ Z)
    (hProd : ∀ a ∈ Z, ∀ b ∈ Z, Commute a b → a ≠ b → a * b ∈ Z) :
    ∀ a ∈ f '' Z, ∀ b ∈ f '' Z, Commute a b → a ≠ b → a * b ∈ f '' Z := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hcomm hne
  have hxinv := hInv x hx
  have hyinv := hInv y hy
  have hfx := image_involution f hker hxinv
  have hfy := image_involution f hker hyinv
  let D : Subgroup Q := Subgroup.zpowers (f x) ⊔ Subgroup.zpowers (f y)
  let : IsElementaryAbelian 2 D := pair_elementary hfx.sq_eq_one hfy.sq_eq_one hcomm
  obtain ⟨P, hP, hmap, _⟩ :=
    Subgroup.exists_elementaryAbelian_map_eq_of_surjective_coprime f hf
      hker.coprime_two_left D
  let := hP
  have hxD : f x ∈ D := (show Subgroup.zpowers (f x) ≤ D from le_sup_left) (Subgroup.mem_zpowers (f x))
  have hyD : f y ∈ D := (show Subgroup.zpowers (f y) ≤ D from le_sup_right) (Subgroup.mem_zpowers (f y))
  rw [← hmap] at hxD hyD
  obtain ⟨a, haP, hax⟩ := hxD
  obtain ⟨b, hbP, hby⟩ := hyD
  have hainv : IsInvolution a := ⟨fun h => hfx.ne_one (by rw [← hax, h, map_one]),
    elemPow_eq_one_of_isElementaryAbelian a haP⟩
  have hbinv : IsInvolution b := ⟨fun h => hfy.ne_one (by rw [← hby, h, map_one]),
    elemPow_eq_one_of_isElementaryAbelian b hbP⟩
  have hmem (z c : A) (hz : z ∈ Z) (hc : IsInvolution c) (he : f z = f c) : c ∈ Z := by
    obtain ⟨g, hg⟩ := Subgroup.involutions_same_image_conj_ker f hker.coprime_two_left
      (orderOf_eq_prime (hInv z hz).sq_eq_one (hInv z hz).ne_one)
      (orderOf_eq_prime hc.sq_eq_one hc.ne_one) he
    exact hg ▸ hConj (g : A) z hz
  have haZ := hmem x a hx hainv hax.symm
  have hbZ := hmem y b hy hbinv hby.symm
  have hab : Commute a b := setLike_mul_comm haP hbP
  have habne : a ≠ b := fun h => hne (hax.symm.trans ((congrArg f h).trans hby))
  exact ⟨a * b, hProd a haZ b hbZ hab habne, by rw [map_mul, hax, hby]⟩

end Theory.GroupTheory
