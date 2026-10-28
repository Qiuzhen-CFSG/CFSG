module

public import Theory.GroupTheory.PResidual.NormalSubgroup.SimpleQuotient
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.PCoreSurjective
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Images and odd normal subgroups of two-perfect cubic extensions

A nontrivial two-core image of a two-perfect group with cubic two-core
quotient still has cubic two-core quotient. In such a group with nontrivial
two-core, every normal odd-order subgroup is trivial: a nontrivial normal
odd subgroup is two-perfect and fills the simple cubic quotient, forcing
it to be the whole group.

These statements preserve actual homomorphisms and their kernels. They
supply the faithful small-linear action in Aschbacher–Smith 13.3.14(d),
printed p.892.
-/

public section
open Subgroup

namespace MonoidHom
variable {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]

omit [Finite A] [Finite B] in
theorem twoCore_quotient_card_three
    (f : A →* B) (hf : Function.Surjective f)
    (hA : IsPPerfect 2 A) (hthree : Nat.card (A ⧸ pCore 2 A) = 3)
    (hm : (pCore 2 A).map f ≠ ⊥) :
    Nat.card (B ⧸ pCore 2 B) = 3 := by
  have hn : ((pCore 2 A).map f).Normal := Normal.map inferInstance f hf
  have hle : (pCore 2 A).map f ≤ pCore 2 B := le_sSup ⟨hn, pCore_isPGroup.map f⟩
  let q : (A ⧸ pCore 2 A) →* B ⧸ pCore 2 B :=
    QuotientGroup.map _ _ f (map_le_iff_le_comap.mp hle)
  have hq : Function.Surjective q := by
    intro b
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective _ b
    obtain ⟨a, rfl⟩ := hf b
    exact ⟨QuotientGroup.mk' _ a, rfl⟩
  have hc : Nat.card (B ⧸ pCore 2 B) ∣ 3 := hthree ▸ card_dvd_of_surjective q hq
  rcases (Nat.dvd_prime Nat.prime_three).mp hc with hc | hc
  · have ht : pCore 2 B = ⊤ := (index_eq_one).mp hc
    have hB : IsPGroup 2 B := by
      exact pCore_isPGroup.of_surjective
        ((MulEquiv.subgroupCongr ht).trans topEquiv).toMonoidHom
        ((MulEquiv.subgroupCongr ht).trans topEquiv).surjective
    have hz := hA.hom_eq_one_of_isPGroup hB f
    exact (hm (by rw [hz]; simp)).elim
  · exact hc

end MonoidHom

namespace Subgroup
variable {A : Type*} [Group A] [Finite A]

theorem normal_odd_eq_bot_of_twoPerfect_cubic
    (hA : IsPPerfect 2 A) (hthree : Nat.card (A ⧸ pCore 2 A) = 3)
    (hcore : pCore 2 A ≠ ⊥) (N : Subgroup A) [N.Normal]
    (hodd : Odd (Nat.card N)) : N = ⊥ := by
  by_contra hn
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : IsSimpleGroup (A ⧸ pCore 2 A) := isSimpleGroup_of_prime_card hthree
  have hN : IsPPerfect 2 N := by
    rw [← pResidual_eq_top_iff]
    apply top_unique
    intro n _
    exact mem_pResidual_of_orderOf_coprime
      (hodd.coprime_two_left.of_dvd_right (_root_.orderOf_dvd_natCard n))
  have ht := eq_top_of_normal_isPPerfect_of_simple_quotient (pCore 2 A)
    pCore_isPGroup hA N hN hn
  have hd : Disjoint (pCore 2 A) N := by
    apply disjoint_of_coprime_natCard
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := A)).exists_card_eq
    rw [hn]
    exact hodd.coprime_two_left.pow_left n
  exact hcore (by simpa only [ht, disjoint_top] using hd)

end Subgroup
