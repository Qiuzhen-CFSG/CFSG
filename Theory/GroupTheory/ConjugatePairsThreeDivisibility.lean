module

public import Theory.GroupTheory.BaerSuzukiLocal
public import Theory.GroupTheory.GeneralizedFitting.SimpleSocleStructure
public import Theory.GroupTheory.ComponentLocalPrimeFree

/-!
# A three-divisibility consequence of the conjugate-pair condition

Let L be a faithful nonabelian simple normal subgroup of a finite group,
and A a subgroup of order two. Suppose every pair of conjugates of A
that generates a non-two-group generates S₃. Then three divides |L|.

Work inside H = ⟨L,A⟩, retaining the literal conjugates in the original
group. The faithful simple normal subgroup makes O₂(H) trivial. If three
did not divide |L|, it would not divide |H| either, so the pair condition
would make every such pair inside H a two-group. Relative Baer–Suzuki
would place the nontrivial A in O₂(H), a contradiction. No containment
A ≤ L or classification of the outer automorphisms is needed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
A.1.2 and the conjugate-pair condition (iv) in 13.5.21, printed pp.923–924.
The application excludes the Suzuki row of Table B.4.5.
-/

public section
open Subgroup
namespace Theory.GroupTheory

/-- The S₃ conjugate-pair condition forces three into the simple socle.
The marked order-two subgroup need not lie in that socle. -/
theorem three_dvd_card_of_symmetricThree_pairs {G : Type*} [Group G] [Finite G]
    (L A : Subgroup G) [L.Normal] [IsSimpleGroup L] [Group.IsPerfect L]
    (hc : centralizer (L : Set G) = ⊥) (ha : Nat.card A = 2)
    (hpair : ∀ x : G, ¬ IsPGroup 2 (A ⊔ A.map (MulAut.conj x).toMonoidHom : Subgroup G) →
      Nonempty ((A ⊔ A.map (MulAut.conj x).toMonoidHom : Subgroup G) ≃* Equiv.Perm (Fin 3))) :
    3 ∣ Nat.card L := by
  classical
  by_contra hthree
  let H := L ⊔ A
  let D := L.subgroupOf H
  let e : D ≃* L := subgroupOfEquivOfLe (show L ≤ H from le_sup_left)
  let : IsSimpleGroup D := e.isSimpleGroup
  let : Group.IsPerfect D := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hcD : centralizer (D : Set H) = ⊥ := by
    apply bot_unique
    intro x hx
    have hxL : (x : G) ∈ centralizer (L : Set G) := by
      intro l hl
      exact congrArg Subtype.val (mem_centralizer_iff.mp hx ⟨l, (show L ≤ H from le_sup_left) hl⟩ hl)
    rw [hc, mem_bot] at hxL
    exact Subtype.ext hxL
  have hcore : pCore 2 H = ⊥ :=
    SimpleSocle.pCore_eq_bot (SimpleSocle.radical_eq_bot D hcD) 2
  have hH : ¬ 3 ∣ Nat.card H :=
    not_dvd_card_sup_of_normalizes Nat.prime_three L A
      (by rw [L.normalizer_eq_top]; exact le_top) hthree (by rw [ha]; decide)
  have hpairs (x : G) (hx : x ∈ H) :
      IsPGroup 2 (A ⊔ A.map (MulAut.conj x).toMonoidHom : Subgroup G) := by
    by_contra hn
    obtain ⟨f⟩ := hpair x hn
    have hle : A ⊔ A.map (MulAut.conj x).toMonoidHom ≤ H := by
      refine sup_le le_sup_right ?_
      rintro _ ⟨a, ha, rfl⟩
      exact H.mul_mem (H.mul_mem hx ((show A ≤ H from le_sup_right) ha)) (H.inv_mem hx)
    have hcard : Nat.card (A ⊔ A.map (MulAut.conj x).toMonoidHom : Subgroup G) = 6 := by
      rw [Nat.card_congr f.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
      decide
    apply hH
    exact (show 3 ∣ Nat.card (A ⊔ A.map (MulAut.conj x).toMonoidHom : Subgroup G) by
      rw [hcard]; decide).trans (card_dvd_of_le hle)
  have hA := le_pCoreIn_of_conjugate_sup_isPGroup H A le_sup_right
    (IsPGroup.of_card (n := 1) (by simpa using ha)) hpairs
  have hz : A = ⊥ := by
    apply bot_unique
    simpa only [pCoreIn, hcore, Subgroup.map_bot] using hA
  have haone : Nat.card A = 1 := Subgroup.card_eq_one.mpr hz
  omega

end Theory.GroupTheory
