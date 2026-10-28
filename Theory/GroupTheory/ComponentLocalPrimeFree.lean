module

public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Orders of local subgroups in a component orbit

Let L be a component of a finite group, K ≤ L, and A a subgroup such that
N_A(L) normalizes K. The A-conjugates of K mutually normalize: conjugates in
the same component coincide, and distinct components commute. Their generated
subgroup therefore has no prime divisors absent from K. Adjoining A introduces
only primes dividing the order of A.

This supplies the order step for the Suzuki-side local overgroup in
Aschbacher–Smith 2.3.9(7), printed p.526. In particular, A need not normalize L.
The proof uses actual conjugate subgroups, relative normality in their join,
and the finite subgroup product-order formula.
-/

open Subgroup

namespace Theory.GroupTheory

variable {G : Type*} [Group G] [Finite G]

/-- A prime absent from two normalizing factors is absent from their join. -/
public theorem not_dvd_card_sup_of_normalizes {p : ℕ} (hp : p.Prime) (K A : Subgroup G)
    (hn : A ≤ normalizer (K : Set G))
    (hK : ¬ p ∣ Nat.card K) (hA : ¬ p ∣ Nat.card A) :
    ¬ p ∣ Nat.card (K ⊔ A : Subgroup G) := by
  intro hd
  have hm := dvd_mul_of_dvd_right hd (Nat.card (K ⊓ A : Subgroup G))
  rw [← card_mul_eq_card_inf_mul_card_sup_of_normalizes K A hn] at hm
  exact (hp.dvd_mul.mp hm).elim hK hA

/-- A finite family of mutually normalizing subgroups introduces no new primes. -/
public theorem not_dvd_card_iSup_of_normalizes {p : ℕ} (hp : p.Prime) {ι : Type*} [Finite ι]
    (K : ι → Subgroup G) (hn : ∀ i j, K i ≤ normalizer (K j : Set G))
    (hK : ∀ i, ¬ p ∣ Nat.card (K i)) : ¬ p ∣ Nat.card (⨆ i, K i : Subgroup G) := by
  classical
  let := Fintype.ofFinite ι
  have hs : ∀ s : Finset ι, ¬ p ∣ Nat.card (s.sup K : Subgroup G) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hp.not_dvd_one
    | @insert i s hi ih =>
      rw [Finset.sup_insert]
      exact not_dvd_card_sup_of_normalizes hp (K i) (s.sup K)
        (Finset.sup_le (fun j _ => hn j i)) (hK i) ih
  simpa only [Finset.sup_univ_eq_iSup] using hs Finset.univ

omit [Finite G] in
private theorem component_seed_normalized {L K A : Subgroup G}
    (hL : IsComponent G L) (hK : K ≤ L)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G)) (a : A) :
    K.map (MulAut.conj (a : G)).toMonoidHom ≤ normalizer (K : Set G) := by
  by_cases he : L.map (MulAut.conj (a : G)).toMonoidHom = L
  · have hn := hinv ⟨a.property, mem_normalizer_iff_map_conj_eq.mpr he⟩
    have heK : K.map (MulAut.conj (a : G)).toMonoidHom = K :=
      mem_normalizer_iff_map_conj_eq.mp hn
    rw [heK]
    exact K.le_normalizer
  · have hc := (hL.map_conj (a : G)).commutator_eq_bot_of_ne hL he
    apply le_trans _ (centralizer_le_normalizer (K : Set G))
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    exact (commutator_mono (map_mono hK) hK).trans hc.le

omit [Finite G] in
/-- A local subgroup invariant under the component stabilizer has mutually
normalizing conjugates, even when the acting subgroup permutes components. -/
public theorem IsComponent.local_conjugates_normalize {L K A : Subgroup G}
    (hL : IsComponent G L) (hK : K ≤ L)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G)) (a b : A) :
    K.map (MulAut.conj (b : G)).toMonoidHom ≤
      normalizer (K.map (MulAut.conj (a : G)).toMonoidHom : Set G) := by
  have hn := map_mono (f := (MulAut.conj (a : G)).toMonoidHom)
    (component_seed_normalized hL hK hinv (a⁻¹ * b))
  rw [map_equiv_normalizer_eq, map_map] at hn
  have he : (MulAut.conj (a : G)).toMonoidHom.comp
      (MulAut.conj ((a⁻¹ * b : A) : G)).toMonoidHom =
        (MulAut.conj (b : G)).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rwa [he] at hn

/-- Adjoining an acting subgroup preserves a missing prime for a local subgroup
of a component, provided only the component stabilizer normalizes the local subgroup. -/
public theorem IsComponent.not_dvd_card_local_adjoin {p : ℕ} (hp : p.Prime) {L K A : Subgroup G}
    (hL : IsComponent G L) (hK : K ≤ L)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G))
    (hcardK : ¬ p ∣ Nat.card K) (hcardA : ¬ p ∣ Nat.card A) :
    ¬ p ∣ Nat.card (K ⊔ A : Subgroup G) := by
  rw [← componentOrbit_sup K A]
  apply not_dvd_card_sup_of_normalizes hp (componentOrbit K A) A (le_normalizer_componentOrbit K A) _ hcardA
  apply not_dvd_card_iSup_of_normalizes hp
  · intro a b
    exact IsComponent.local_conjugates_normalize hL hK hinv b a
  · intro a
    rwa [card_map_of_injective (MulAut.conj (a : G)).injective]

end Theory.GroupTheory
