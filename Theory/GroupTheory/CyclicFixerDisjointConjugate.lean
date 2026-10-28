module
public import Theory.GroupAction.SubgroupConjugation
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Coset.Card
/-!
# A disjoint conjugate kernel in a cyclic preimage

If an element normalizes C and moves the kernel of C→D disjointly from
itself, the conjugate kernel embeds in D. When D is cyclic, the original
kernel is cyclic and its order divides |D|. The conjugating element may
lie outside C, as required by the original crossing in 2.5.15, p.559.
-/
public section
namespace Subgroup
variable {G A : Type*} [Group G] [Group A]

theorem cyclic_of_disjoint_conjugate_in_cyclic_preimage
    (C : Subgroup G) (f : C →* A) (D : Subgroup A) [IsCyclic D]
    (N : Subgroup G) (hker : f.ker = N.subgroupOf C) (hCD : ∀ c, f c ∈ D)
    (hNC : N ≤ C) (x : G) (hx : x ∈ normalizer (C : Set G))
    (hd : Disjoint N (N.conjBy x)) :
    IsCyclic N ∧ Nat.card N ∣ Nat.card D := by
  have hconjC : N.conjBy x ≤ C := by
    have hh := map_mono (f := (MulAut.conj x).toMonoidHom) hNC
    have he : C.map (MulAut.conj x).toMonoidHom = C := mem_normalizer_iff_map_conj_eq.mp hx
    rw [he] at hh
    exact hh
  let a : N.conjBy x →* D :=
    (f.comp (inclusion hconjC)).codRestrict D (fun n => hCD _)
  have hi : Function.Injective a := by
    apply (MonoidHom.ker_eq_bot_iff a).mp
    apply bot_unique
    intro n hn
    have hf : f (inclusion hconjC n) = 1 := congrArg Subtype.val (show a n = 1 from hn)
    have hnN : (n : G) ∈ N := by
      have hm : inclusion hconjC n ∈ f.ker := hf
      rw [hker] at hm
      exact hm
    have hone : (n : G) = 1 := (disjoint_def.mp hd) hnN n.property
    exact mem_bot.mpr (Subtype.ext hone)
  let e : N ≃* N.conjBy x := N.equivMapOfInjective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective
  have hic : IsCyclic (N.conjBy x) := isCyclic_of_injective a hi
  let := hic
  refine ⟨isCyclic_of_injective e.toMonoidHom e.injective,?_⟩
  have hh := card_dvd_of_injective a hi
  rwa [← Nat.card_congr e.toEquiv] at hh
end Subgroup
