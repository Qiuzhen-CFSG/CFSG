module
public import CFSG.Quasithin.Chapter14.Section06.MaximalOvergroups
public import CFSG.Quasithin.Chapter1.Section01

/-!
# Normal subgroups of the maximal outside family

A nonzero subgroup S of T ∩ I normalized by I is a two-subgroup, so its
normalizer belongs to the original local family. Maximal intersection with
T then keeps that normalizer in the same outside family and fixes its
intersection with T. This gives the normalizer control required by the
original C.5/C.6 pushing-up argument, for every intervening two-overgroup.

Source: Aschbacher–Smith, refs/quasithin.pdf, the assertions (a) and (b) in
the proof of 14.6.9, printed p.1025. The Sylow assertion of (a) is supplied
separately by 14.6.6(2); it is not needed for the pushing-up control here.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section06
variable {G : Type*} [Group G]

/-- The actual IStar normalizer-control input used in the small-block branch
of 14.6.9; all local-family membership is proved from the nonzero two-subgroup. -/
theorem source_lemma_14_6_9_normalizers
    (T : Sylow 2 G) (Tu M Mc I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G) Tu Mc M))
    (S : Subgroup G) (hne : S ≠ ⊥) (hS : S ≤ (T : Subgroup G) ⊓ I)
    (hn : I ≤ normalizer (S : Set G)) :
    normalizer (S : Set G) ∈ IStar (T : Subgroup G)
      (outsideOvergroups (Chapter1.H G) Tu Mc M) ∧
      (T : Subgroup G) ⊓ normalizer (S : Set G) = (T : Subgroup G) ⊓ I ∧
      (∀ r ∈ (T : Subgroup G), r ∉ (T : Subgroup G) ⊓ I →
        r ∉ normalizer (S : Set G)) ∧
      ∀ Λ : Subgroup G, (T : Subgroup G) ⊓ I ≤ Λ → Λ ≤ (T : Subgroup G) →
        Λ ⊓ normalizer (S : Set G) = (T : Subgroup G) ⊓ I := by
  have hlocal : normalizer (S : Set G) ∈ Chapter1.H G :=
    Chapter1.mem_H_of_isTwoLocal ⟨S,hne,T.isPGroup'.to_le (hS.trans inf_le_left),rfl⟩
  obtain ⟨hstar,heq⟩ := lemma14_6_5 hI hn hlocal
  refine ⟨hstar,heq,?_,?_⟩
  · intro r hr hrI hrN
    exact hrI (heq ▸ (show r ∈ (T : Subgroup G) ⊓ normalizer (S : Set G) from ⟨hr,hrN⟩))
  · intro Λ hRΛ hΛT
    apply le_antisymm
    · exact (inf_le_inf_right _ hΛT).trans_eq heq
    · exact le_inf hRΛ (inf_le_right.trans hn)

end CFSG.Quasithin.Chapter14.Section06
