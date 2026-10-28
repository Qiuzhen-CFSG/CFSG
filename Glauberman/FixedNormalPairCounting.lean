module
public import Glauberman.MaximumAbelianReplacement
public import Glauberman.ThompsonPair

/-!
# The counting stage of a fixed-normal-free pair

A subgroup isomorphism fixing no nontrivial normal subgroup supplies maximum
abelian witnesses outside the common intersection on both sides. Sharp
fixed-space lower bounds then force supplements and maximum abelian
replacements inside that intersection. This proves the equal maximum-order
families and the exact fixed-space indices of both members of the pair.

The lower bounds are the precise natural-module consequences in Niles4.3;
they do not assert an arbitrary action is natural. This pair formulation is
used again after restriction in the recursive construction4.4.

Source: Niles, *Pushing-up in finite groups* (1979), Lemma4.3, printedp44.
-/

public section
open Subgroup
namespace Glauberman
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem fixed_intersection_of_supplement {A Q S V : Subgroup G}
    (hgen : A ⊔ Q = S) (hV : V ≤ centralizer (Q : Set G)) :
    V ⊓ centralizer (S : Set G) = V ⊓ centralizer (A : Set G) := by
  apply le_antisymm
  · exact inf_le_inf_left V (centralizer_le (show A ≤ S from hgen ▸ le_sup_left))
  · apply le_inf inf_le_left
    rw [←hgen]
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp inf_le_right)
      (le_centralizer_iff.mp (inf_le_left.trans hV))

/-- The full counting conclusions on both sides of the source pair, including
existence of outside subgroups and the fixed-space indices of both members. -/
theorem fixed_normal_pair_counting (S T V : Subgroup G) (φ : S ≃* T)
    (hS : S ≠ ⊥)
    (hno : ∀ A : Subgroup S, A.Normal →
      (A.map φ.toMonoidHom).map T.subtype = A.map S.subtype → A = ⊥)
    (hSn : S ≤ normalizer (S ⊓ T : Set G))
    (hTn : T ≤ normalizer (S ⊓ T : Set G))
    (hVQ : V ≤ S ⊓ T) (hVc : IsMulCommutative V)
    (hcentral : V ≤ centralizer (S ⊓ T : Set G))
    (hlowerS : ∀ A, A ∈ thompsonAbelianSubgroups S → ¬ A ≤ S ⊓ T →
      (S ⊓ T).relIndex S ≤ (V ⊓ centralizer (A : Set G)).relIndex V)
    (hlowerT : ∀ A, A ∈ thompsonAbelianSubgroups T → ¬ A ≤ S ⊓ T →
      (S ⊓ T).relIndex T ≤ (V ⊓ centralizer (A : Set G)).relIndex V) :
    (∃ A, A ∈ thompsonAbelianSubgroups S ∧ ¬ A ≤ S ⊓ T) ∧
    (∃ A, A ∈ thompsonAbelianSubgroups T ∧ ¬ A ≤ S ⊓ T) ∧
    (∀ A, A ∈ thompsonAbelianSubgroups S → ¬ A ≤ S ⊓ T →
      A ⊔ (S ⊓ T) = S ∧
      A ⊓ (S ⊓ T) ⊔ V ∈ thompsonAbelianSubgroups (S ⊓ T)) ∧
    (∀ A, A ∈ thompsonAbelianSubgroups T → ¬ A ≤ S ⊓ T →
      A ⊔ (S ⊓ T) = T ∧
      A ⊓ (S ⊓ T) ⊔ V ∈ thompsonAbelianSubgroups (S ⊓ T)) ∧
    thompsonAbelianSubgroups (S ⊓ T) ⊆ thompsonAbelianSubgroups S ∧
    thompsonAbelianSubgroups (S ⊓ T) ⊆ thompsonAbelianSubgroups T ∧
    (V ⊓ centralizer (S : Set G)).relIndex V = (S ⊓ T).relIndex S ∧
    (V ⊓ centralizer (T : Set G)).relIndex V = (S ⊓ T).relIndex T := by
  obtain ⟨hAS,hAT⟩ := exists_maximum_abelian_outside_pair S T φ hS hno
  obtain ⟨A,hA,hAQ⟩ := hAS
  obtain ⟨B,hB,hBQ⟩ := hAT
  have hs := maximum_abelian_replacement_of_fixedIndex hA inf_le_left hVQ hVc hcentral
    hSn (hlowerS A hA hAQ)
  have ht := maximum_abelian_replacement_of_fixedIndex hB inf_le_right hVQ hVc hcentral
    hTn (hlowerT B hB hBQ)
  refine ⟨⟨A,hA,hAQ⟩,⟨B,hB,hBQ⟩,?_,?_,hs.2.2.2.2.2,ht.2.2.2.2.2,?_,?_⟩
  · intro C hC hCQ
    have hc := maximum_abelian_replacement_of_fixedIndex hC inf_le_left hVQ hVc hcentral
      hSn (hlowerS C hC hCQ)
    exact ⟨hc.1,hc.2.2.1⟩
  · intro C hC hCQ
    have hc := maximum_abelian_replacement_of_fixedIndex hC inf_le_right hVQ hVc hcentral
      hTn (hlowerT C hC hCQ)
    exact ⟨hc.1,hc.2.2.1⟩
  · rw [fixed_intersection_of_supplement hs.1 hcentral,
      centralizer_intersection_maximum_abelian hA (hVQ.trans inf_le_left)]
    exact hs.2.2.2.2.1
  · rw [fixed_intersection_of_supplement ht.1 hcentral,
      centralizer_intersection_maximum_abelian hB (hVQ.trans inf_le_right)]
    exact ht.2.2.2.2.1
end Glauberman
