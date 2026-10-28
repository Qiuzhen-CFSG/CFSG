module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.ExceptionalExclusion.LocalGeometry.Products
public import Theory.GroupTheory.AbelianOrderNormalizerControl

/-!
# Sylow control from the exceptional fixed-subgroup calculation

The split three-subgroup AX has order 81 and index four in N_G(A).
Its abelian subgroup A is uniquely determined by its order 27 as soon as
|C_A(X)|=3. Sylow conjugacy inside N_G(A), where A is normal, gives the
same uniqueness throughout N_G(A). The p-group normalizer condition then
puts every ambient three-overgroup of A inside N_G(A).

Together with the independent index-three normalization argument this
constructs the exact ExceptionalSylowControl contract. The fixed-subgroup
order remains an explicit earlier-source premise; it is not asserted here.
No OddCentralizerComplement is used, so this applies uniformly to A and
its actual conjugates.

Source: Bender, *Finite groups with large subgroups* (1974), proof of (4.1),
printed p.225, the sentence passing from N_G(A) to an ambient Sylow subgroup.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

/-- Fixed order three implies uniqueness in the full normalizer. -/
public theorem exceptional_local_unique_of_fixed_card (h : Janko1CentralizerData G)
    (A : Subgroup G) (e : ExceptionalOddNormalizer A)
    (V X : Subgroup G) (hV : Nat.card V = 4) (hX : Nat.card X = 3)
    (hXV : X ≤ normalizer (V : Set G))
    (hN : normalizer (A : Set G) = A ⊔ (V ⊔ X))
    (hfixed : Nat.card (A ⊓ centralizer (X : Set G) : Subgroup G) = 3)
    (B : Subgroup G) (hBN : B ≤ normalizer (A : Set G))
    (hBc : IsMulCommutative B) (hcard : Nat.card B = 27) : B = A := by
  let : IsElementaryAbelian 3 A := e.elementary
  let : IsMulCommutative B := hBc
  let N := normalizer (A : Set G)
  have hXA : X ≤ N := by
    change X ≤ normalizer (A : Set G)
    rw [hN]
    exact le_sup_of_le_right le_sup_right
  have hAX : Disjoint A X := (h.exceptional_complement_disjoint A V X e.card hV hXV hN).mono_right
    (show X ≤ V ⊔ X from le_sup_right)
  have hPN : A ⊔ X ≤ N := sup_le A.le_normalizer hXA
  have hPc : Nat.card (A ⊔ X : Subgroup G) = 81 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint A X hXA hAX, e.card, hX]
  let P₀ := (A ⊔ X).subgroupOf N
  have hP₀c : Nat.card P₀ = 81 :=
    (Nat.card_congr (subgroupOfEquivOfLe hPN).toEquiv).trans hPc
  have hP₀p : IsPGroup 3 P₀ := IsPGroup.of_card (n := 4) (by simpa using hP₀c)
  have hP₀i : P₀.index = 4 := by
    have hi := P₀.index_mul_card
    rw [hP₀c, h.exceptional_normalizer_card A e] at hi
    omega
  let P : Sylow 3 N := hP₀p.toSylow (by rw [hP₀i]; decide)
  have hAc : Nat.card (A.subgroupOf N) = 27 :=
    (Nat.card_congr (subgroupOfEquivOfLe A.le_normalizer).toEquiv).trans e.card
  have hu : ∀ D : Subgroup N, D ≤ (P : Subgroup N) →
      IsMulCommutative D → Nat.card D = Nat.card (A.subgroupOf N) →
        D = A.subgroupOf N := by
    intro D hDP hDc hDcard
    let : IsMulCommutative D := hDc
    have hD : D.map N.subtype ≤ A ⊔ X := by
      rintro w ⟨d, hd, rfl⟩
      exact hDP hd
    have he := eq_of_abelian_order27_in_cubic_extension A X e.card hX hXA hAX hfixed
      (D.map N.subtype) hD inferInstance
      ((card_map_of_injective N.subtype_injective).trans (hDcard.trans hAc))
    apply map_injective (f := N.subtype) N.subtype_injective
    rw [he, subgroupOf_map_subtype, inf_of_le_left A.le_normalizer]
  have hBp : IsPGroup 3 (B.subgroupOf N) :=
    (IsPGroup.of_card (p := 3) (n := 3) (by simpa using hcard)).comap_subtype
  have hBcard : Nat.card (B.subgroupOf N) = Nat.card (A.subgroupOf N) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hBN).toEquiv, hcard, hAc]
  have he := eq_of_abelian_card_of_unique_in_sylow (A.subgroupOf N) P hu
    (B.subgroupOf N) hBp inferInstance hBcard
  have hm := congrArg (fun D : Subgroup N => D.map N.subtype) he
  have hAN : A ≤ N := A.le_normalizer
  have hBN' : B ≤ N := hBN
  simpa only [subgroupOf_map_subtype, inf_of_le_left hBN',
    inf_of_le_left hAN] using hm

/-- The fixed-subgroup calculation suffices for both Sylow-control clauses. -/
public theorem exceptional_sylowControl_of_fixed_card (h : Janko1CentralizerData G)
    (A : Subgroup G) (e : ExceptionalOddNormalizer A)
    (V X : Subgroup G) (hV : Nat.card V = 4) (hX : Nat.card X = 3)
    (hXV : X ≤ normalizer (V : Set G))
    (hN : normalizer (A : Set G) = A ⊔ (V ⊔ X))
    (hfixed : Nat.card (A ⊓ centralizer (X : Set G) : Subgroup G) = 3) :
    ExceptionalSylowControl A := by
  let : IsElementaryAbelian 3 A := e.elementary
  refine ⟨?_, fun D hD hcard _ => h.exceptional_normalizes_order27 A e D hD hcard⟩
  intro S hAS B hBS hBc hcard
  apply eq_of_same_card_abelian_in_p_overgroup A ?_ (S : Subgroup G) S.isPGroup'
    hAS B hBS hBc (hcard.trans e.card.symm)
  intro D hDN hDc hDcard
  exact h.exceptional_local_unique_of_fixed_card A e V X hV hX hXV hN hfixed
    D hDN hDc (hDcard.trans e.card)
end CFSG.Quasithin.Janko1CentralizerData
