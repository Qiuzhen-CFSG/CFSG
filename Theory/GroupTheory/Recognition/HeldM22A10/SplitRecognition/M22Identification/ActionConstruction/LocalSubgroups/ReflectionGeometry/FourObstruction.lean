module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.LocalSubgroups.DerivedNormalizer

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.L27Exclusion.IntersectionConstruction.LocalGeometry

/-!
# Excluding the four-by-A5 intermediate subgroup

An element of order five normalizing a group of order four centralizes it:
its permutation action has order dividing both 5 and 4!. Combining it with
an involution in the four-group then produces an element of order ten.

For an intermediate subgroup U of the actual derived F-normalizer, U ∩ F
is normal in U. If this intersection is E ∩ F, it has order four. The source
order spectrum therefore excludes a factor of five in |U|, and in particular
excludes the possible A5 quotient in Janko's intermediate-subgroup argument.
All normality used here is relative to U, not to the ambient simple group.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 8, Lemma 17, p.17;
DOI 10.1016/0021-8693(68)90002-1.
-/

open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

private theorem order_five_centralizes_four (V : Subgroup G) (hV : Nat.card V = 4)
    (x : G) (hxV : x ∈ normalizer (V : Set G)) (hx : orderOf x = 5) :
    ∀ v ∈ V, Commute x v := by
  classical
  let := Fintype.ofFinite V
  let N := normalizer (V : Set G)
  let f := MulAction.toPermHom N V
  let xN : N := ⟨x, hxV⟩
  have h5 : orderOf (f xN) ∣ 5 := by
    have hxN : orderOf xN = 5 := (orderOf_coe xN).symm.trans hx
    exact hxN ▸ orderOf_map_dvd f xN
  have h24 : orderOf (f xN) ∣ 24 := by
    have hc : Fintype.card V = 4 := by rwa [← Nat.card_eq_fintype_card]
    simpa only [Nat.card_eq_fintype_card, Fintype.card_perm, hc,
      show Nat.factorial 4 = 24 from rfl] using _root_.orderOf_dvd_natCard (f xN)
  have hf : f xN = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 5 24) h5 h24)
  intro v hv
  have he := congrArg (fun p : Equiv.Perm V => ((p ⟨v, hv⟩ : V) : G)) hf
  exact mul_inv_eq_iff_eq_mul.mp he

private theorem exists_order_ten_of_five_normalizes_four (V : Subgroup G) (hV : Nat.card V = 4)
    (x : G) (hxV : x ∈ normalizer (V : Set G)) (hx : orderOf x = 5) :
    ∃ g : G, orderOf g = 10 := by
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := V) 2 (by rw [hV]; decide)
  have hvG : orderOf (v : G) = 2 := (orderOf_coe v).trans hv
  refine ⟨x * (v : G), ?_⟩
  rw [(order_five_centralizes_four V hV x hxV hx v v.property).orderOf_mul_eq_mul_orderOf_of_coprime
    (by rw [hx, hvG]; decide), hx, hvG]
end Subgroup

namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

omit [Finite G] in
/-- The source intersection has order four, in the ambient group. -/
public theorem E_inf_F_card : Nat.card (CaseII.E D k ⊓ CaseII.F D k : Subgroup G) = 4 :=
  CaseII.l27_intersection_card D k

omit [Finite G] in
/-- F intersects each subgroup of X in a normal subgroup of that subgroup. -/
public theorem intermediate_F_normal (U : Subgroup G) (hUX : U ≤ X D k) :
    ((CaseII.F D k).subgroupOf U).Normal :=
  normal_subgroupOf_of_le_normalizer (hUX.trans (X_le_normalizer_F D k))

/-- The small-intersection branch cannot have order divisible by five.
This discharges the order-ten obstruction in Janko's A5-quotient case. -/
public theorem five_not_dvd_intermediate_card
    (horders : ∀ g : G, orderOf g ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 11} : Finset ℕ))
    (U : Subgroup G) (hUX : U ≤ X D k)
    (hUF : U ⊓ CaseII.F D k = CaseII.E D k ⊓ CaseII.F D k) :
    ¬ 5 ∣ Nat.card U := by
  intro h5
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := U) 5 h5
  have hxN : (x : G) ∈ normalizer
      ((CaseII.E D k ⊓ CaseII.F D k : Subgroup G) : Set G) := by
    rw [← hUF]
    exact inf_normalizer_le_normalizer_inf
      ⟨U.le_normalizer x.property, X_le_normalizer_F D k (hUX x.property)⟩
  obtain ⟨g, hg⟩ := Subgroup.exists_order_ten_of_five_normalizes_four
    (CaseII.E D k ⊓ CaseII.F D k) (E_inf_F_card D k) x hxN
    ((orderOf_coe x).trans hx)
  have h := horders g
  rw [hg] at h
  norm_num at h

/-- No surjection onto the actual A5 exists in the small-intersection branch. -/
public theorem intermediate_not_A5_image
    (horders : ∀ g : G, orderOf g ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 11} : Finset ℕ))
    (U : Subgroup G) (hUX : U ≤ X D k)
    (hUF : U ⊓ CaseII.F D k = CaseII.E D k ⊓ CaseII.F D k)
    (f : U →* alternatingGroup (Fin 5)) : ¬ Function.Surjective f := by
  intro hf
  apply five_not_dvd_intermediate_card D k horders U hUX hUF
  apply dvd_trans (b := Nat.card (alternatingGroup (Fin 5)))
  · rw [nat_card_alternatingGroup]
    norm_num
  · exact card_dvd_of_surjective f hf

/-- In particular the literal quotient by F ∩ U cannot be A5. The supplied
normality instance is relative to U and is produced by `intermediate_F_normal`. -/
public theorem intermediate_not_A5_quotient
    (horders : ∀ g : G, orderOf g ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 11} : Finset ℕ))
    (U : Subgroup G) (hUX : U ≤ X D k)
    (hUF : U ⊓ CaseII.F D k = CaseII.E D k ⊓ CaseII.F D k)
    [((CaseII.F D k).subgroupOf U).Normal] :
    ¬ Nonempty (U ⧸ (CaseII.F D k).subgroupOf U ≃* alternatingGroup (Fin 5)) := by
  rintro ⟨e⟩
  exact intermediate_not_A5_image D k horders U hUX hUF
    (e.toMonoidHom.comp (QuotientGroup.mk' _))
    (e.surjective.comp (QuotientGroup.mk'_surjective _))

end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups
