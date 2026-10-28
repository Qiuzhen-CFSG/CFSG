module

public import CFSG.Quasithin.Chapter2.Section01To03.Selection.Transport
/-!
# The two starred selections and Sylow transport

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 2.3.7(1–4), printed p.523. The numbered statements instantiate the
families with Chapter 1's actual `He`.

For the superscript star, retain a globally largest local-base witness
before maximizing the two-part. For the subscript star, maximize just
the two-part. In either case a suitable overgroup has the same two-part,
so the original Sylow subgroup remains Sylow there and in its intersection
with M. The conclusions of `lemma_2_3_7_2` and `lemma_2_3_7_3` each include
both implications of part (4), separately preserving the two stars.
Part (3) keeps the extra largest-base witness explicitly. For part (1),
all members of Γ have two-part at most half the order of T; the index-two
hypothesis attains that bound. Relative index is used with S ≤ T.
-/

public section
namespace CFSG.Quasithin.Chapter2
open Subgroup
variable {G : Type*} [Group G] [Finite G] {E : Set (Subgroup G)} {M H K U L : Subgroup G}

omit [Finite G] in
theorem gamma_mono (hH : H ∈ gamma E M) (hHK : H ≤ K) (hK : twoCore K ≠ ⊥) :
    K ∈ gamma E M := ⟨hK, hH.2.mono (localPairsIn_mono hHK)⟩

omit [Finite G] in
theorem gammaWithLargestBase_mono (hH : H ∈ gammaWithLargestBase E M)
    (hHK : H ≤ K) (hK : twoCore K ≠ ⊥) : K ∈ gammaWithLargestBase E M := by
  obtain ⟨P, hP, hmax⟩ := hH.2
  exact ⟨gamma_mono hH.1 hHK hK, P, localPairsIn_mono hHK hP, hmax⟩

omit [Finite G] in
theorem gammaStar_of_twoPart_le (hH : H ∈ gammaStar E M)
    (hK : K ∈ gammaWithLargestBase E M) (hc : twoPart H ≤ twoPart K) :
    K ∈ gammaStar E M ∧ twoPart K = twoPart H := by
  have he := le_antisymm (hH.2 K hK) hc
  exact ⟨⟨hK, fun L hL => (hH.2 L hL).trans he.ge⟩, he⟩

omit [Finite G] in
theorem gammaMax_of_twoPart_le (hH : H ∈ gammaMax E M)
    (hK : K ∈ gamma E M) (hc : twoPart H ≤ twoPart K) :
    K ∈ gammaMax E M ∧ twoPart K = twoPart H := by
  have he := le_antisymm (hH.2 K hK) hc
  exact ⟨⟨hK, fun L hL => (hH.2 L hL).trans he.ge⟩, he⟩

theorem gamma_sylow_transport (hK : K ∈ gamma E M) (S : Sylow 2 H)
    (hSK : (S : Subgroup H).map H.subtype ≤ K) (hc : twoPart K = twoPart H)
    (hSM : (S : Subgroup H).map H.subtype ≤ M) :
    (∃ R : Sylow 2 K, (R : Subgroup K).map K.subtype = (S : Subgroup H).map H.subtype) ∧
    (∃ R : Sylow 2 ↥(K ⊓ M), (R : Subgroup ↥(K ⊓ M)).map (K ⊓ M).subtype =
      (S : Subgroup H).map H.subtype) := by
  refine ⟨exists_sylow_of_card hSK ((sylow_image_card H S).trans hc.symm), ?_⟩
  apply exists_sylow_of_card (le_inf hSK hSM)
  exact (sylow_image_card H S).trans (hc.symm.trans (gamma_twoPart_inf hK))

theorem gammaZero_overgroup (hH : H ∈ gammaZero E M)
    (hHK : H ≤ K) (hKcore : twoCore K ≠ ⊥) :
    K ∈ gammaZero E M ∧ twoPart K = twoPart H ∧
      (H ∈ gammaStar E M → K ∈ gammaStar E M) ∧
      (H ∈ gammaMax E M → K ∈ gammaMax E M) := by
  have hHgam : H ∈ gamma E M := hH.elim (fun h => h.1.1) (fun h => h.1)
  have hKgam := gamma_mono hHgam hHK hKcore
  have hc := twoPart_mono hHK
  have hs : H ∈ gammaStar E M → K ∈ gammaStar E M ∧ twoPart K = twoPart H :=
    fun h => gammaStar_of_twoPart_le h (gammaWithLargestBase_mono h.1 hHK hKcore) hc
  have hm : H ∈ gammaMax E M → K ∈ gammaMax E M ∧ twoPart K = twoPart H :=
    fun h => gammaMax_of_twoPart_le h hKgam hc
  refine ⟨?_, ?_, fun h => (hs h).1, fun h => (hm h).1⟩
  · exact hH.elim (fun h => Or.inl (hs h).1) (fun h => Or.inr (hm h).1)
  · exact hH.elim (fun h => (hs h).2) (fun h => (hm h).2)

/-- Lemma 2.3.7(2) and (4): overgroups in H retain both starred conditions and the Sylow subgroup. -/
theorem lemma_2_3_7_2 (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hpair : (U, L) ∈ localPairsIn (Chapter1.He G) M H) (S : Sylow 2 H)
    (hUS : U ≤ (S : Subgroup H).map H.subtype)
    (hK : K ∈ Chapter1.HOver G (H : Set G)) :
    K ∈ gammaZero (Chapter1.He G) M ∧
    (∃ R : Sylow 2 K, (R : Subgroup K).map K.subtype = (S : Subgroup H).map H.subtype) ∧
    (∃ R : Sylow 2 ↥(K ⊓ M), (R : Subgroup ↥(K ⊓ M)).map (K ⊓ M).subtype =
      (S : Subgroup H).map H.subtype) ∧
    (H ∈ gammaStar (Chapter1.He G) M → K ∈ gammaStar (Chapter1.He G) M) ∧
    (H ∈ gammaMax (Chapter1.He G) M → K ∈ gammaMax (Chapter1.He G) M) := by
  have ht := gammaZero_overgroup hH hK.2 hK.1
  have hKg : K ∈ gamma (Chapter1.He G) M := ht.1.elim (fun h => h.1.1) (fun h => h.1)
  have hSM := (beta_mono hpair.1.1 hUS (S.isPGroup'.map H.subtype)).2.1
  have hs := gamma_sylow_transport hKg S ((map_subtype_le _).trans hK.2) ht.2.1 hSM
  exact ⟨ht.1, hs.1, hs.2, ht.2.2.1, ht.2.2.2⟩

/-- Lemma 2.3.7(3) and (4), retaining the extra globally largest-base witness in the superscript-star case. -/
theorem lemma_2_3_7_3 (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hpair : (U, L) ∈ localPairsIn (Chapter1.He G) M H) (S : Sylow 2 H)
    (hUS : U ≤ (S : Subgroup H).map H.subtype)
    (hK : K ∈ gamma (Chapter1.He G) M) (hSK : (S : Subgroup H).map H.subtype ≤ K)
    (hlargest : H ∈ gammaStar (Chapter1.He G) M →
      (∀ V ∈ localBases (Chapter1.He G) M, Nat.card V ≤ Nat.card U) ∧
      ∃ L₁, (U, L₁) ∈ localPairsIn (Chapter1.He G) M K) :
    K ∈ gammaZero (Chapter1.He G) M ∧
    (∃ R : Sylow 2 K, (R : Subgroup K).map K.subtype = (S : Subgroup H).map H.subtype) ∧
    (∃ R : Sylow 2 ↥(K ⊓ M), (R : Subgroup ↥(K ⊓ M)).map (K ⊓ M).subtype =
      (S : Subgroup H).map H.subtype) ∧
    (H ∈ gammaStar (Chapter1.He G) M → K ∈ gammaStar (Chapter1.He G) M) ∧
    (H ∈ gammaMax (Chapter1.He G) M → K ∈ gammaMax (Chapter1.He G) M) := by
  have hSb := beta_mono hpair.1.1 hUS (S.isPGroup'.map H.subtype)
  have hc : twoPart H ≤ twoPart K := by
    rw [← sylow_image_card H S]
    exact beta_card_le_twoPart hSb hSK
  have hs : H ∈ gammaStar (Chapter1.He G) M → K ∈ gammaStar (Chapter1.He G) M ∧ twoPart K = twoPart H := by
    intro h
    obtain ⟨hmax, L₁, hL₁⟩ := hlargest h
    exact gammaStar_of_twoPart_le h ⟨hK, (U, L₁), hL₁, hmax⟩ hc
  have hm : H ∈ gammaMax (Chapter1.He G) M → K ∈ gammaMax (Chapter1.He G) M ∧ twoPart K = twoPart H :=
    fun h => gammaMax_of_twoPart_le h hK hc
  have hzero : K ∈ gammaZero (Chapter1.He G) M :=
    hH.elim (fun h => Or.inl (hs h).1) (fun h => Or.inr (hm h).1)
  have he : twoPart K = twoPart H := hH.elim (fun h => (hs h).2) (fun h => (hm h).2)
  have hSyl := gamma_sylow_transport hK S hSK he hSb.2.1
  exact ⟨hzero, hSyl.1, hSyl.2, fun h => (hs h).1, fun h => (hm h).1⟩

/-- Lemma 2.3.7(1): relative index two attains the maximum two-part in Γ. -/
theorem lemma_2_3_7_1 (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hH : H ∈ gamma (Chapter1.He G) M) (S : Sylow 2 H)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hindex : ((S : Subgroup H).map H.subtype).relIndex (T : Subgroup G) = 2) :
    H ∈ gammaMax (Chapter1.He G) M ∧ ∀ K ∈ gamma (Chapter1.He G) M,
      Nat.card ((S : Subgroup H).map H.subtype) ≤ twoPart K →
      twoPart K = Nat.card ((S : Subgroup H).map H.subtype) ∧ K ∈ gammaMax (Chapter1.He G) M := by
  let A := (S : Subgroup H).map H.subtype
  have hcard : Nat.card (T : Subgroup G) = 2 * twoPart H := by
    have hh := (A.subgroupOf (T : Subgroup G)).card_mul_index
    have he : Nat.card (A.subgroupOf (T : Subgroup G)) = Nat.card A :=
      Nat.card_congr (subgroupOfEquivOfLe hST).toEquiv
    change Nat.card (A.subgroupOf (T : Subgroup G)) * A.relIndex (T : Subgroup G) = _ at hh
    rw [he, hindex, sylow_image_card] at hh
    omega
  have hmax : H ∈ gammaMax (Chapter1.He G) M := by
    refine ⟨hH, ?_⟩
    intro K hK
    have hh := gamma_twoPart_double_le T hTM hunique hK
    rw [hcard] at hh
    omega
  refine ⟨hmax, ?_⟩
  intro K hK hc
  rw [sylow_image_card] at hc ⊢
  have ht := gammaMax_of_twoPart_le hmax hK hc
  exact ⟨ht.2, ht.1⟩
end CFSG.Quasithin.Chapter2
