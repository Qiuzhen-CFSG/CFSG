module

public import CFSG.Quasithin.Chapter14.Section06.SourceIntersectionParabolic
public import CFSG.Quasithin.Chapter14.Section06.SuitableInvolutionSylow
public import CFSG.Quasithin.Chapter14.Section06.SourceOrderBound

/-!
# The first parabolic core in the original rank-two argument

For the maximal-intersection choice I, put S = T ∩ I and
I₁ = O²(L ∩ I)S. The literal core identity from the first-parabolic
calculation makes N_T(S) normalize O₂(I₁). Every characteristic subgroup
of that core is therefore normalized by both I₁ and N_T(S). Since I₁
escapes M_c and N_T(S) properly contains S, maximality of the original
outside family forces each such characteristic normalizer into M.

The original numerical hypotheses give |S| > 2⁹, while the quotient of
I₁ by its two-core is S₃. Consequently its core is nontrivial. If the
second parabolic had the same core, their join I would normalize it and
lie in M, contradicting the choice of I. This proves 14.6.10(1–2), with
the preceding factorization from 14.6.9 kept explicit. The final theorem
discharges that factorization in the already proved escaping-intersection
branch of 14.6.6(3).

Source: Aschbacher–Smith, refs/quasithin.pdf, 14.6.10(1–2), printed p.1028.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section06
variable {G : Type*} [Group G] [Finite G]

private theorem characteristicNormalizer_le_of_maximal_intersection
    (T : Sylow 2 G) (Tu M Mc I P R : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G) Tu Mc M))
    (hTuT : Tu ≤ (T : Subgroup G))
    (hproper : (T : Subgroup G) ⊓ I < (T : Subgroup G))
    (hR : R ≤ (T : Subgroup G) ⊓ I)
    (hSP : (T : Subgroup G) ⊓ I ≤ P) (hPN : P ≤ normalizer (R : Set G))
    (hPMc : ¬ P ≤ Mc)
    (hTN : (T : Subgroup G) ⊓ normalizer ((T : Subgroup G) ⊓ I : Set G) ≤
      normalizer (R : Set G)) :
    R.characteristicNormalizerClosure ≤ M := by
  let S := (T : Subgroup G) ⊓ I
  have hTuS : Tu ≤ S := le_inf hTuT hI.1.2.1
  have hSproper : S.subgroupOf (T : Subgroup G) < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, subgroupOf_eq_top]
    exact hproper.not_ge
  let : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
  obtain ⟨t, ht, htS⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (S.subgroupOf (T : Subgroup G)) hSproper)
  have htN : (t : G) ∈ normalizer (S : Set G) := by
    rw [← subgroupOf_normalizer_eq (show S ≤ (T : Subgroup G) from inf_le_left)] at ht
    exact ht
  apply (characteristicNormalizerClosure_le_iff R M).mpr
  intro C hC hCne
  let := hC
  let W := C.map R.subtype
  have hWne : W ≠ ⊥ := fun hz => hCne
    ((map_eq_bot_iff_of_injective _ R.subtype_injective).mp hz)
  have hWp : IsPGroup 2 W :=
    ((T.isPGroup'.to_le (hR.trans inf_le_left)).to_subgroup C).map _
  have hRN : normalizer (R : Set G) ≤ normalizer (W : Set G) :=
    normalizer_le_normalizer_characteristic_image R C
  have hPNW := hPN.trans hRN
  by_contra hnot
  have hNW : normalizer (W : Set G) ∈ outsideOvergroups (Chapter1.H G) Tu Mc M :=
    ⟨Chapter1.mem_H_of_isTwoLocal ⟨W, hWne, hWp, rfl⟩,
      (hTuS.trans hSP).trans hPNW, fun hc => hPMc (hPNW.trans hc), hnot⟩
  have hbound : (T : Subgroup G) ⊓ normalizer (W : Set G) ≤ S :=
    hI.2 hNW (le_inf inf_le_left (hSP.trans hPNW))
  exact htS (hbound ⟨t.property, hRN (hTN ⟨t.property, htN⟩)⟩)

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (hindex : (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u).relIndex
        (T : Subgroup G) = 2)
    (hmove : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G))
    (hU3 : Mc ⊓ normalizer (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u : Set G) =
        (T : Subgroup G))
    (hlocal : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
      (H ⊓ centralizer ({u} : Set G)))

include hG hempty hM hunique hmany hcard e hab H hH hu hindex hmove hproduct hU3 hlocal

/-- The original suitability hypotheses supply both the ambient Sylow
intersection and its properness; neither is retained as an extra premise. -/
theorem source_suitable_intersection_sylow
    (I : Subgroup G)
    (hI : I ∈ outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M) :
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ I) I ∧
      (T : Subgroup G) ⊓ I < (T : Subgroup G) := by
  let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  let Tu := (T : Subgroup G) ⊓ centralizer ({u} : Set G)
  let T0 := suitableQuotientCentralizer h u
  have hi := source_lemma_14_6_3_1 hG T hempty hM hunique hmany hcard e hab H hH
    u hu hindex hmove hproduct
  have hn := source_lemma_14_6_3_4 hG T hempty hM hunique hmany hcard e hab H hH
    u hu hindex hmove hproduct hU3 hlocal
  have hQH : H.pCoreIn 2 ≤ T0 := by
    change H.pCoreIn 2 ≤ suitableQuotientCentralizer h u
    rw [hi.2.2.2.1]
    exact le_sup_left
  have hN0 := source_lemma_14_6_3_2 hG T hempty hM hunique hmany hcard e hab H hH
    T0 hQH inf_le_left hindex hU3
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,hpair⟩ :=
    source_lemma_14_1_18 hG T hempty hM hunique hmany hcard e
  obtain ⟨hcases,hSyl,_⟩ := suitable_involution_intersection_sylow
    T Tu T0 M Mc I hi.1 hindex hn.1 hN0 hpair hI
  refine ⟨hSyl, lt_of_le_of_ne inf_le_left ?_⟩
  intro he
  rcases hcases with hcase | hcase
  · have hc : Tu.relIndex (T : Subgroup G) = 4 := hi.2.1
    rw [←hcase, he, relIndex_self] at hc
    omega
  · have hc : T0.relIndex (T : Subgroup G) = 2 := hindex
    rw [←hcase, he, relIndex_self] at hc
    omega

set_option maxHeartbeats 800000
/-- Original 14.6.10(1–2), on the literal first parabolic and its core.
The only earlier 14.6.9 conclusion retained is its factorization of L. -/
theorem source_lemma_14_6_10_1_2
    (I I2 : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (hcoreIndex : 4 < (H.pCoreIn 2).relIndex (T : Subgroup G))
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H)))
    (hcover : (sourceResidual M Mc : Set G) =
      ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
        (sourceResidual M Mc ⊓ I).subtype : Set G) *
          ((sourceResidual M Mc).pCoreIn 2 : Set G))
    (hgen : ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)) ⊔ I2 = I) :
    let I1 := (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)
    (I1.pCoreIn 2).characteristicNormalizerClosure ≤ M ∧
      I1.pCoreIn 2 ≠ ⊥ ∧ I1.pCoreIn 2 ≠ I2.pCoreIn 2 := by
  let L := sourceResidual M Mc
  let LI := (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype
  let S := (T : Subgroup G) ⊓ I
  let I1 := LI ⊔ S
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let R := I1.pCoreIn 2
  change R.characteristicNormalizerClosure ≤ M ∧ R ≠ ⊥ ∧ R ≠ I2.pCoreIn 2
  change I1 ⊔ I2 = I at hgen
  obtain ⟨hSyl,hproper⟩ := source_suitable_intersection_sylow hG T hempty hM hunique
    hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I hI.1
  obtain ⟨⟨eI⟩,_,hR,hLI⟩ := source_intersection_parabolic_data hG T hempty hM hunique
    hmany hcard e hab H hH u hu hindex hmove hproduct I hI.1.2.1 hSyl hcover
  change R = S ⊓ Q at hR
  change ¬ LI ≤ Mc at hLI
  change (I1 ⧸ pCore 2 I1) ≃* Equiv.Perm (Fin 3) at eI
  have hI1N : I1 ≤ normalizer (R : Set G) := I1.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image I1 (pCore 2 I1))
  have hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G) :=
    (le_sup_right : (T : Subgroup G) ≤ L ⊔ (T : Subgroup G)).trans
      ((L ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))))
  have hcontrol : R.characteristicNormalizerClosure ≤ M := by
    apply characteristicNormalizer_le_of_maximal_intersection T _ M Mc I I1 R hI inf_le_left
      hproper (hR.le.trans inf_le_left) le_sup_right hI1N
      (fun hh => hLI (le_sup_left.trans hh))
    rw [hR]
    exact (le_inf inf_le_right (inf_le_left.trans hTQ)).trans
      (inf_normalizer_le_normalizer_inf (H := S) (K := Q))
  have hTcard := (source_lemma_14_6_9_order hG T hempty hM hunique hmany hcard e hab H hH
    hcoreIndex hrank).2
  have hSlarge : 2 ^ 9 < Nat.card S := by
    let Tu := (T : Subgroup G) ⊓ centralizer ({u} : Set G)
    have hi := source_lemma_14_6_3_1 hG T hempty hM hunique hmany hcard e hab H hH
      u hu hindex hmove hproduct
    have hTuIndex : Tu.relIndex (T : Subgroup G) = 4 := hi.2.1
    have hc : Nat.card Tu * 4 = Nat.card T := by
      simpa only [relIndex_bot_left, hTuIndex] using
        relIndex_mul_relIndex (⊥ : Subgroup G) Tu (T : Subgroup G) bot_le inf_le_left
    have hTuS : Tu ≤ S := le_inf inf_le_left hI.1.2.1
    have hle : Nat.card Tu ≤ Nat.card S :=
      Nat.card_le_card_of_injective (Subgroup.inclusion hTuS)
        (Subgroup.inclusion_injective _)
    norm_num at hTcard ⊢
    omega
  have hRne : R ≠ ⊥ := by
    intro hz
    have hz' : pCore 2 I1 = ⊥ :=
      (map_eq_bot_iff_of_injective _ I1.subtype_injective).mp hz
    have hcI : Nat.card I1 = 6 := by
      have hh := Nat.card_congr eI.toEquiv
      change Nat.card (I1 ⧸ pCore 2 I1) = Nat.card (Equiv.Perm (Fin 3)) at hh
      rw [hz', Nat.card_congr QuotientGroup.quotientBot.toEquiv] at hh
      simpa [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] using hh
    have hSI : S ≤ I1 := le_sup_right
    have hle : Nat.card S ≤ Nat.card I1 :=
      Nat.card_le_card_of_injective (Subgroup.inclusion hSI)
        (Subgroup.inclusion_injective _)
    rw [hcI] at hle
    norm_num at hSlarge
    omega
  refine ⟨hcontrol,hRne,?_⟩
  intro he
  have hI2N : I2 ≤ normalizer (R : Set G) := by
    rw [he]
    exact I2.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image I2 (pCore 2 I2))
  have hIN : I ≤ normalizer (R : Set G) := hgen ▸ sup_le hI1N hI2N
  exact hI.1.2.2.2 (hIN.trans
    ((normalizer_le_characteristicNormalizerClosure_self R hRne).trans hcontrol))

end CFSG.Quasithin.Chapter14.Section06
