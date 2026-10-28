module

public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicCore
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# Rechoosing the generated group in 14.6.6(6)

Put S = T ∩ I, A = O²(L ∩ I), and I₂ = O²(H₂)S.  The source
constructs I₀ = ⟨AS,I₂⟩, rather than deducing that the old I is generated
by its two parabolics.  In the nontrivial-two-core branch, I₀ belongs to
I* and has the same Sylow intersection S.  The residual A is two-perfect,
so it lies in O²(L ∩ I₀).  Thus the first parabolic recomputed inside I₀,
together with the original I₂, still generates I₀.

The source application below obtains both residual factorizations from
14.6.6(3) and applies 14.6.10(1–2) to the reselected group.  The other
branch O₂(I₀) = 1 requires the F.1.12 size bound and is not asserted here.
Source: Aschbacher–Smith, refs/quasithin.pdf, 14.6.6(6), printed pp.1023–1024,
and the explicit generation hypothesis of 14.6.10, printed p.1028.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
variable {G : Type*} [Group G] [Finite G]

/-- The literal generated choice in the nontrivial-core branch of 14.6.6(6).
The first residual can be recomputed inside the new group without losing
its generation property. -/
theorem generated_parabolic_choice_of_twoCore_ne_bot
    (T : Sylow 2 G) (Tu M Mc L I H2 T0 : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G) Tu Mc M))
    (hTuT : Tu ≤ (T : Subgroup G)) (hLM : L ≤ M)
    (hS0 : (T : Subgroup G) ⊓ I ≤ T0)
    (hSylH2 : Chapter1.IsSylowIn 2 T0 H2) (hT0M : T0 ≤ M)
    (hH2out : ¬ H2 ≤ M)
    (hAout : ¬ (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype ≤ Mc)
    (hcore : (((pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype ⊔
      ((T : Subgroup G) ⊓ I)) ⊔ ((pResidual 2 H2).map H2.subtype ⊔
      ((T : Subgroup G) ⊓ I))).pCoreIn 2 ≠ ⊥) :
    let S := (T : Subgroup G) ⊓ I
    let I2 := (pResidual 2 H2).map H2.subtype ⊔ S
    let I0 := ((pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype ⊔ S) ⊔ I2
    I0 ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G) Tu Mc M) ∧
      (T : Subgroup G) ⊓ I0 = S ∧
      ((pResidual 2 (L ⊓ I0 : Subgroup G)).map (L ⊓ I0).subtype ⊔
        ((T : Subgroup G) ⊓ I0)) ⊔ I2 = I0 ∧
      ¬ I0 ⊓ M ≤ Mc ∧ I2 ≤ H2 := by
  let S := (T : Subgroup G) ⊓ I
  let A := (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype
  let B := (pResidual 2 H2).map H2.subtype
  let I2 := B ⊔ S
  let I0 := (A ⊔ S) ⊔ I2
  change I0 ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G) Tu Mc M) ∧
    (T : Subgroup G) ⊓ I0 = S ∧
    ((pResidual 2 (L ⊓ I0 : Subgroup G)).map (L ⊓ I0).subtype ⊔
      ((T : Subgroup G) ⊓ I0)) ⊔ I2 = I0 ∧ ¬ I0 ⊓ M ≤ Mc ∧ I2 ≤ H2
  have hBcover : B ⊔ T0 = H2 := by
    obtain ⟨P,hP⟩ := hSylH2
    have hh := congrArg (map H2.subtype) (pResidual_sup_sylow_eq_top P)
    simpa only [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype,hP] using hh
  have hI2out : ¬ I2 ≤ M := by
    intro hc
    exact hH2out (hBcover ▸ sup_le (le_sup_left.trans hc) hT0M)
  have hSI0 : S ≤ I0 := le_sup_right.trans le_sup_left
  have hAI0 : A ≤ I0 := le_sup_left.trans le_sup_left
  have hAL : A ≤ L := (map_subtype_le _).trans inf_le_left
  have hmem : I0 ∈ outsideOvergroups (Chapter1.H G) Tu Mc M :=
    ⟨hcore, (le_inf hTuT hI.1.2.1).trans hSI0,
      fun hh => hAout (hAI0.trans hh), fun hh => hI2out (le_sup_right.trans hh)⟩
  obtain ⟨hI0,hS⟩ := lemma14_6_4 hI hmem hSI0
  refine ⟨hI0,hS,?_,fun hh => hAout ((le_inf hAI0 (hAL.trans hLM)).trans hh),
    sup_le (map_subtype_le _) (hS0.trans (Chapter1.isSylowIn_iff.mp hSylH2).2.1)⟩
  have hAres : A ≤ (pResidual 2 (L ⊓ I0 : Subgroup G)).map (L ⊓ I0).subtype := by
    have hh := embedded_pResidual_mono 2 (le_inf hAL hAI0)
    rw [(pResidual_eq_top_iff 2 A).mpr
      (isPPerfect_embedded_pResidual 2 (L ⊓ I)),←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  rw [hS]
  apply le_antisymm
  · exact sup_le (sup_le ((map_subtype_le _).trans inf_le_right) hSI0) le_sup_right
  · exact sup_le_sup (sup_le_sup hAres le_rfl) le_rfl

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

/-- The containment needed to form the second parabolic in 14.6.6(6),
from the literal suitable-involution data of 14.6.3. -/
theorem source_suitable_intersection_le_quotientCentralizer
    (I : Subgroup G)
    (hI : I ∈ outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M) :
    (T : Subgroup G) ⊓ I ≤ suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u := by
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
  rcases (suitable_involution_intersection_sylow
    T Tu T0 M Mc I hi.1 hindex hn.1 hN0 hpair hI).1 with hcase | hcase
  · exact hcase.le.trans (hn.1 ▸ Tu.le_normalizer)
  · exact hcase.le

/-- The source's generated choice, followed by the actual 14.6.10(1–2)
application. Both residual factorizations and generation in the reselected
group are proved, rather than required from the caller. -/
theorem source_generated_parabolic_cores
    (I H2 : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (hout : ¬ I ⊓ M ≤ Mc)
    (hSylH2 : Chapter1.IsSylowIn 2 (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u) H2)
    (hH2out : ¬ H2 ≤ M)
    (hcoreIndex : 4 < (H.pCoreIn 2).relIndex (T : Subgroup G))
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H)))
    (hcore : (((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)) ⊔
      ((pResidual 2 H2).map H2.subtype ⊔ ((T : Subgroup G) ⊓ I))).pCoreIn 2 ≠ ⊥) :
    let I2 := (pResidual 2 H2).map H2.subtype ⊔ ((T : Subgroup G) ⊓ I)
    let I0 := ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)) ⊔ I2
    let I1 := (pResidual 2 (sourceResidual M Mc ⊓ I0 : Subgroup G)).map
      (sourceResidual M Mc ⊓ I0).subtype ⊔ ((T : Subgroup G) ⊓ I0)
    I0 ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M) ∧
      (T : Subgroup G) ⊓ I0 = (T : Subgroup G) ⊓ I ∧
      I1 ⊔ I2 = I0 ∧ I2 ≤ H2 ∧
      (I1.pCoreIn 2).characteristicNormalizerClosure ≤ M ∧
      I1.pCoreIn 2 ≠ ⊥ ∧ I1.pCoreIn 2 ≠ I2.pCoreIn 2 := by
  let L := sourceResidual M Mc
  let T0 := suitableQuotientCentralizer
    (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u
  let I2 := (pResidual 2 H2).map H2.subtype ⊔ ((T : Subgroup G) ⊓ I)
  let I0 := ((pResidual 2 (L ⊓ I : Subgroup G)).map
    (L ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)) ⊔ I2
  have hcover := (source_lemma_14_6_6_3 hG T hempty hM hunique hmany hcard e
    hab H hH u hu hindex hmove hproduct I hI.1.2.1 hout).1
  have hSyl := (source_suitable_intersection_sylow hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I hI.1).1
  have hAout := (source_intersection_parabolic_data hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct I hI.1.2.1 hSyl hcover).2.2.2
  have hS0 := source_suitable_intersection_le_quotientCentralizer hG T hempty hM hunique
    hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I hI.1
  have hT0M : T0 ≤ M := inf_le_left.trans hM.1.2
  obtain ⟨hI0,hS,hgen,hout0,hI2H2⟩ := generated_parabolic_choice_of_twoCore_ne_bot
    T _ M Mc L I H2 T0 hI inf_le_left (sourceResidual_le M Mc) hS0 hSylH2
      hT0M hH2out hAout hcore
  have hcover0 := (source_lemma_14_6_6_3 hG T hempty hM hunique hmany hcard e
    hab H hH u hu hindex hmove hproduct I0 hI0.1.2.1 hout0).1
  exact ⟨hI0,hS,hgen,hI2H2,source_lemma_14_6_10_1_2 hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I0 I2 hI0
      hcoreIndex hrank hcover0 hgen⟩

end CFSG.Quasithin.Chapter14.Section06
