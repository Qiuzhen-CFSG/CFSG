module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent
public import CFSG.Quasithin.Chapter14.Section06.SourceSolvableInvariantSubgroups.Normal
public import Theory.GroupTheory.PerfectSmallTwoAction

/-!
# The selected component escapes using the solvable quotient kernel

The Goldschmidt prime-to-three core is solvable. The invariant-subgroup
dichotomy places it in C_M(V): otherwise it contains the moving residual,
which F.6.11 would force into O₂(I), contradicting two-perfection. If the
selected component K lay in M, its perfect action on the four-group V
would be trivial. In the quotient, F.6.10 either puts the first residual
inside K O₃′(I), contradicting its action, or makes K O₃′(I) I₁=I, forcing
I≤M. Thus the literal selected component escapes I∩M in either orientation.

Source: Aschbacher–Smith, F.6.10–11 and 14.6.10(3),(5), printed pp.306,1028–1029.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]
namespace CFSG.Quasithin.Chapter14.Section06
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


/-- The solvable prime-to-three kernel centralizes the original four-group. -/
theorem source_parabolic_primeToThreeCore_centralizes
    (hcoreIndex : 4 < (H.pCoreIn 2).relIndex (T : Subgroup G))
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H)))
    (I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (hout : ¬ I ⊓ M ≤ Mc) (B : Subgroup I)
    (htriple : ChapterF.IsGoldschmidtTriple
      (((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
        (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)).subgroupOf I) B) :
    (pPrimeCore 3 I).map I.subtype ≤ M ⊓ centralizer (localModule T M : Set G) := by
  let P := (pPrimeCore 3 I).map I.subtype
  let LI := (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
    (sourceResidual M Mc ⊓ I).subtype
  let I1 := LI ⊔ ((T : Subgroup G) ⊓ I)
  let : Group.IsSolvable (pPrimeCore 3 I) := htriple.primeToThreeCore_solvable
  let : Group.IsSolvable P := Group.isSolvable_of_surjective
    (I.subtype.subgroupMap_surjective (pPrimeCore 3 I))
  have hPI : P ≤ I := map_subtype_le _
  have hN : I ≤ normalizer (P : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer hPI).mp
    rw [show P.subgroupOf I = pPrimeCore 3 I from
      comap_map_eq_self_of_injective I.subtype_injective _]
    infer_instance
  have hLII : LI ≤ I := (map_subtype_le _).trans inf_le_right
  have hI1I : I1 ≤ I := sup_le hLII inf_le_right
  rcases source_invariant_solvable_subgroup_of_escape hG T hempty hM hunique hmany hcard
    e hab H hH u hu hindex hmove hproduct hU3 hlocal hcoreIndex hrank I P hI hout hPI
    (hI1I.trans hN) with hLP | hPC
  · have hLN : LI.subgroupOf I ≤ pPrimeCore 3 I := by
      apply (map_le_map_iff_of_injective I.subtype_injective).mp
      rw [map_subgroupOf_eq_of_le hLII]
      exact hLP
    have hLcore : LI ≤ I.pCoreIn 2 := by
      have hh := map_mono (f := I.subtype) ((le_inf
        (subgroupOf_mono I (show LI ≤ I1 from le_sup_left)) hLN).trans
          htriple.left_inf_primeToThreeCore.le)
      rwa [map_subgroupOf_eq_of_le hLII] at hh
    have hz := (isPPerfect_embedded_pResidual 2 (sourceResidual M Mc ⊓ I)).hom_eq_one_of_isPGroup
      (isPGroup_pCoreIn 2 I) (inclusion hLcore)
    have hbot : LI ≤ ⊥ := by
      intro r hr
      change r = 1
      exact congrArg (I.pCoreIn 2).subtype (DFunLike.congr_fun hz ⟨r,hr⟩)
    have hcover := (source_lemma_14_6_6_3 hG T hempty hM hunique hmany hcard e hab
      H hH u hu hindex hmove hproduct I hI.1.2.1 hout).1
    have hSyl := (source_suitable_intersection_sylow hG T hempty hM hunique hmany
      hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I hI.1).1
    have hLIout := (source_intersection_parabolic_data hG T hempty hM hunique hmany
      hcard e hab H hH u hu hindex hmove hproduct I hI.1.2.1 hSyl hcover).2.2.2
    exact (hLIout (hbot.trans bot_le)).elim
  · exact hPC
/-- The selected normal C-component escapes I∩M. Its actual quotient
component supplies both orientations; the solvable kernel has already
been placed in C_M(V), so no component–Sylow supplement is assumed. -/
theorem source_parabolic_component_outside
    (hcoreIndex : 4 < (H.pCoreIn 2).relIndex (T : Subgroup G))
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H)))
    (I I2 : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (hSI2 : (T : Subgroup G) ⊓ I ≤ I2) (hI2H : I2 ≤ H)
    (hquot2 : Nonempty ((I2 ⧸ pCore 2 I2) ≃* Equiv.Perm (Fin 3)))
    (hout : ¬ I ⊓ M ≤ Mc)
    (hgen : ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)) ⊔ I2 = I)
    (K : Subgroup I) (hK : K.IsCComponent) [K.Normal]
    (hbar : IsComponent (I ⧸ pPrimeCore 3 I)
      (K.map (QuotientGroup.mk' (pPrimeCore 3 I)))) :
    ¬ K.map I.subtype ≤ I ⊓ M := by
  let LI := (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
    (sourceResidual M Mc ⊓ I).subtype
  let I1 := LI ⊔ ((T : Subgroup G) ⊓ I)
  let A := I1.subgroupOf I
  let q := QuotientGroup.mk' (pPrimeCore 3 I)
  let KG := K.map I.subtype
  let P := (pPrimeCore 3 I).map I.subtype
  have hLII : LI ≤ I := (map_subtype_le _).trans inf_le_right
  have hI1I : I1 ≤ I := sup_le hLII inf_le_right
  have hI1M : I1 ≤ M := sup_le
    (((map_subtype_le _).trans inf_le_left).trans (sourceResidual_le M Mc))
    (inf_le_left.trans hM.1.2)
  have ht := source_parabolic_goldschmidtTriple_of_escape hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I I2 hI hSI2 hI2H hquot2 hout hgen
  obtain ⟨hqt,_⟩ := source_parabolic_quotient_preparation hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal hcoreIndex hrank
    I I2 hI hSI2 hI2H hquot2 hout hgen
  have hPC := source_parabolic_primeToThreeCore_centralizes hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal hcoreIndex hrank I hI hout
    (I2.subgroupOf I) ht
  intro hKM
  have hKM' : KG ≤ M := hKM.trans inf_le_right
  let V := localModule T M
  let : Group.IsPerfect K := hK.perfect
  let : Group.IsPerfect KG := Group.IsPerfect.map I.subtype
  let : Group.IsPerfect (KG.subgroupOf M) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKM').symm.toMonoidHom)
    (subgroupOfEquivOfLe hKM').symm.surjective
  let : (V.subgroupOf M).Normal :=
    normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
  have hVM : V ≤ M := localModule_le T hM.1.2
  have hc := le_centralizer_of_isPerfect_of_card_le_four (KG.subgroupOf M)
    (V.subgroupOf M) (by
      rw [Nat.card_congr (subgroupOfEquivOfLe hVM).toEquiv,hcard])
  have hKC : KG ≤ centralizer (V : Set G) := by
    intro k hk v hv
    exact congrArg M.subtype (hc (show (⟨k,hKM' hk⟩ : M) ∈ KG.subgroupOf M from hk)
      ⟨v,hVM hv⟩ hv)
  let : (K.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  rcases ChapterF.SourceAssembly.normal_component_contains_residual hqt
    ht.primeToThreeCore_quotient_twoCore_eq_bot hbar with hleft | hright
  · have hLA : LI ≤ (pResidual 2 I1).map I1.subtype := by
      have hp := (isPPerfect_embedded_pResidual 2 (sourceResidual M Mc ⊓ I)).of_surjective
        (subgroupOfEquivOfLe (show LI ≤ I1 from le_sup_left)).symm.toMonoidHom
        (subgroupOfEquivOfLe (show LI ≤ I1 from le_sup_left)).symm.surjective
      have hh := map_mono (f := I1.subtype) (le_pResidual_of_isPPerfect (LI.subgroupOf I1) hp)
      rwa [map_subgroupOf_eq_of_le (show LI ≤ I1 from le_sup_left)] at hh
    have hLAi : LI.subgroupOf I ≤ (pResidual 2 A).map A.subtype := by
      apply (map_le_map_iff_of_injective I.subtype_injective).mp
      rw [map_subgroupOf_eq_of_le hLII,map_embedded_pResidual,
        map_subgroupOf_eq_of_le hI1I]
      exact hLA
    have him : (LI.subgroupOf I).map q ≤ K.map q := by
      apply (map_mono hLAi).trans
      rw [map_embedded_pResidual]
      exact hleft.1
    have hpre : LI.subgroupOf I ≤ K ⊔ pPrimeCore 3 I := by
      have hh := (le_comap_map q (LI.subgroupOf I)).trans (comap_mono him)
      simpa only [comap_map_eq,q,QuotientGroup.ker_mk'] using hh
    have hLIP : LI ≤ KG ⊔ P := by
      have hh := map_mono (f := I.subtype) hpre
      rwa [map_subgroupOf_eq_of_le hLII,Subgroup.map_sup] at hh
    have hcover := (source_lemma_14_6_6_3 hG T hempty hM hunique hmany hcard e hab
      H hH u hu hindex hmove hproduct I hI.1.2.1 hout).1
    have hSyl := (source_suitable_intersection_sylow hG T hempty hM hunique hmany
      hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I hI.1).1
    have hLIout := (source_intersection_parabolic_data hG T hempty hM hunique hmany
      hcard e hab H hH u hu hindex hmove hproduct I hI.1.2.1 hSyl hcover).2.2.2
    exact hLIout (hLIP.trans ((sup_le hKC (hPC.trans inf_le_right)).trans
      (InitialSource.localModule_centralizer_le_partner T M hunique)))
  · have he : K ⊔ A ⊔ pPrimeCore 3 I = ⊤ := by
      have hh := congrArg (Subgroup.comap q) hright.2
      rw [←Subgroup.map_sup,comap_map_eq,QuotientGroup.ker_mk',comap_top] at hh
      exact hh
    have hmap := congrArg (Subgroup.map I.subtype) he
    rw [Subgroup.map_sup,Subgroup.map_sup,map_subgroupOf_eq_of_le hI1I,
      ←MonoidHom.range_eq_map,range_subtype] at hmap
    exact hI.1.2.2.2 (hmap.symm ▸ sup_le (sup_le hKM' hI1M) (hPC.trans inf_le_left))

end CFSG.Quasithin.Chapter14.Section06
