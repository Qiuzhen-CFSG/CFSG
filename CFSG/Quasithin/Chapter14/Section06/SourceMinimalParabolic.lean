module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicCore
public import CFSG.Quasithin.Chapter14.Section06.SourceNormalSubgroups
public import CFSG.Quasithin.ChapterE.Section02.Structure.Original

/-!
# The original minimal parabolic in the nonsolvable factorization branch

The IStar normalizer theorem and the normalizer condition in T exclude a
normal Sylow intersection. In the non-factorization branch, 14.6.6(5)
therefore makes the actual inclusion-minimal outside subgroup a minimal
parabolic. Applying the opening source theorem E.2.2 constructs its generating
C-component on the literal two-core quotient. The factorization alternative
retains both original set products.

Source: Aschbacher--Smith 14.6.6(5),(7), 14.6.9, printed pp.1023--1028;
E.2.2, printed pp.215--216. Component-model exclusions remain separate.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section06
variable {G : Type*} [Group G] [Finite G]

/-- A proper maximal outside Sylow intersection cannot be normal in I.
The ambient normalizer theorem supplies the contradiction inside T. -/
theorem iStar_intersection_not_normal
    (T : Sylow 2 G) (Tu M Mc I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G) Tu Mc M))
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ I) I)
    (hproper : (T : Subgroup G) ⊓ I < (T : Subgroup G)) :
    ¬ (((T : Subgroup G) ⊓ I).subgroupOf I).Normal := by
  let R := (T : Subgroup G) ⊓ I
  have hRne : R ≠ ⊥ := by
    intro he
    obtain ⟨S,hS⟩ := hSyl
    have hc : I.pCoreIn 2 ≤ R := (pCoreIn_le_sylow I S).trans_eq hS
    exact hI.1.1 (le_bot_iff.mp (hc.trans he.le))
  intro hn
  have hIN : I ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show R ≤ I from inf_le_right)).mp hn
  have hNT := (source_lemma_14_6_9_normalizers T Tu M Mc I hI R hRne le_rfl hIN).2.1
  have hRproper : R.subgroupOf (T : Subgroup G) < ⊤ :=
    lt_top_iff_ne_top.mpr (fun he => hproper.not_ge (subgroupOf_eq_top.mp he))
  let : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
  obtain ⟨t,ht,htR⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (R.subgroupOf (T : Subgroup G)) hRproper)
  have htN : (t : G) ∈ normalizer (R : Set G) := by
    rw [←subgroupOf_normalizer_eq (show R ≤ (T : Subgroup G) from inf_le_left)] at ht
    exact ht
  have htRI : (t : G) ∈ (T : Subgroup G) ⊓ I := by
    rw [←hNT]
    exact ⟨t.property,htN⟩
  exact htR htRI

omit [Finite G] in
private theorem unique_transport (I B S : Subgroup G) (hB : B ≤ I)
    (hS : S ≤ B) (hmax : Maximal (fun Y : Subgroup G => Y < I) B)
    (hu : ∀ J : Subgroup G, S ≤ J → Maximal (fun Y : Subgroup G => Y < I) J → J = B) :
    Order.HasUniqueMaximalOver (S.subgroupOf I) ⊤ ∧ IsCoatom (B.subgroupOf I) := by
  have hmaptop : (⊤ : Subgroup I).map I.subtype = I := by
    rw [←MonoidHom.range_eq_map,range_subtype]
  have hmap (X : Subgroup I) : X.map I.subtype < I ↔ X < ⊤ := by
    simpa only [hmaptop] using
      (map_lt_map_iff_of_injective I.subtype_injective (H := X) (K := ⊤))
  have hcov : B.subgroupOf I ⋖ ⊤ := by
    refine ⟨lt_top_iff_ne_top.mpr (fun he => hmax.1.not_ge (subgroupOf_eq_top.mp he)),?_⟩
    intro X hBX hX
    have he : X.map I.subtype ≤ B := hmax.2 ((hmap X).mpr hX) (by
      rw [←map_subgroupOf_eq_of_le hB]
      exact map_mono hBX.le)
    exact hBX.not_ge (by intro x hx; exact he (mem_map_of_mem I.subtype hx))
  refine ⟨?_,hcov.isCoatom⟩
  refine ⟨lt_of_le_of_lt (subgroupOf_mono I hS) hcov.lt, B.subgroupOf I,
    ⟨subgroupOf_mono I hS,hcov⟩,?_⟩
  intro X hX
  have he : X.map I.subtype = B := hu _ (by
    rw [←map_subgroupOf_eq_of_le (hS.trans hB)]
    exact map_mono hX.1) ⟨(hmap X).mpr hX.2.lt,by
      intro Y hY hXY
      have hXIY : X ≤ Y.subgroupOf I := by
        intro x hx; exact hXY (mem_map_of_mem I.subtype hx)
      have hYtop : Y.subgroupOf I < ⊤ := lt_top_iff_ne_top.mpr
        (fun he => hY.not_ge (subgroupOf_eq_top.mp he))
      have hYX : Y.subgroupOf I ≤ X :=
        ((hX.2.eq_or_eq hXIY le_top).resolve_right hYtop.ne).le
      rw [←map_subgroupOf_eq_of_le hY.le]
      exact map_mono hYX⟩
  apply map_injective I.subtype_injective
  rw [map_subgroupOf_eq_of_le hB,he]

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


/-- The original minimal outside choice is a minimal parabolic unless the
literal L and LT products already hold. The Sylow and normality premises
are discharged from the original source setup. -/
theorem source_minimal_parabolic_or_factorization
    (I : Subgroup G)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M)) :
    (∃ S : Sylow 2 I,
      (S : Subgroup I).map I.subtype = (T : Subgroup G) ⊓ I ∧
      ∃ hP : ChapterB.IsMinimalParabolicOver S ⊤,
        ChapterB.minimalParabolicMax S hP = (I ⊓ Mc).subgroupOf I) ∨
    (let L := sourceResidual M Mc
     let R := (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype
     (L : Set G) = (R : Set G) * (L.pCoreIn 2 : Set G) ∧
       (L ⊔ (T : Subgroup G) : Subgroup G) =
         (R : Set G) * ((T : Subgroup G) ⊓ I : Subgroup G) *
           ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)) := by
  obtain ⟨hSyl,hproper⟩ := source_suitable_intersection_sylow hG T hempty hM hunique
    hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I hI.1.1
  rcases source_lemma_14_6_6_5 hG T hempty hM hunique hmany hcard e hab H hH
    u hu hindex hmove hproduct I hI hSyl with hun | hf
  · left
    obtain ⟨S,hS⟩ := hSyl
    have he : ((T : Subgroup G) ⊓ I).subgroupOf I = (S : Subgroup I) := by
      rw [←hS]
      exact comap_map_eq_self_of_injective I.subtype_injective _
    have huB := unique_transport I (I ⊓ Mc) ((T : Subgroup G) ⊓ I)
      inf_le_left hun.1 hun.2.1 hun.2.2
    have hu' : Order.HasUniqueMaximalOver (S : Subgroup I) ⊤ := he ▸ huB.1
    have hn : ¬ (S : Subgroup I).Normal := by
      rw [←he]
      exact iStar_intersection_not_normal T _ M Mc I hI.1 ⟨S,hS⟩ hproper
    have hP : ChapterB.IsMinimalParabolicOver S ⊤ := by
      refine ⟨hu',?_⟩
      intro hnorm
      exact hn (normalizer_eq_top_iff.mp (top_unique hnorm))
    refine ⟨S,hS,hP,?_⟩
    exact (ChapterB.minimalParabolicMax_unique S hP huB.2
      (he ▸ subgroupOf_mono I hun.1)).symm
  · exact Or.inr hf

/-- The actual E.2.2 consumer in the nonsolvable branch of 14.6.9.
The source hypotheses construct the minimal parabolic and its SQTK input;
no minimal-parabolic or component-selection premise remains. -/
theorem source_nonsolvable_component_or_factorization
    (I : Subgroup G) (hs : ¬ Group.IsSolvable I)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M)) :
    (∃ S : Sylow 2 I,
      (S : Subgroup I).map I.subtype = (T : Subgroup G) ⊓ I ∧
      ∃ hP : ChapterB.IsMinimalParabolicOver S ⊤,
      ChapterB.minimalParabolicMax S hP = (I ⊓ Mc).subgroupOf I ∧
      ∃ K : Subgroup I, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
        K ⊔ (S : Subgroup I) = ⊤ ∧
        IsComponent (I ⧸ pCore 2 I) (K.map (QuotientGroup.mk' (pCore 2 I)))) ∨
    (let L := sourceResidual M Mc
     let R := (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype
     (L : Set G) = (R : Set G) * (L.pCoreIn 2 : Set G) ∧
       (L ⊔ (T : Subgroup G) : Subgroup G) =
         (R : Set G) * ((T : Subgroup G) ⊓ I : Subgroup G) *
           ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)) := by
  rcases source_minimal_parabolic_or_factorization hG T hempty hM hunique hmany hcard e
    hab H hH u hu hindex hmove hproduct hU3 hlocal I hI with ⟨S,hS,hP,hmax⟩ | hf
  · have hsq : IsSQTK KnownSimple.IsKnownSimple I := by
      let N := normalizer (I.pCoreIn 2 : Set G)
      have hIN : I ≤ N := I.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
      have hN : IsTwoLocal N := ⟨I.pCoreIn 2,hI.1.1.1,isPGroup_pCoreIn 2 I,rfl⟩
      exact (IsSQTK.equiv (subgroupOfEquivOfLe hIN)).mp
        ((hG.twoLocal_sqtk hN).subgroup (I.subgroupOf N))
    exact Or.inl ⟨S,hS,hP,hmax,ChapterE.Structure.source_original_component hsq S hP hs⟩
  · exact Or.inr hf

end CFSG.Quasithin.Chapter14.Section06
