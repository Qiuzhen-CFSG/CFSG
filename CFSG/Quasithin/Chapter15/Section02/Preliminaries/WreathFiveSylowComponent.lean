module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveResidualContainment
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.GeneralSylowBlocks
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.ChiZero

/-!
# The Sylow overcomponent in the original wreath-five branch

C.2.5 makes the normal overcomponent L₁ a χ₀ block when R is Sylow in
L₁R. The original wreath component K is a local C-component for the same
S inside W. The χ₀ proper-Sylow-overgroup theorem therefore forces K=L₁.
Together with the prime-index residual-containment proof, this gives the
actual alternative K=L₁ or Y≤L₁ in every failed-quotient configuration.

The final normalizer contradiction in the first case and model comparison
in the second remain distinct source obligations.
Source: Aschbacher--Smith, original15.2.4, printed pp.1106--1107.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02
variable {G : Type*} [Group G] [Finite G]

/-- A local component in the original Sylow configuration fills a containing χ₀ block. -/
public theorem source_local_component_eq_chiZero_overcomponent
    {H K S W L₁ : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn H) (hSH : S ≤ H)
    (hKW : K ≤ W) (hSyl : Chapter1.IsSylowIn 2 S W)
    (hcore : pCore 2 W ≠ ⊥)
    (hL₁ : L₁ ∈ Chapter1.cComponentsIn W) (hKL : K ≤ L₁)
    (hchi : ChapterC.IsChiZeroBlock L₁) : K = L₁ := by
  obtain ⟨P,hP⟩ := hSyl
  have hSW : S ≤ W := hP ▸ map_subtype_le _
  have hP' : (P : Subgroup W) = S.subgroupOf W := by
    rw [←hP]
    exact (comap_map_eq_self_of_injective W.subtype_injective _).symm
  have hWH : W ∈ Chapter1.H G :=
    fun hb => hcore ((map_eq_bot_iff_of_injective _ W.subtype_injective).mp hb)
  have hcoreS : W.pCoreIn 2 ≤ S := hP ▸ pCoreIn_le_sylow W P
  have hcoreKS : W.pCoreIn 2 ≤ (K ⊔ S).pCoreIn 2 :=
    (le_inf (hcoreS.trans le_sup_right) le_rfl).trans
      (inf_pCoreIn_le_of_le 2 (sup_le hKW hSW))
  have hlocal : K ∈ Chapter1.L G S :=
    ⟨hK.2.subgroupOf_of_le le_sup_left (sup_le hK.1 hSH),
      Chapter1.IsSylowIn.restrict ⟨P,hP⟩ le_sup_right (sup_le hKW hSW),
      fun hb => hWH (bot_unique (hb ▸ hcoreKS))⟩
  have hlocal' : K.subgroupOf W ∈ Chapter1.L W (P : Subgroup W) := by
    rw [hP']
    exact (Chapter1.mem_LIn_iff_subgroupOf hSW hKW).mp ⟨hKW,hlocal⟩
  have he := ChapterA.Section03.SourceEmbeddings.eq_of_chiZero_containing_component
    P hlocal'.1 hL₁.2 (comap_mono hKL)
    (hchi.of_mulEquiv (subgroupOfEquivOfLe hL₁.1).symm)
  have hh := congrArg (map W.subtype) he
  simpa only [map_subgroupOf_eq_of_le hKW,map_subgroupOf_eq_of_le hL₁.1] using hh

open Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource

/-- The original chosen component either is the normal overcomponent or that
overcomponent contains the original residual Y. All C.2.5 and containment
premises are discharged on the literal failed-quotient source configuration. -/
public theorem source_HStar_wreath_five_failed_quotient_component_alternative
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V H : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M V)
    (hcases : SourceCases.Dihedral (imageRepresentation M V hV.normalized) ∨
      SourceCases.Omega (imageRepresentation M V hV.normalized))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2)))) :
    let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    ∃ K : Subgroup G, K ∈ Chapter1.cComponentsIn H ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) ∧ ¬ K ≤ M ∧
      let L := ![Y ⊔ (M ⊓ Mc).pCoreIn 2,K]
      let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
      let W := ChapterF.Source.generated L S
      let q := QuotientGroup.mk' (pCore 2 W)
      let R := (Y ⊔ S).pCoreIn 2
      S.relIndex (T : Subgroup G) = 2 ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤ S ∧
      (pCore 2 W ≠ ⊥ →
        (¬ ∀ i, generalizedFitting (((ChapterF.Source.parabolic L S i).subgroupOf W).map q) =
          pCore 2 (((ChapterF.Source.parabolic L S i).subgroupOf W).map q)) →
        Chapter1.IsSylowIn 2 S W ∧ V ≤ W.pCoreIn 2 ∧
        generalizedFitting W = pCore 2 W ∧
        Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple W R (W ⊓ M) ∧
        ∃ L₁ : Subgroup G, L₁ ∈ Chapter1.cComponentsIn W ∧ K ≤ L₁ ∧ ¬ L₁ ≤ M ∧
          W ≤ normalizer (L₁ : Set G) ∧ W = L₁ ⊔ (W ⊓ M) ∧
          generalizedFitting L₁ = pCore 2 L₁ ∧ (K = L₁ ∨ Y ≤ L₁)) := by
  obtain ⟨K,hK,heK,hout,hi,hJS,hconf⟩ :=
    source_HStar_wreath_five_failed_quotient_residual_configuration
      hG T hempty hM hJ hu hmany hV hcases hH he
  refine ⟨K,hK,heK,hout,hi,hJS,?_⟩
  intro hcore hf
  obtain ⟨hSyl,hVcore,hWfit,hsetup,L₁,hL₁,hKL,houtL,hNL,hgen,hLfit,hY⟩ := hconf hcore hf
  refine ⟨hSyl,hVcore,hWfit,hsetup,L₁,hL₁,hKL,houtL,hNL,hgen,hLfit,?_⟩
  let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
  let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
  let W := ChapterF.Source.generated ![Y ⊔ (M ⊓ Mc).pCoreIn 2,K] S
  let R := (Y ⊔ S).pCoreIn 2
  by_cases hs : Chapter1.IsSylowIn 2 R (L₁ ⊔ R)
  · have hRW : R ≤ W := (pCoreIn_le 2 _).trans
      (sup_le (show Y ≤ W from le_sup_left.trans (le_sup_left.trans le_sup_left)) le_sup_right)
    have hc := ChapterC.C27Source.chiZero_of_sylow_setup hsetup hL₁ hLfit
      (fun hh => houtL (hh.trans inf_le_right)) (hRW.trans hNL) hs
    exact Or.inl (source_local_component_eq_chiZero_overcomponent hK (inf_le_left.trans hH.1.1.2)
      (show K ≤ W from le_sup_right.trans le_sup_left) hSyl hcore hL₁ hKL hc)
  · exact Or.inr (hY hs)
end CFSG.Quasithin.Chapter15.Section02
