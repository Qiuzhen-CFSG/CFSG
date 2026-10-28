module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveFailedParabolic
public import Theory.GroupTheory.PrimeIndexResidualContainment
public import Theory.GroupTheory.SylowNormalizedSupIndex

/-!
# The marked-five residual lies in the normal overcomponent

Keep the original residual Y, S=N_T(K), W=⟨YRc,K,S⟩ and R=O₂(YS).
The marked five quotient gives [YS:S]=5. If a normal overcomponent L₁ of
W does not contain Y, the prime-index intersection theorem puts S∩L₁
inside R. Since S is Sylow in W, its intersection is Sylow in L₁, so R
is Sylow in L₁R. Thus the non-Sylow branch has Y≤L₁, as required by the
later C.2.7 comparison. The final theorem applies this deduction to the
same chosen H-star component and literal failed-quotient configuration.

The earlier Sylow-branch exclusion and mixed DGS compatibility remain
separate source obligations; neither is assumed as a proved conclusion.
Source: Aschbacher--Smith, original15.2.4, printed pp.1106--1107.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02
variable {G : Type*} [Group G] [Finite G]
private theorem residual_le_of_prime_index_not_sylow
    {Y S W L : Subgroup G} (hY : IsPPerfect 2 Y)
    (hYW : Y ≤ W) (hSyl : Chapter1.IsSylowIn 2 S W)
    (hLW : L ≤ W) (hWN : W ≤ normalizer (L : Set G))
    (hi : S.relIndex (Y ⊔ S) = 5)
    (hnot : ¬ Chapter1.IsSylowIn 2 ((Y ⊔ S).pCoreIn 2) (L ⊔ (Y ⊔ S).pCoreIn 2)) :
    Y ≤ L := by
  by_contra hout
  have hS := (Chapter1.isSylowIn_iff.mp hSyl).1
  have hSW := (Chapter1.isSylowIn_iff.mp hSyl).2.1
  have hPW : Y ⊔ S ≤ W := sup_le hYW hSW
  have hD := inf_le_pCore_of_prime_index_of_not_le hY hS (by decide : Nat.Prime 5) hi (hPW.trans hWN) hout
  have hSL : S ⊓ L ≤ (Y ⊔ S).pCoreIn 2 :=
    (inf_le_inf_right L (show S ≤ Y ⊔ S from le_sup_right)).trans hD
  have hn : (L.subgroupOf W).Normal := (normal_subgroupOf_iff_le_normalizer hLW).mpr hWN
  obtain ⟨P,hP⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hSyl hLW hn.isSubnormal
  apply hnot
  exact IsPGroup.exists_sylow_sup_of_coprime_index L ((Y ⊔ S).pCoreIn 2)
    (isPGroup_pCoreIn 2 _) (((pCoreIn_le 2 _).trans hPW).trans hWN)
    P P.not_dvd_index (hP ▸ hSL)

omit [Finite G] in
private theorem core_le_sylow_of_normalizes
    {Y S W : Subgroup G} (hYW : Y ≤ W) (hSyl : Chapter1.IsSylowIn 2 S W)
    (hn : S ≤ normalizer (Y : Set G)) : Y.pCoreIn 2 ≤ S := by
  obtain ⟨hS,hSW,hmax⟩ := Chapter1.isSylowIn_iff.mp hSyl
  have hjoin := hmax (Y.pCoreIn 2 ⊔ S)
    ((isPGroup_pCoreIn 2 Y).to_sup_of_normal_left' hS
      (hn.trans (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y))))
    le_sup_right (sup_le ((pCoreIn_le 2 Y).trans hYW) hSW)
  exact le_sup_left.trans hjoin.le

open Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource

/-- The original case-II residual is two-perfect. -/
public theorem source_caseIIResidual_isPPerfect (T : Sylow 2 G) (M M₀ Mc : Subgroup G) :
    IsPPerfect 2 (caseIIResidual T M M₀ Mc) := by
  let A := conjugateSpanBy ((M ⊓ Mc).pCoreIn 2)
    (twoResidualAmbient M₀ ⊔ (T : Subgroup G))
  have he : twoResidualAmbient A = (pResidual 2 A).map A.subtype := by
    unfold twoResidualAmbient twoResidualSubgroup pResidual
    congr 1
    apply congrArg sInf
    ext N
    constructor
    · rintro ⟨hN,n,hn⟩
      exact ⟨hN,IsPGroup.of_card hn⟩
    · rintro ⟨hN,hn⟩
      exact ⟨hN,IsPGroup.iff_card.mp hn⟩
  change IsPPerfect 2 (twoResidualAmbient A)
  rw [he]
  exact isPPerfect_embedded_pResidual 2 A


/-- The original marked-five residual lies in every normal overcomponent
for which R is not Sylow in L₁R. -/
public theorem source_dihedral_five_residual_le_normal_of_not_sylow
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V K L₁ : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M V)
    (l : LocalGeneration ((imageRepresentation M V hV.normalized).comp
      (Jhat (imageRepresentation M V hV.normalized)).subtype))
    (hd : DihedralMarking l 5 2) :
    let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
    let W := ChapterF.Source.generated ![Y ⊔ (M ⊓ Mc).pCoreIn 2,K] S
    let R := (Y ⊔ S).pCoreIn 2
    Chapter1.IsSylowIn 2 S W → L₁ ≤ W → W ≤ normalizer (L₁ : Set G) →
      (¬ Chapter1.IsSylowIn 2 R (L₁ ⊔ R)) → Y ≤ L₁ := by
  intro Y S W R hSyl hLW hWN hnot
  have hYM : Y ≤ M := source_caseIIResidual_le T hM.1.2 (map_subtype_le _)
  have hYW : Y ≤ W := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hSN : S ≤ normalizer (Y : Set G) :=
    (inf_le_left.trans hM.1.2).trans ((normal_subgroupOf_iff_le_normalizer hYM).mp
      (source_dihedral_five_residual_normal T hM.1.2 hu hV l hd))
  have hc := source_dihedral_five_residual_core_index hG T hempty hM hJ hu hmany hV l
    ((primeDimensionOptions_iff 5 2).mpr (Or.inr ⟨rfl,rfl⟩)) hd
  have hS5 : ¬ 5 ∣ Nat.card S := by
    obtain ⟨n,hn⟩ := (Chapter1.isSylowIn_iff.mp hSyl).1.exists_card_eq
    rw [hn]
    intro hh
    have hd' := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 5) hh
    norm_num at hd'
  have hi := index_five_of_core_le_borel Y S hc.1
    (core_le_sylow_of_normalizes hYW hSyl hSN) hSN hS5
  exact residual_le_of_prime_index_not_sylow (source_caseIIResidual_isPPerfect T M _ Mc)
    hYW hSyl hLW hWN hi hnot

/-- The same normal overcomponent supplied by the failed-quotient source
configuration contains Y in the non-Sylow branch. -/
public theorem source_HStar_wreath_five_failed_quotient_residual_configuration
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
          generalizedFitting L₁ = pCore 2 L₁ ∧
          ((¬ Chapter1.IsSylowIn 2 R (L₁ ⊔ R)) → Y ≤ L₁)) := by
  obtain ⟨l,hd,_⟩ := source_HStar_wreath_five_reduction
    hG T hempty hM hJ hu hmany hV hcases hH he
  obtain ⟨K,hK,heK,hout,hi,hJS,hconf⟩ := source_HStar_wreath_five_failed_quotient_configuration
    hG T hempty hM hJ hu hmany hV hcases hH he
  refine ⟨K,hK,heK,hout,hi,hJS,?_⟩
  intro hcore hf
  obtain ⟨hSyl,hVcore,hWfit,hsetup,L₁,hL₁,hKL,houtL,hNL,hgen,hLfit⟩ := hconf hcore hf
  exact ⟨hSyl,hVcore,hWfit,hsetup,L₁,hL₁,hKL,houtL,hNL,hgen,hLfit,
    source_dihedral_five_residual_le_normal_of_not_sylow
      hG T hempty hM hJ hu hmany hV l hd hSyl hL₁.1 hNL⟩

end CFSG.Quasithin.Chapter15.Section02
