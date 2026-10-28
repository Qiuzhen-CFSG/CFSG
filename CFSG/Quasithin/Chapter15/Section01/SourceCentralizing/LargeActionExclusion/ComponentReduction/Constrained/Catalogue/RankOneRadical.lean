module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.OrbitBorel
/-!
# The exact full-Sylow branch of the constrained catalogue

For an ambient C-component, the Sylow orbit of its marked intersection is
M_Z-invariant: O²(M_Z) fixes the component and the Sylow supplement permutes
the orbit. When that intersection is its Sylow Borel, the orbit has a normal
Sylow two-subgroup. Its embedded core is normal in M_Z, so S∩K lies in Q₁.
Conversely C.2.4(1) reconstructs a genuine chi-zero block from containment of
the component Sylow in Q₁; nonsolvability excludes the A₃ block.

Thus for the selected constrained component, the natural L₂/A₅ block branch
is equivalent to S_L≤Q₁. The original and exchanged consumers split into
the complete rank-one alternative or a non-rank-one C.2.7 input on the
literal Q₁ and core-to-star map. No recognition of the remaining star rows
is asserted. General local-family orbit invariance, FF reconstruction and
the remaining parabolic clauses stay with this catalogue owner. Original
15.1.14 remains explicit for qt-e-1514-global-thompson-residual, with final
discharge by qt-e-15122-pre-exclusion-catalogue; quotient assembly stays
with qt-e-1515-constrained-linear-quotient.

Source: Aschbacher--Smith 15.1.20, pp.1094--1095; C.2.4(1), p.144.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private theorem marked_orbit_normalized_of_cComponent
    (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hSyl : Chapter1.IsSylowIn 2 d.S d.G1)
    {K B : Subgroup G} (hK : K ≤ d.G1)
    (hcomp : (K.subgroupOf d.G1).IsCComponent)
    (hinv : d.MZ ⊓ normalizer (K : Set G) ≤ normalizer (B : Set G)) :
    d.MZ ≤ normalizer (conjugateSpanBy B d.S : Set G) := by
  let := h.elementary
  let R := (pResidual 2 d.MZ).map d.MZ.subtype
  have hRM : R ≤ d.MZ := map_subtype_le _
  have hRG : R ≤ d.G1 := hRM.trans inf_le_left
  let e := (subgroupOfEquivOfLe hRG).symm
  have hp : IsPPerfect 2 (R.subgroupOf d.G1) :=
    (isPPerfect_embedded_pResidual 2 d.MZ).of_surjective e.toMonoidHom e.surjective
  have hsqtk : IsSQTK KnownSimple.IsKnownSimple d.G1 :=
    caseI_centralizer_sqtk hG d.Z1 d.Z1_ne_bot
    ((IsElementaryAbelian.isPGroup 2 V).to_le (d.Z1_le_fixed.trans inf_le_left))
  have hquot : IsSQTK KnownSimple.IsKnownSimple (d.G1 ⧸ pCore 2 d.G1) := by
    refine ⟨?_,hsqtk.isKGroup.quotient (pCore 2 d.G1)⟩
    intro q hq ho
    let : Fact q.Prime := ⟨hq⟩
    exact (primeRank_quotient_le_of_isTwoGroup q ho (pCore 2 d.G1) pCore_isPGroup).trans
      (hsqtk.stronglyQuasithin q hq ho)
  have hn0 := Chapter1.Section02.twoPerfect_normalizes_cComponent_source hquot hcomp hp
  have hnK := (map_mono (f := d.G1.subtype) hn0).trans
    ((K.subgroupOf d.G1).le_normalizer_map d.G1.subtype)
  rw [map_subgroupOf_eq_of_le hRG,map_subgroupOf_eq_of_le hK] at hnK
  have hnB : R ≤ normalizer (B : Set G) := (le_inf hRM hnK).trans hinv
  have hnR : d.MZ ≤ normalizer (R : Set G) := d.MZ.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image d.MZ (pResidual 2 d.MZ))
  have hSM : d.S ≤ d.MZ := by
    have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hu ▸ Set.mem_singleton Mc
    intro x hx
    exact ⟨d.S_le_G1 hx,hMc.2 (fun z hz =>
      (centralInvolutions_le_centralizer_sylow T hz x (d.S_le_T hx)).symm)⟩
  obtain ⟨P,hP⟩ := hSyl
  obtain ⟨Q,hQ⟩ := P.exists_map_subtype_eq_of_le
    (show d.MZ ≤ d.G1 from inf_le_left) (hP ▸ hSM)
  have he : R ⊔ d.S = d.MZ := by
    have hh := congrArg (map d.MZ.subtype) (pResidual_sup_sylow_eq_top Q)
    simpa only [Subgroup.map_sup,hQ,hP,←MonoidHom.range_eq_map,range_subtype] using hh
  rw [←he]
  exact sup_le (TwoOrbitSpan.normalizes_span _ _ R hnB (hSM.trans hnR))
    (le_normalizer_conjugateSpanBy _ _)


/-- The normal Sylow subgroup of the actual invariant Borel orbit places S∩K in Q₁. -/
theorem localFamily_sylow_le_radical_of_borel_orbit
    (d : CaseIComponentData T M Mc V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hb : IsShort K)
    (hle : d.orbitSylowBorel K ≤ d.MZ)
    (hn : d.MZ ≤ normalizer (d.orbitSylowBorel K : Set G)) :
    d.S ⊓ K ≤ d.Q1 := by
  let B := d.orbitSylowBorel K
  obtain ⟨_,⟨P,hP⟩,_⟩ := d.localFamily_orbitBorel_structure hK hq hb
  have hSB : d.S ⊓ K ≤ B :=
    (le_inf inf_le_right (d.S ⊓ K).le_normalizer).trans (le_conjugateSpanBy _ _)
  have hp : IsPGroup 2 ((d.S ⊓ K).subgroupOf B) :=
    (T.isPGroup'.to_le (inf_le_left.trans d.S_le_T)).comap_subtype
  obtain ⟨R,hR⟩ := hp.exists_le_sylow
  have hPR : (P : Subgroup B) ≤ R := by
    rw [hP]
    exact pCore_isPGroup.le_sylow_of_normal R
  have he : (R : Subgroup B) = (P : Subgroup B) := P.is_maximal' R.isPGroup' hPR
  have hcore : d.S ⊓ K ≤ B.pCoreIn 2 := by
    have hh := map_mono (f := B.subtype) hR
    rw [he,hP,map_subgroupOf_eq_of_le hSB] at hh
    exact hh
  exact hcore.trans (pCoreIn_mono_of_normalizes hle hn)

/-- An ambient C-component with the literal marked Borel has its Sylow subgroup in Q₁. The component hypothesis is essential to the orbit argument. -/
theorem localFamily_rankOne_sylow_le_radical_of_cComponent
    (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hSyl : Chapter1.IsSylowIn 2 d.S d.G1)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hcomp : (K.subgroupOf d.G1).IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hb : IsShort K)
    (he : d.MZ ⊓ K = (normalizer ((d.S ⊓ K).subgroupOf K : Set K)).map K.subtype) :
    d.S ⊓ K ≤ d.Q1 := by
  have heB : d.localSylowBorel K = d.MZ ⊓ K := (d.localSylowBorel_eq K).trans he.symm
  have hSM : d.S ≤ d.MZ := by
    have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hu ▸ Set.mem_singleton Mc
    intro x hx
    exact ⟨d.S_le_G1 hx,hMc.2 (fun z hz =>
      (centralInvolutions_le_centralizer_sylow T hz x (d.S_le_T hx)).symm)⟩
  have hle : d.orbitSylowBorel K ≤ d.MZ :=
    conjugateSpanBy_le (heB ▸ inf_le_left) (hSM.trans d.MZ.le_normalizer)
  have hn : d.MZ ≤ normalizer (d.orbitSylowBorel K : Set G) := by
    apply d.marked_orbit_normalized_of_cComponent hG h hu hSyl hK.1 hcomp
    rw [heB]
    exact (le_inf (inf_le_left.trans d.MZ.le_normalizer) inf_le_right).trans
      inf_normalizer_le_normalizer_inf
  exact d.localFamily_sylow_le_radical_of_borel_orbit hK hq hb hle hn

open ChapterC.CatalogueFullSylow

/-- C.2.4(1) on the original G₁ reconstructs a rank-one block from a full Sylow subgroup in Q₁, without characteristic two for G₁. -/
theorem constrained_component_rankOne_of_sylow_le_radical
  (d : CaseIComponentData T M Mc V) (h : PreparedChosenModule T M V)
  (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
  (hodd : pPrimeCore 2 d.G1 = ⊥)
  (hQne : d.Q1 ≠ ⊥)
  (hcontrol : d.Q1.characteristicNormalizerClosure ≤ Mc)
  (hnormalizer : d.G1 ⊓ normalizer (d.Q1 : Set G) = d.MZ)
  {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn d.G1)
  (hq : IsQuasisimple (B ⧸ pCore 2 B))
  (hfit : generalizedFitting B = pCore 2 B) (hout : ¬ B ≤ d.MZ)
  (P : Sylow 2 B) (hP : (P : Subgroup B).map B.subtype ≤ d.Q1) :
  (∃ n : ℕ, IsL2EvenBlock B n) ∨ IsAlternatingBlock B 5 := by
  let := h.elementary
  let K := B.subgroupOf d.G1
  let R := d.Q1.subgroupOf d.G1
  let N := d.MZ.subgroupOf d.G1
  let e : K ≃* B := subgroupOfEquivOfLe hB.1
  let := hq
  let hqK : IsQuasisimple (K ⧸ pCore 2 K) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hf : generalizedFitting K = pCore 2 K := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_generalizedFitting_equiv,pCore_map_iso,hfit]
  have hQG := d.Q1_le_MZ.trans (show d.MZ ≤ d.G1 from inf_le_left)
  let P0 : Sylow 2 K := P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hP0 : (P0 : Subgroup K).map K.subtype ≤ R := by
    rintro _ ⟨x,⟨y,hy,rfl⟩,rfl⟩
    exact hP (mem_map_of_mem B.subtype hy)
  have hb : IsChiZeroBlock B :=
    (@constrained_component_chiZero_of_full_sylow d.G1 inferInstance inferInstance
      (caseI_centralizer_sqtk hG d.Z1 d.Z1_ne_bot
        ((IsElementaryAbelian.isPGroup 2 V).to_le (d.Z1_le_fixed.trans inf_le_left)))
      R N K
      (caseI_intrinsic_core_radical d.G1 d.MZ inf_le_left hQne hnormalizer)
      (caseI_intrinsic_characteristic_control d.G1 Mc d.Q1 hQG hcontrol)
      hB.2 hqK hodd hf
      (fun hh => hout (fun b hb => hh (show (⟨b,hB.1 hb⟩ : d.G1) ∈ K from hb)))
      P0 hP0).of_mulEquiv e
  rcases hb with hb | hb | hb
  · exact Or.inl hb
  · obtain ⟨f⟩ := hb.equiv_alternatingFour
    let : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup_fin_four_isSolvable
    let : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective (f := f.toMonoidHom) f.injective
    exact (hB.2.not_isSolvable
      (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)).elim
  · exact Or.inr hb

/-- The selected original component satisfies the genuine full-Sylow block conclusion. -/
theorem PreExclusionSource.constrained_rankOne_block_of_sylow_le_radical
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hfit : generalizedFitting d.L = pCore 2 d.L) (hSL : d.SL ≤ d.Q1) :
    (∃ n : ℕ, IsL2EvenBlock d.L n) ∨ IsAlternatingBlock d.L 5 := by
  obtain ⟨P,hP⟩ := ComponentModels.source20_sylow_intersection s.local_component
  exact d.constrained_component_rankOne_of_sylow_le_radical h hG
    s.odd_core s.core_nontrivial s.characteristic_control s.core_normalizer
    d.L_component s.quasisimple hfit d.L_not_le_MZ P (hP.le.trans hSL)

/-- The same full-Sylow conclusion for either exchanged-plane size. -/
theorem ExchangedSource.constrained_rankOne_block_of_sylow_le_radical
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (h : PreparedChosenModule T M V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hfit : generalizedFitting d.L = pCore 2 d.L) (hSL : d.SL ≤ d.Q1) :
    (∃ n : ℕ, IsL2EvenBlock d.L n) ∨ IsAlternatingBlock d.L 5 := by
  obtain ⟨P,hP⟩ := ComponentModels.source20_sylow_intersection s.local_component
  exact d.constrained_component_rankOne_of_sylow_le_radical h hG
    s.odd_core s.core_nontrivial s.characteristic_control s.core_normalizer
    d.L_component s.quasisimple hfit d.L_not_le_MZ P (hP.le.trans hSL)

/-- Before exchanged selection, the actual rank-one blocks are exactly the full-Sylow branch. -/
theorem PreExclusionSource.constrained_rankOne_block_iff_sylow_le_radical
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hfit : generalizedFitting d.L = pCore 2 d.L) :
    ((∃ n : ℕ, IsL2EvenBlock d.L n) ∨ IsAlternatingBlock d.L 5) ↔ d.SL ≤ d.Q1 := by
  constructor
  · intro hb
    have hk : d.L ∈ Chapter1.LIn d.G1 d.S := ⟨d.L_component.1,s.local_component⟩
    have hh : IsShort d.L ∧
        d.ML = (normalizer (d.SL.subgroupOf d.L : Set d.L)).map d.L.subtype := by
      rcases hb with ⟨n,hb⟩ | hb
      · exact ⟨hb.2.1,s.constrained_linearTwo_borel (h := h) hG hM hu hne hmany hres hb⟩
      · exact ⟨hb.2.1,(d.localFamily_alternatingFive_borel h hM.1.2 hu hk
          s.quasisimple d.L_not_le_MZ hb).2⟩
    exact d.localFamily_rankOne_sylow_le_radical_of_cComponent hG h hu s.centralizer_sylow
      hk d.L_component.2 s.quasisimple hh.1 hh.2
  · exact s.constrained_rankOne_block_of_sylow_le_radical (h := h) hG hfit

/-- The rank-one/full-Sylow equivalence for the later exchanged source. -/
theorem ExchangedSource.constrained_rankOne_block_iff_sylow_le_radical
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (h : PreparedChosenModule T M V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hfit : generalizedFitting d.L = pCore 2 d.L) :
    ((∃ n : ℕ, IsL2EvenBlock d.L n) ∨ IsAlternatingBlock d.L 5) ↔ d.SL ≤ d.Q1 := by
  constructor
  · intro hb
    have hk : d.L ∈ Chapter1.LIn d.G1 d.S := ⟨d.L_component.1,s.local_component⟩
    have hh : IsShort d.L ∧
        d.ML = (normalizer (d.SL.subgroupOf d.L : Set d.L)).map d.L.subtype := by
      rcases hb with ⟨n,hb⟩ | hb
      · exact ⟨hb.2.1,s.constrained_linearTwo_borel h hG hM hu hne hmany hres hb⟩
      · exact ⟨hb.2.1,(d.localFamily_alternatingFive_borel h hM.1.2 hu hk
          s.quasisimple d.L_not_le_MZ hb).2⟩
    exact d.localFamily_rankOne_sylow_le_radical_of_cComponent hG h hu s.centralizer_sylow
      hk d.L_component.2 s.quasisimple hh.1 hh.2
  · exact s.constrained_rankOne_block_of_sylow_le_radical h hG hfit

/-- The original source splits into the complete rank-one alternative and a genuinely non-rank-one C.2.7 branch. All local orbit premises are discharged. -/
theorem PreExclusionSource.constrained_disjoint_rankOne_or_star
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hfit : generalizedFitting d.L = pCore 2 d.L) :
    (d.SL ≤ d.Q1 ∧ d.ConstrainedRankOneAlternative) ∨
      (¬ d.SL ≤ d.Q1 ∧
        ¬ ((∃ n : ℕ, IsL2EvenBlock d.L n) ∨ IsAlternatingBlock d.L 5) ∧
        ∃ hnL : d.Q1 ≤ normalizer (d.L : Set G),
          StarModels.Model (starImage d.L d.Q1 d.L) ∧
            (coreToStar hnL).ker ≤ center (d.L ⧸ pCore 2 d.L) ∧
            (Nat.card (center (d.L ⧸ pCore 2 d.L)) = 1 ∨
              Nat.card (center (d.L ⧸ pCore 2 d.L)) = 3)) := by
  classical
  by_cases hSL : d.SL ≤ d.Q1
  · refine Or.inl ⟨hSL,?_⟩
    rcases s.constrained_rankOne_block_of_sylow_le_radical (h := h) hG hfit hSL with ⟨n,hb⟩ | hb
    · exact s.constrained_rankOne_of_linearTwo (h := h) hG hempty hM hJ hu hne hmany hres hb
    · exact s.constrained_rankOne_of_alternatingFive (h := h) hG hempty hM hJ hu hb
  · have hb : ¬ ((∃ n : ℕ, IsL2EvenBlock d.L n) ∨ IsAlternatingBlock d.L 5) :=
      fun hb => hSL ((s.constrained_rankOne_block_iff_sylow_le_radical (h := h) hG hM hu hne hmany hres hfit).mp hb)
    have hi := s.constrained_input_of_not_contains_sylow (h := h) hG hu hfit hSL
    exact Or.inr ⟨hSL,hb,hi.normalizes,star_model_from_source hi,
      coreToStar_ker_central_from_source hi,coreQuotient_center_card_from_source hi⟩

/-- The disjoint branch reduction retains both exchanged-plane sizes and the literal core-to-star map. -/
theorem ExchangedSource.constrained_disjoint_rankOne_or_star
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (h : PreparedChosenModule T M V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hfit : generalizedFitting d.L = pCore 2 d.L) :
    (d.SL ≤ d.Q1 ∧ d.ConstrainedRankOneAlternative) ∨
      (¬ d.SL ≤ d.Q1 ∧
        ¬ ((∃ n : ℕ, IsL2EvenBlock d.L n) ∨ IsAlternatingBlock d.L 5) ∧
        ∃ hnL : d.Q1 ≤ normalizer (d.L : Set G),
          StarModels.Model (starImage d.L d.Q1 d.L) ∧
            (coreToStar hnL).ker ≤ center (d.L ⧸ pCore 2 d.L) ∧
            (Nat.card (center (d.L ⧸ pCore 2 d.L)) = 1 ∨
              Nat.card (center (d.L ⧸ pCore 2 d.L)) = 3)) := by
  classical
  by_cases hSL : d.SL ≤ d.Q1
  · refine Or.inl ⟨hSL,?_⟩
    rcases s.constrained_rankOne_block_of_sylow_le_radical h hG hfit hSL with ⟨n,hb⟩ | hb
    · exact s.constrained_rankOne_of_linearTwo h hG hempty hM hJ hu hne hmany hres hb
    · exact s.constrained_rankOne_of_alternatingFive hG hempty hM hJ hu h hb
  · have hb : ¬ ((∃ n : ℕ, IsL2EvenBlock d.L n) ∨ IsAlternatingBlock d.L 5) :=
      fun hb => hSL ((s.constrained_rankOne_block_iff_sylow_le_radical h hG hM hu hne hmany hres hfit).mp hb)
    have hi := s.constrained_input_of_not_contains_sylow hG h hu hfit hSL
    exact Or.inr ⟨hSL,hb,hi.normalizes,star_model_from_source hi,
      coreToStar_ker_central_from_source hi,coreQuotient_center_card_from_source hi⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
