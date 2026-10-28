module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.SporadicRefinement.HigmanSimsSeed

/-!
# The actual moving core in the original HS residual

The invariant seed retains a surjection onto the concrete elementary-eight
normalizer, with a central two-group kernel. Perfectness of that normalizer
makes the same map surjective on the seed's perfect residual K. The quotient
K/O₂(K) remains the literal SL₃(2), and K still escapes M_Z in L(G₁,S).

The model order-seven action now shows that [O₂(K),K] maps onto the actual
C₄³ core. In particular it is not elementary abelian. This is combined with
the proved obstruction to K normalizing any nontrivial characteristic subgroup
of the full S. The marker application keeps the original d, Z₁, row and prime.
It supplies the concrete core obstruction required by the HS paragraph of
15.1.22, including central covers; it does not assert the remaining MS
contradiction. That contradiction, the Ru exclusion, the binary linear
source family and final Ordinary22 assembly remain with
qt-e-15122-ordinary-pre-exclusion. The independent full local-family
nonblock premise retains producer qt-e-1515-constrained-source-catalogue
and final discharge by qt-e-15122-pre-exclusion-catalogue.

Source: Aschbacher--Smith 15.1.22, printed p.1100 of refs/quasithin.pdf;
GLS3 Table 5.3m for the concrete HS normalizer.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The escaping perfect residual retains its central covering of the actual
HS normalizer, whose C₄³ image rules out an elementary moving core. -/
theorem PreExclusionSource.higmanSims_escaping_local_core
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : (d.L ⧸ pCore 2 d.L) ≃* Sporadic.LeechRelated.HS.Carrier) :
    ∃ B K : Subgroup G, B ≤ d.L ∧ d.SL ≤ B ∧
      d.S ≤ normalizer (B : Set G) ∧ d.ML ⊔ B = d.L ∧
      (solvableResidual B).map B.subtype = K ∧ Group.IsPerfect K ∧
      d.S ≤ normalizer (K : Set G) ∧ K ∈ Chapter1.LIn d.G1 d.S ∧
      generalizedFitting K = pCore 2 K ∧ ¬ K ≤ d.MZ ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
      (∃ f : K →* Sporadic.LeechRelated.HS.BlockNormalizer.baseNormalizer,
        Function.Surjective f ∧ IsPGroup 2 f.ker ∧ f.ker ≤ center K) ∧
      ¬ IsElementaryAbelian 2 (⁅pCore 2 K, (⊤ : Subgroup K)⁆ : Subgroup K) := by
  obtain ⟨B,hBL,hSB,hnB,hself,hgen,hout,u,huSurj,huKer,huCentral⟩ :=
    s.higmanSims_escaping_normalizer_cover (h := h) hG hM hu hL e
  obtain ⟨q⟩ := Sporadic.LeechRelated.HS.BlockNormalizer.baseNormalizer_quotient_of_surjective
    Sporadic.LeechRelated.HS.BlockNormalizer.baseNormalizer_action_surjective
  let g := q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2
    Sporadic.LeechRelated.HS.BlockNormalizer.baseNormalizer))
  have hg : Function.Surjective g := q.surjective.comp (QuotientGroup.mk'_surjective _)
  have hgKer : g.ker = pCore 2 Sporadic.LeechRelated.HS.BlockNormalizer.baseNormalizer := by
    rw [MonoidHom.ker_comp_of_injective _ _ q.injective,QuotientGroup.ker_mk']
  let f := g.comp u
  have hf : Function.Surjective f := hg.comp huSurj
  have hk : IsPGroup 2 f.ker := by
    rw [←MonoidHom.comap_ker,hgKer]
    exact pCore_isPGroup.comap_of_ker_isPGroup u huKer
  let D := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
  let : IsSimpleGroup D := Atlas.Comparisons.Exceptional.sl3Two_simple
  let : Group.IsPerfect D := Atlas.sl_perfect (F := ZMod 2) 3 (by decide)
  let : IsQuasisimple D :=
    { simple := ((QuotientGroup.quotientMulEquivOfEq
        Atlas.Comparisons.Exceptional.sl3Two_center_eq_bot).trans QuotientGroup.quotientBot).isSimpleGroup }
  have hOD : pCore 2 D = ⊥ := bot_unique
    ((IsQuasisimple.pCore_le_center (G := D) 2).trans
      Atlas.Comparisons.Exceptional.sl3Two_center_eq_bot.le)
  let eB : (B ⧸ pCore 2 B) ≃* D := (f.pCoreQuotientEquiv hf hk).trans
    ((QuotientGroup.quotientMulEquivOfEq hOD).trans QuotientGroup.quotientBot)
  let : Group.IsPerfect (B ⧸ pCore 2 B) :=
    Group.IsPerfect.ofSurjective (f := eB.symm.toMonoidHom) eB.symm.surjective
  let R := solvableResidual B
  let K := R.map B.subtype
  let er : R ≃* K := R.equivMapOfInjective B.subtype B.subtype_injective
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := er.toMonoidHom) er.surjective
  let eK : (K ⧸ pCore 2 K) ≃* D :=
    ((QuotientGroup.congr _ _ er.symm (pCore_map_iso 2 er.symm)).trans
      (solvableResidualPCoreQuotientEquiv 2)).trans eB
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv eK.symm
  let : Nontrivial (K ⧸ pCore 2 K) := eK.surjective.nontrivial
  let : Nontrivial K := (QuotientGroup.mk'_surjective (pCore 2 K)).nontrivial
  have hselfR := normal_core_selfCentralizing hself R
  have hselfK : centralizer (pCore 2 K : Set K) ≤ pCore 2 K :=
    er.symm.toMonoidHom.centralizer_pCore_le_of_surjective_pKernel er.symm.surjective
      (by rw [er.symm.toMonoidHom.ker_eq_bot er.symm.injective]
          exact IsPGroup.of_card (n := 0) (by simp)) hselfR
  have hnK : d.S ≤ normalizer (K : Set G) := hnB.trans
    (normalizer_le_normalizer_characteristic_image B R)
  have hKG : K ≤ d.G1 := (map_subtype_le _).trans (hBL.trans d.L_component.1)
  have hfamily : K ∈ Chapter1.LIn d.G1 d.S := by
    apply Chapter1.mem_LIn_of_normalized_perfect s.centralizer_sylow hKG hnK
    intro hb
    have hc : pCore 2 K = ⊥ := (map_eq_bot_iff_of_injective _ K.subtype_injective).mp hb
    obtain ⟨x,hx⟩ := exists_ne (1 : K)
    apply hx
    apply mem_bot.mp
    exact hc ▸ hselfK (by
      intro y hy
      have hy1 : y = 1 := mem_bot.mp (hc ▸ hy)
      simp only [hy1,mul_one,one_mul])
  obtain ⟨Q,hQ⟩ := s.component_sylow.restrict hSB hBL
  have hRS : R ⊔ (Q : Subgroup B) = ⊤ := by
    apply top_unique
    rw [←pResidual_sup_sylow_eq_top Q]
    have hPR : pResidual 2 B ≤ R := sInf_le ⟨inferInstance,
      quotient_solvableResidual_isPGroup_of_perfect_pCore_quotient 2⟩
    exact sup_le_sup_right hPR _
  have hBS : K ⊔ d.SL = B := by
    have hh := congrArg (Subgroup.map B.subtype) hRS
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype,hQ] at hh
    exact hh
  let ur := u.comp R.subtype
  have hur : Function.Surjective ur := by
    intro y
    have hy : y ∈ R.map u := by
      change y ∈ (solvableResidual B).map u
      rw [map_solvableResidual_eq u huSurj,solvableResidual_eq_top]
      trivial
    obtain ⟨x,hx,he⟩ := hy
    exact ⟨⟨x,hx⟩,he⟩
  let uk := ur.comp er.symm.toMonoidHom
  have huk : Function.Surjective uk := hur.comp er.symm.surjective
  have hukKer : IsPGroup 2 uk.ker := by
    change IsPGroup 2 ((u.comp R.subtype).comp er.symm.toMonoidHom).ker
    rw [←MonoidHom.comap_ker,←MonoidHom.comap_ker]
    exact (huKer.comap_of_injective _ R.subtype_injective).comap_of_injective _ er.symm.injective
  have hukCentral : uk.ker ≤ center K := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply er.symm.injective
    apply Subtype.ext
    have hc : (er.symm x : B) ∈ center B := huCentral hx
    simpa only [map_mul,coe_mul] using mem_center_iff.mp hc (er.symm y)
  have hSM : d.SL ≤ d.MZ := by
    have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hu ▸ Set.mem_singleton Mc
    apply le_inf (d.SL_le_L.trans d.L_component.1)
    apply d.SL_le_S.trans (d.S_le_T.trans ?_)
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  exact ⟨B,K,hBL,hSB,hnB,hgen,rfl,inferInstance,hnK,hfamily,
    generalizedFitting_eq_pCore_of_selfCentralizing 2 hselfK,
    fun hh => hout (hBS ▸ sup_le hh hSM),⟨eK⟩,⟨uk,huk,hukKer,hukCentral⟩,
    Sporadic.LeechRelated.HS.BlockNormalizer.moving_core_not_elementary uk huk hukKer⟩



/-- The same original HS residual has both the concrete moving-core obstruction
and the full-S characteristic-subgroup obstruction used in the source argument. -/
theorem PreExclusionSource.higmanSims_local_core_obstruction
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : (d.L ⧸ pCore 2 d.L) ≃* Sporadic.LeechRelated.HS.Carrier) :
    ∃ K : Subgroup G, K ≤ d.L ∧ Group.IsPerfect K ∧
      d.S ≤ normalizer (K : Set G) ∧ K ∈ Chapter1.LIn d.G1 d.S ∧
      generalizedFitting K = pCore 2 K ∧ ¬ K ≤ d.MZ ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
      (∃ f : K →* Sporadic.LeechRelated.HS.BlockNormalizer.baseNormalizer,
        Function.Surjective f ∧ IsPGroup 2 f.ker ∧ f.ker ≤ center K) ∧
      ¬ IsElementaryAbelian 2 (⁅pCore 2 K, (⊤ : Subgroup K)⁆ : Subgroup K) ∧
      ∀ C : Subgroup d.S, C.Characteristic → C ≠ ⊥ →
        ¬ K ≤ normalizer (C.map d.S.subtype : Set G) := by
  obtain ⟨B,K,hBL,_,_,_,hres,hperf,hn,hfamily,hfit,hout,eqK,hcover,hne⟩ :=
    s.higmanSims_escaping_local_core (h := h) hG hM hu hL e
  let := hperf
  have hKL : K ≤ d.L := hres ▸ (map_subtype_le _).trans hBL
  exact ⟨K,hKL,hperf,hn,hfamily,hfit,hout,eqK,hcover,hne,
    s.perfect_escape_not_normalize_characteristic (h := h) hG hempty hu
      (hKL.trans d.L_component.1) hout⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
variable {G : Type*} [Group G] [Finite G]

/-- The original marker supplies the actual HS local residual and the full-S
characteristic obstruction at the same component, row, Z₁ and source prime. -/
theorem PreparedChosenModule.source_preExclusion_higmanSims_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (IsComponent d.G1 (d.L.subgroupOf d.G1) →
        (d.L ⧸ pCore 2 d.L) ≃* Sporadic.LeechRelated.HS.Carrier →
        ∃ K : Subgroup G, K ≤ d.L ∧ Group.IsPerfect K ∧
          d.S ≤ normalizer (K : Set G) ∧ K ∈ Chapter1.LIn d.G1 d.S ∧
          generalizedFitting K = pCore 2 K ∧ ¬ K ≤ d.MZ ∧
          Nonempty ((K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
          (∃ f : K →* Sporadic.LeechRelated.HS.BlockNormalizer.baseNormalizer,
            Function.Surjective f ∧ IsPGroup 2 f.ker ∧ f.ker ≤ center K) ∧
          ¬ IsElementaryAbelian 2 (⁅pCore 2 K, (⊤ : Subgroup K)⁆ : Subgroup K) ∧
          ∀ C : Subgroup d.S, C.Characteristic → C ≠ ⊥ →
            ¬ K ≤ normalizer (C.map d.S.subtype : Set G)) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hL e =>
    s.higmanSims_local_core_obstruction (h := h) hG hempty hM hu hL e⟩

end CFSG.Quasithin.Chapter15.Section01
