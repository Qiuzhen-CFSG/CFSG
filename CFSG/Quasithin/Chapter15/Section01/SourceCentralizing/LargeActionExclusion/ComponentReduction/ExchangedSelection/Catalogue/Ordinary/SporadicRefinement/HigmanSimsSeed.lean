module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.SporadicRefinement.RudvalisQuintic
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.CentralCoverSeed
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.CentralCoverCore
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.ThreeRank
public import Theory.GroupTheory.GeneralizedFitting.ComponentCoprimeRankNormal
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.SolvableResidual.PerfectQuotient
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.NormalizedPerfect
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# The original Higman--Sims local residual

Cubic rank makes the ordinary HS component normal in G₁. The actual
Sylow-fixing involution and the central-cover seed therefore give an
S-invariant subgroup B generating L with M_L and escaping M_Z. Its perfect
residual K retains characteristic two and has literal quotient
K/O₂(K) ≃ SL₃(2). The Sylow supplement proves K still escapes M_Z;
normality in KS places it in the full local family L(G₁,S).

Source 14.1.6(3), with the original empty faithful family and singleton
partner hypothesis, excludes every nontrivial characteristic subgroup of
the full S normalized by K. The marker consumer retains the same d, Z₁,
row and prime, and all central covers. No exchanged-component hypothesis
or characteristicity transfer from S∩L to S is used.

This constructs the local residual and its characteristic obstruction in
original 15.1.22, printed p.1100 of refs/quasithin.pdf. The core-geometry
contradiction for this residual, the Ru branch and final Ordinary22
assembly remain with qt-e-15122-ordinary-pre-exclusion. The original
15.1.14 premise in the marker consumer remains with the final catalogue
owner qt-e-15122-pre-exclusion-catalogue.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

private theorem normal_of_odd_rank
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {r : ℕ} (hr : r.Prime) (ho : Odd r) (hR : 2 ≤ primeRank r d.L) :
    (d.L.subgroupOf d.G1).Normal := by
  let : Fact r.Prime := ⟨hr⟩
  let := h.elementary
  have hsq : IsSQTK KnownSimple.IsKnownSimple d.G1 := caseI_centralizer_sqtk hG d.Z1 d.Z1_ne_bot
    ((IsElementaryAbelian.isPGroup 2 V).to_le (d.Z1_le_fixed.trans inf_le_left))
  let e := subgroupOfEquivOfLe (show d.L ≤ d.G1 from d.L_component.1)
  have hZ : IsPGroup 2 (center d.L) := by
    rw [(s.ordinary hL).center_eq]
    exact pCore_isPGroup
  have hZ' : IsPGroup 2 (center (d.L.subgroupOf d.G1)) := hZ.of_equiv (centerCongr e.symm)
  obtain ⟨n,hn⟩ := hZ'.exists_card_eq
  have hc : Nat.Coprime r (Nat.card (center (d.L.subgroupOf d.G1))) := by
    rw [hn]
    exact (Nat.coprime_two_right.mpr ho).pow_right n
  have hR' : 2 ≤ primeRank r (d.L.subgroupOf d.G1) := by
    rwa [primeRank_equiv r e]
  exact hL.normal_of_coprime_center_primeRank r hc (by
    have hh := hsq.stronglyQuasithin r hr ho
    omega)

private theorem marked_fixer
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) :
    ∃ P : Sylow 2 d.L, (P : Subgroup d.L).map d.L.subtype = d.SL ∧
      ∃ α : MulAut d.L, α^2=1 ∧ α≠1 ∧ (∀ x ∈ P, α x=x) ∧
        α.fixedSubgroup.map d.L.subtype ≤ Mc := by
  obtain ⟨z,hz,hzne⟩ := (Subgroup.bot_or_exists_ne_one (centralInvolutions T)).resolve_left
    (centralInvolutions_ne_bot_of_maximal_local T hM.1)
  obtain ⟨α,ha,_⟩ := s.ordinary_marked_model (h := h) hL hz hzne
  obtain ⟨R,hR,h115⟩ := d.ordinary_involution_inputs hG hu h s.centralizer_sylow
  have hzc : z ∈ centralizer (d.S : Set G) := by
    intro x hx
    exact (h115 z hz hzne).central x (hR.symm ▸ hx)
  have hz2 : z*z=1 := by
    simpa only [(h115 z hz hzne).involution,pow_two] using pow_orderOf_eq_one z
  have hα2 : α^2=1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change (α (α x) : G) = x
    rw [ha,ha]
    calc
      z*(z*(x:G)*z⁻¹)*z⁻¹ = (z*z)*x*(z*z)⁻¹ := by group
      _ = x := by rw [hz2]; simp
  have hαne : α ≠ 1 := by
    intro he
    have hc : z ∈ centralizer (d.L : Set G) := by
      intro x hx
      have hh := ha (⟨x,hx⟩:d.L)
      rw [he] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
    have hzbot : z ∈ (⊥ : Subgroup G) := (s.ordinary hL).central_faithful ▸ ⟨hz,hc⟩
    exact hzne (mem_bot.mp hzbot)
  obtain ⟨P,hP⟩ := s.component_sylow
  refine ⟨P,hP,α,hα2,hαne,?_,?_⟩
  · intro x hx
    apply Subtype.ext
    rw [ha]
    exact mul_inv_eq_iff_eq_mul.mpr
      (hzc x (d.SL_le_S (hP ▸ mem_map_of_mem d.L.subtype hx))).symm
  · rintro _ ⟨x,hx,rfl⟩
    apply (h115 z hz hzne).centralizer_le
    apply mem_centralizer_singleton_iff.mpr
    have he := ha x
    rw [(MulAut.mem_fixedSubgroup _ _).mp hx] at he
    exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm


private theorem seed_normalized
    (hn : d.S ≤ normalizer (d.L : Set G))
    (P : Sylow 2 d.L) (hP : (P : Subgroup d.L).map d.L.subtype = d.SL)
    (B : Subgroup d.L)
    (hi : ∀ a : MulAut d.L, (P : Subgroup d.L).map a.toMonoidHom = P →
      B.map a.toMonoidHom = B) : d.S ≤ normalizer (B.map d.L.subtype : Set G) := by
  have hP' : (P : Subgroup d.L)=d.SL.subgroupOf d.L := by
    apply map_injective d.L.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le d.SL_le_L]
  intro t ht
  let a := d.L.normalizerMonoidHom ⟨t,hn ht⟩
  have ha : (P : Subgroup d.L).map a.toMonoidHom = P := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      rw [hP'] at hx ⊢
      change t * (x : G) * t⁻¹ ∈ d.S ⊓ d.L
      exact ⟨d.S.mul_mem (d.S.mul_mem ht hx.1) (d.S.inv_mem ht),(a x).property⟩
    · exact (Nat.card_congr (a.subgroupMap (P : Subgroup d.L)).toEquiv).le
  have hb := hi a ha
  have hm : (B.map d.L.subtype).map (MulAut.conj t).toMonoidHom = B.map d.L.subtype := by
    rw [map_map]
    have he : (MulAut.conj t).toMonoidHom.comp d.L.subtype = d.L.subtype.comp a.toMonoidHom := by
      ext x
      rfl
    rw [he,←map_map,hb]
  exact (mem_normalizer_iff_map_conj_eq).mpr hm

/-- Cubic rank forces normality of the original HS component, retaining its central cover. -/
theorem PreExclusionSource.higmanSims_normal
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : (d.L ⧸ pCore 2 d.L) ≃* Sporadic.LeechRelated.HS.Carrier) :
    (d.L.subgroupOf d.G1).Normal := by
  apply normal_of_odd_rank (h := h) s hG hL (by decide : Nat.Prime 3) (by decide)
  rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 d.L) pCore_isPGroup,
    primeRank_equiv 3 e]
  exact Sporadic.LeechRelated.HS.ThreeRank.two_le_primeRank

/-- The actual invariant HS seed escapes the original M_Z and generates
with M_L, through every retained central two-cover. -/
theorem PreExclusionSource.higmanSims_escaping_seed
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : (d.L ⧸ pCore 2 d.L) ≃* Sporadic.LeechRelated.HS.Carrier) :
    ∃ B : Subgroup G, B ≤ d.L ∧ d.SL ≤ B ∧
      d.S ≤ normalizer (B : Set G) ∧
      centralizer (pCore 2 B : Set B) ≤ pCore 2 B ∧
      d.ML ⊔ B = d.L ∧ ¬ B ≤ d.MZ ∧
      ∃ f : B →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
        Function.Surjective f ∧ IsPGroup 2 f.ker := by
  let : IsQuasisimple d.L := IsQuasisimple.of_mulEquiv (hG := hL.2)
    (subgroupOfEquivOfLe d.L_component.1)
  let ez := (QuotientGroup.quotientMulEquivOfEq (s.ordinary hL).center_eq).trans e
  obtain ⟨P,hP,a,ha,hne,hfix,hfixed⟩ := marked_fixer (h := h) s hG hM hu hL
  obtain ⟨B,hPB,hi,hgen,hself,f,hf,hk⟩ :=
    Sporadic.LeechRelated.HS.BlockNormalizer.exists_sylow_seed_of_central_two_cover
      ez (s.ordinary hL).center_two P a ha hne hfix
  let C := B.map d.L.subtype
  let eB : B ≃* C := B.equivMapOfInjective d.L.subtype d.L.subtype_injective
  have hCL : C ≤ d.L := map_subtype_le _
  have hnL : d.S ≤ normalizer (d.L : Set G) := d.S_le_G1.trans
    ((normal_subgroupOf_iff_le_normalizer d.L_component.1).mp
      (s.higmanSims_normal (h := h) hG hL e))
  have hnC := seed_normalized hnL P hP B hi
  have hselfC : centralizer (pCore 2 C : Set C) ≤ pCore 2 C :=
    eB.symm.toMonoidHom.centralizer_pCore_le_of_surjective_pKernel eB.symm.surjective
      (by rw [eB.symm.toMonoidHom.ker_eq_bot eB.symm.injective];
          exact IsPGroup.of_card (n := 0) (by simp)) hself
  have hfixedML : a.fixedSubgroup.map d.L.subtype ≤ d.ML := by
    exact le_inf (le_inf ((map_subtype_le _).trans d.L_component.1) hfixed) (map_subtype_le _)
  have hg : d.ML ⊔ C = d.L := by
    apply le_antisymm (sup_le inf_le_right hCL)
    have hh := congrArg (Subgroup.map d.L.subtype) hgen
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh.ge.trans (sup_le (hfixedML.trans le_sup_left) le_sup_right)
  refine ⟨C,hCL,hP ▸ map_mono hPB,hnC,hselfC,hg,?_,
    f.comp eB.symm.toMonoidHom,hf.comp eB.symm.surjective,?_⟩
  · intro hh
    exact d.L_not_le_MZ (hg.ge.trans (sup_le inf_le_left hh))
  · rw [←MonoidHom.comap_ker]
    exact hk.comap_of_injective _ eB.symm.injective



/-- Retain a central two-kernel covering of the actual HS normalizer in the
original escaping seed, through every central two-cover of the component. -/
theorem PreExclusionSource.higmanSims_escaping_normalizer_cover
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : (d.L ⧸ pCore 2 d.L) ≃* Sporadic.LeechRelated.HS.Carrier) :
    ∃ B : Subgroup G, B ≤ d.L ∧ d.SL ≤ B ∧
      d.S ≤ normalizer (B : Set G) ∧
      centralizer (pCore 2 B : Set B) ≤ pCore 2 B ∧
      d.ML ⊔ B = d.L ∧ ¬ B ≤ d.MZ ∧
      ∃ f : B →* Sporadic.LeechRelated.HS.BlockNormalizer.baseNormalizer,
        Function.Surjective f ∧ IsPGroup 2 f.ker ∧ f.ker ≤ center B := by
  let : IsQuasisimple d.L := IsQuasisimple.of_mulEquiv (hG := hL.2)
    (subgroupOfEquivOfLe d.L_component.1)
  let ez := (QuotientGroup.quotientMulEquivOfEq (s.ordinary hL).center_eq).trans e
  obtain ⟨P,hP,a,ha,hne,hfix,hfixed⟩ := marked_fixer (h := h) s hG hM hu hL
  obtain ⟨B,hPB,hi,hgen,hself,f,hf,hk,hz⟩ :=
    Sporadic.LeechRelated.HS.BlockNormalizer.exists_sylow_seed_covering_normalizer
      ez (s.ordinary hL).center_two P a ha hne hfix
  let C := B.map d.L.subtype
  let eB : B ≃* C := B.equivMapOfInjective d.L.subtype d.L.subtype_injective
  have hCL : C ≤ d.L := map_subtype_le _
  have hnL : d.S ≤ normalizer (d.L : Set G) := d.S_le_G1.trans
    ((normal_subgroupOf_iff_le_normalizer d.L_component.1).mp
      (s.higmanSims_normal (h := h) hG hL e))
  have hnC := seed_normalized hnL P hP B hi
  have hselfC : centralizer (pCore 2 C : Set C) ≤ pCore 2 C :=
    eB.symm.toMonoidHom.centralizer_pCore_le_of_surjective_pKernel eB.symm.surjective
      (by rw [eB.symm.toMonoidHom.ker_eq_bot eB.symm.injective];
          exact IsPGroup.of_card (n := 0) (by simp)) hself
  have hfixedML : a.fixedSubgroup.map d.L.subtype ≤ d.ML := by
    exact le_inf (le_inf ((map_subtype_le _).trans d.L_component.1) hfixed) (map_subtype_le _)
  have hg : d.ML ⊔ C = d.L := by
    apply le_antisymm (sup_le inf_le_right hCL)
    have hh := congrArg (Subgroup.map d.L.subtype) hgen
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh.ge.trans (sup_le (hfixedML.trans le_sup_left) le_sup_right)
  refine ⟨C,hCL,hP ▸ map_mono hPB,hnC,hselfC,hg,?_,
    f.comp eB.symm.toMonoidHom,hf.comp eB.symm.surjective,?_,?_⟩
  · intro hh
    exact d.L_not_le_MZ (hg.ge.trans (sup_le inf_le_left hh))
  · rw [←MonoidHom.comap_ker]
    exact hk.comap_of_injective _ eB.symm.injective



  · intro x hx
    apply mem_center_iff.mpr
    intro y
    apply eB.symm.injective
    have hc : eB.symm x ∈ center B := hz hx
    simpa only [map_mul] using mem_center_iff.mp hc (eB.symm y)

/-- The perfect residual of the actual HS seed belongs to the full original
local family and escapes M_Z; its own two-core quotient is the literal SL₃(2). -/
theorem PreExclusionSource.higmanSims_escaping_local_residual
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
      Nonempty ((K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  obtain ⟨B,hBL,hSB,hnB,hself,hgen,hout,f,hf,hk⟩ :=
    s.higmanSims_escaping_seed (h := h) hG hM hu hL e
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
  have hSM : d.SL ≤ d.MZ := by
    have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hu ▸ Set.mem_singleton Mc
    apply le_inf (d.SL_le_L.trans d.L_component.1)
    apply d.SL_le_S.trans (d.S_le_T.trans ?_)
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  exact ⟨B,K,hBL,hSB,hnB,hgen,rfl,inferInstance,hnK,hfamily,
    generalizedFitting_eq_pCore_of_selfCentralizing 2 hselfK,
    fun hh => hout (hBS ▸ sup_le hh hSM),⟨eK⟩⟩



/-- Source 14.1.6(3) forbids an escaping perfect subgroup from normalizing
any nontrivial characteristic subgroup of the full original S. -/
theorem PreExclusionSource.perfect_escape_not_normalize_characteristic
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {K : Subgroup G} [Group.IsPerfect K] (hKG : K ≤ d.G1) (hout : ¬ K ≤ d.MZ)
    (C : Subgroup d.S) (hC : C.Characteristic) (hne : C ≠ ⊥) :
    ¬ K ≤ normalizer (C.map d.S.subtype : Set G) := by
  let := hC
  intro hnK
  let D := C.map d.S.subtype
  have hDT : D ≤ (T : Subgroup G) := (map_subtype_le _).trans d.S_le_T
  have hDne : D ≠ ⊥ := fun he => hne
    ((map_eq_bot_iff_of_injective _ d.S.subtype_injective).mp he)
  have hnS : (T : Subgroup G) ≤ normalizer (d.S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer d.S_le_T).mp s.sylow_normal
  have hnT : (T : Subgroup G) ≤ normalizer (D : Set G) := hnS.trans
    (normalizer_le_normalizer_characteristic_image d.S C)
  have hN : normalizer (D : Set G) ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal ⟨D,hDne,T.isPGroup'.to_le hDT,rfl⟩,hnT⟩
  have hKM : K ≤ Mc := (le_map_solvableResidual_of_isPerfect K _ hnK).trans
    (residual_le_partner (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hG T hempty hu hN)
  exact hout (le_inf hKG hKM)

/-- The original HS residual has the full-S characteristic-subgroup obstruction
used in the source MS argument, as well as actual local-family membership. -/
theorem PreExclusionSource.higmanSims_local_residual_characteristic_obstruction
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
      ∀ C : Subgroup d.S, C.Characteristic → C ≠ ⊥ →
        ¬ K ≤ normalizer (C.map d.S.subtype : Set G) := by
  obtain ⟨B,K,hBL,_,_,_,hres,hperf,hn,hfamily,hfit,hout,eqK⟩ :=
    s.higmanSims_escaping_local_residual (h := h) hG hM hu hL e
  let := hperf
  have hKL : K ≤ d.L := hres ▸ (map_subtype_le _).trans hBL
  exact ⟨K,hKL,hperf,hn,hfamily,hfit,hout,eqK,
    s.perfect_escape_not_normalize_characteristic (h := h) hG hempty hu
      (hKL.trans d.L_component.1) hout⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
variable {G : Type*} [Group G] [Finite G]

/-- The original marker supplies the actual HS local residual and the full-S
characteristic obstruction at the same component, row, Z₁ and source prime. -/
theorem PreparedChosenModule.source_preExclusion_higmanSims_residual
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
          ∀ C : Subgroup d.S, C.Characteristic → C ≠ ⊥ →
            ¬ K ≤ normalizer (C.map d.S.subtype : Set G)) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hL e =>
    s.higmanSims_local_residual_characteristic_obstruction (h := h) hG hempty hM hu hL e⟩

end CFSG.Quasithin.Chapter15.Section01
