module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LinearTwo
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.SolvableControl
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.OrbitBorel
public import Theory.GroupTheory.Commutator.TwoOrbitSpan
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwoSource
/-!
# Orbit Borels and the selected natural rank-one alternative

The actual S-orbit of the Sylow Borel has characteristic two, a normal
Sylow two-subgroup, and odd quotient for every short K in L(G₁,S).
This calculation takes place inside ⟨K,S⟩ and keeps the original embeddings.

For a C-component of G₁, O²(M_Z) normalizes K by the source two-orbit
bound. Characteristicity of O₂(M_Z∩K)=S∩K then makes it preserve the
Borel. The supplement M_Z=O²(M_Z)S preserves the whole Borel orbit.
Original 15.1.19(2) now gives reverse containment, hence M_Z∩K=B_K.
The selected-component applications supply the complete natural L₂
rank-one alternative, before exchanged selection and on both later planes.

The general local-family orbit structure does not assert M_Z-invariance.
For K which is only a C-component of ⟨K,S⟩, that invariance remains with
this catalogue owner. Neither ambient C-componenthood nor S-normalization
is inferred from local-family membership. Full FF reconstruction and the
remaining C.2.7 clauses are still needed for catalogue exhaustiveness.
Original 15.1.14 remains explicit for qt-e-1514-global-thompson-residual,
with discharge by qt-e-15122-pre-exclusion-catalogue.

Source: Aschbacher--Smith 15.1.20, third paragraph and (2a), printed p.1094;
1.2.1(3), printed p.504; C.1.9, printed p.123.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The original Sylow Borel inside K, retaining its ambient embedding. -/
@[expose] def localSylowBorel (d : CaseIComponentData T M Mc V) (K : Subgroup G) : Subgroup G :=
  K ⊓ normalizer ((d.S ⊓ K : Subgroup G) : Set G)

/-- The source B₀=⟨B_K^S⟩; the fixed original S can permute K. -/
@[expose] def orbitSylowBorel (d : CaseIComponentData T M Mc V) (K : Subgroup G) : Subgroup G :=
  conjugateSpanBy (d.localSylowBorel K) d.S

theorem localSylowBorel_eq (d : CaseIComponentData T M Mc V) (K : Subgroup G) :
    d.localSylowBorel K = (normalizer ((d.S ⊓ K).subgroupOf K : Set K)).map K.subtype := by
  rw [←subgroupOf_normalizer_eq (show d.S ⊓ K ≤ K from inf_le_right),subgroupOf_map_subtype]
  exact inf_comm _ _

/-- The particular orbit Borel stays in G₁ and is invariant under S. -/
theorem orbitSylowBorel_local (d : CaseIComponentData T M Mc V)
    {K : Subgroup G} (hK : K ≤ d.G1) :
    d.orbitSylowBorel K ≤ d.G1 ∧ d.S ≤ normalizer (d.orbitSylowBorel K : Set G) := by
  exact ⟨conjugateSpanBy_le (inf_le_left.trans hK) (d.S_le_G1.trans d.G1.le_normalizer),
    le_normalizer_conjugateSpanBy _ _⟩

/-- The source orbit Borel has characteristic two and a normal Sylow
subgroup for every short member of the original local family. -/
theorem localFamily_orbitBorel_structure (d : CaseIComponentData T M Mc V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hb : IsShort K) :
    generalizedFitting (d.orbitSylowBorel K) = pCore 2 (d.orbitSylowBorel K) ∧
      (∃ P : Sylow 2 (d.orbitSylowBorel K),
        (P : Subgroup (d.orbitSylowBorel K)) = pCore 2 (d.orbitSylowBorel K)) ∧
      Odd (Nat.card (d.orbitSylowBorel K ⧸ pCore 2 (d.orbitSylowBorel K))) := by
  let H := K ⊔ d.S
  let K0 := K.subgroupOf H
  let eK : K0 ≃* K := subgroupOfEquivOfLe le_sup_left
  obtain ⟨P,hP⟩ := hK.2.2.1
  have hK0 : IsBlock K0 := ⟨inferInstance,hb.of_mulEquiv eK.symm,hK.2.1.subnormal⟩
  let := hq
  have hq0 : IsQuasisimple (K0 ⧸ pCore 2 K0) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)).symm
  let B := conjugateSpanBy (K0 ⊓ normalizer (((P : Subgroup H) ⊓ K0 : Subgroup H) : Set H)) (P : Subgroup H)
  have hB : B.map H.subtype = d.orbitSylowBorel K := by
    rw [map_conjugateSpanBy,map_relative_sylowNormalizer _ _ _ H.subtype_injective,hP,
      map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left)]
    rfl
  let e : B ≃* d.orbitSylowBorel K :=
    (equivMapOfInjective B H.subtype H.subtype_injective).trans (MulEquiv.subgroupCongr hB)
  obtain ⟨hf,⟨R,hR⟩,ho⟩ := hK0.orbit_borel_structure P hq0
  have hf' : generalizedFitting (d.orbitSylowBorel K) = pCore 2 (d.orbitSylowBorel K) := by
    rw [←map_generalizedFitting_equiv e,←pCore_map_iso 2 e,hf]
  refine ⟨hf',⟨R.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩,?_⟩
  · change (R : Subgroup B).map e.toMonoidHom = _
    rw [hR,pCore_map_iso]
  · rwa [←Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv]

/-- The core defining the source Borel is exactly the previously computed
core of the original marked intersection. -/
theorem localFamily_linearTwo_borel_eq_core_normalizer (d : CaseIComponentData T M Mc V)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hout : ¬ K ≤ d.MZ) {n : ℕ} (hb : IsL2EvenBlock K n) :
    d.localSylowBorel K =
      (normalizer (((d.MZ ⊓ K).pCoreIn 2).subgroupOf K : Set K)).map K.subtype := by
  rw [d.localFamily_linearTwo_core hu hK hout hb]
  exact d.localSylowBorel_eq K

/-- Apply original 15.1.19(2) after establishing invariance of the actual
orbit. The C-component application below discharges this premise. -/
private theorem PreExclusionSource.localFamily_linearTwo_borel_of_orbit_normalized
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
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    {n : ℕ} (hb : IsL2EvenBlock K n)
    (hn : d.MZ ≤ normalizer (d.orbitSylowBorel K : Set G)) :
    d.MZ ⊓ K = (normalizer ((d.S ⊓ K).subgroupOf K : Set K)).map K.subtype := by
  have hs := d.localFamily_orbitBorel_structure hK hq hb.2.1
  have hB := s.constrained_solvable_control (h := h) hG hM hu hne hmany hres
    (d.orbitSylowBorel_local hK.1).1 hn hs.1 hs.2.2
  apply le_antisymm (d.localFamily_linearTwo_borel_bound hu hK hout hb)
  rw [←d.localSylowBorel_eq]
  exact le_inf ((le_conjugateSpanBy _ _).trans hB) inf_le_left

/-- For an actual C-component of G₁, O²(M_Z) normalizes K and
hence its marked Borel. The Sylow supplement then normalizes the full
Borel orbit. This additional C-component hypothesis is retained explicitly. -/
theorem localFamily_linearTwo_orbit_normalized_of_cComponent
    (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hSyl : Chapter1.IsSylowIn 2 d.S d.G1)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hcomp : (K.subgroupOf d.G1).IsCComponent)
    (hout : ¬ K ≤ d.MZ) {n : ℕ} (hb : IsL2EvenBlock K n) :
    d.MZ ≤ normalizer (d.orbitSylowBorel K : Set G) := by
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
  rw [map_subgroupOf_eq_of_le hRG,map_subgroupOf_eq_of_le hK.1] at hnK
  have hnB : R ≤ normalizer (d.localSylowBorel K : Set G) := by
    rw [d.localSylowBorel_eq]
    exact (le_inf hRM hnK).trans (d.localFamily_linearTwo_borel_normalized hu hK hout hb)
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

/-- Reverse Borel containment for a member of the original local family
which is also a C-component of the fixed G₁. All orbit-control premises
are discharged; the extra component hypothesis is explicit. -/
theorem PreExclusionSource.localFamily_linearTwo_borel_of_cComponent
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
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hcomp : (K.subgroupOf d.G1).IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    {n : ℕ} (hb : IsL2EvenBlock K n) :
    d.MZ ⊓ K = (normalizer ((d.S ⊓ K).subgroupOf K : Set K)).map K.subtype := by
  exact s.localFamily_linearTwo_borel_of_orbit_normalized (h := h) hG hM hu hne hmany hres
    hK hq hout hb
    (d.localFamily_linearTwo_orbit_normalized_of_cComponent hG h hu s.centralizer_sylow
      hK hcomp hout hb)

/-- The complete natural L₂ Borel equality on the original selected
C-component, before exchanged selection. -/
theorem PreExclusionSource.constrained_linearTwo_borel
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p n : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hb : IsL2EvenBlock d.L n) :
    d.ML = (normalizer (d.SL.subgroupOf d.L : Set d.L)).map d.L.subtype := by
  have hk : d.L ∈ Chapter1.LIn d.G1 d.S := ⟨d.L_component.1,s.local_component⟩
  exact s.localFamily_linearTwo_borel_of_cComponent (h := h) hG hM hu hne hmany hres
    hk d.L_component.2 s.quasisimple d.L_not_le_MZ hb

/-- The later selected component has the same Borel equality on either
exchanged-plane size, retaining the original residual premise. -/
theorem ExchangedSource.constrained_linearTwo_borel
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource) {n : ℕ}
    (h : PreparedChosenModule T M V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hb : IsL2EvenBlock d.L n) :
    d.ML = (normalizer (d.SL.subgroupOf d.L : Set d.L)).map d.L.subtype := by
  have hk : d.L ∈ Chapter1.LIn d.G1 d.S := ⟨d.L_component.1,s.local_component⟩
  have hs := d.localFamily_orbitBorel_structure hk s.quasisimple hb.2.1
  have hn := d.localFamily_linearTwo_orbit_normalized_of_cComponent hG h hu s.centralizer_sylow
    hk d.L_component.2 d.L_not_le_MZ hb
  have hB := s.constrained_solvable_control h hG hM hu hne hmany hres
    (d.orbitSylowBorel_local hk.1).1 hn hs.1 hs.2.2
  apply le_antisymm (d.localFamily_linearTwo_borel_bound hu hk d.L_not_le_MZ hb)
  rw [←d.localSylowBorel_eq]
  exact le_inf ((le_conjugateSpanBy _ _).trans hB) inf_le_left

/-- The natural L₂ block supplies every clause of the rank-one alternative
before exchanged selection, including its original Thompson action. -/
theorem PreExclusionSource.constrained_rankOne_of_linearTwo
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p n : ℕ}
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
    (hb : IsL2EvenBlock d.L n) : d.ConstrainedRankOneAlternative := by
  have hk : d.L ∈ Chapter1.LIn d.G1 d.S := ⟨d.L_component.1,s.local_component⟩
  exact ⟨Or.inl ⟨n,hb⟩,
    s.constrained_linearTwo_borel (h := h) hG hM hu hne hmany hres hb,
    (d.localFamily_normalizerAction hG hempty hM hJ hu h hk s.quasisimple
      d.L_not_le_MZ hb.2.1.fitting).movement.symm⟩

/-- The same complete rank-one alternative on the later exchanged source. -/
theorem ExchangedSource.constrained_rankOne_of_linearTwo
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource) {n : ℕ}
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
    (hb : IsL2EvenBlock d.L n) : d.ConstrainedRankOneAlternative := by
  have hk : d.L ∈ Chapter1.LIn d.G1 d.S := ⟨d.L_component.1,s.local_component⟩
  exact ⟨Or.inl ⟨n,hb⟩,s.constrained_linearTwo_borel h hG hM hu hne hmany hres hb,
    (d.localFamily_normalizerAction hG hempty hM hJ hu h hk s.quasisimple
      d.L_not_le_MZ hb.2.1.fitting).movement.symm⟩

/-- The full-Sylow branch now gives the complete rank-one source alternative;
the remaining branch retains the literal C.2.7 star comparison. -/
theorem PreExclusionSource.constrained_rankOne_or_star
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
    d.ConstrainedRankOneAlternative ∨
      ∃ hnL : d.Q1 ≤ normalizer (d.L : Set G),
        StarModels.Model (starImage d.L d.Q1 d.L) ∧
          (coreToStar hnL).ker ≤ center (d.L ⧸ pCore 2 d.L) ∧
          (Nat.card (center (d.L ⧸ pCore 2 d.L)) = 1 ∨
            Nat.card (center (d.L ⧸ pCore 2 d.L)) = 3) := by
  rcases s.constrained_star_catalogue_or_rankOne (h := h) hG hfit with hb | hs
  · rcases hb with ⟨n,hb⟩ | hb
    · exact Or.inl (s.constrained_rankOne_of_linearTwo (h := h) hG hempty hM hJ hu hne hmany hres hb)
    · exact Or.inl (s.constrained_rankOne_of_alternatingFive (h := h) hG hempty hM hJ hu hb)
  · exact Or.inr hs

/-- The later exchanged source retains both plane sizes and the same
complete rank-one-or-star conclusion. -/
theorem ExchangedSource.constrained_rankOne_or_star
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
    d.ConstrainedRankOneAlternative ∨
      ∃ hnL : d.Q1 ≤ normalizer (d.L : Set G),
        StarModels.Model (starImage d.L d.Q1 d.L) ∧
          (coreToStar hnL).ker ≤ center (d.L ⧸ pCore 2 d.L) ∧
          (Nat.card (center (d.L ⧸ pCore 2 d.L)) = 1 ∨
            Nat.card (center (d.L ⧸ pCore 2 d.L)) = 3) := by
  rcases s.constrained_star_catalogue_or_rankOne hG h hfit with hb | hs
  · rcases hb with ⟨n,hb⟩ | hb
    · exact Or.inl (s.constrained_rankOne_of_linearTwo h hG hempty hM hJ hu hne hmany hres hb)
    · exact Or.inl (s.constrained_rankOne_of_alternatingFive hG hempty hM hJ hu h hb)
  · exact Or.inr hs

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
