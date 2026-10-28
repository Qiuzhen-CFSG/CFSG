module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.OrbitBorel
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Selection
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2ThompsonBorel
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.AmbientLift
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2BorelCentralizer

/-!
# Natural Borels in the original selected maximal subgroup

For every natural L₂ block K in the fixed local family L(G₁,S), the
original seed proves that J(S) normalizes K. The natural-block Thompson
theorem then makes B_K normalize J(S)=J(T), so B_K lies in M. The proper
Sylow-overgroup theorem gives the reverse containment M∩K≤B_K. Both
M∩K and M_Z∩K therefore retain the same embedded two-core S∩K.

The full-cover Borel is two-perfect. Its centralizer in S equals C_S(K),
by applying the relative C-component theorem inside K S. The S-orbit Borel
inherits two-perfectness, Thompson normalization and the centralizer bound,
and also lies in M. These conclusions cover all local members; no ambient
C-componenthood or S-normalization of K is imposed.

For the selected ambient component, the already proved M_Z Borel equality
identifies both original intersections. The original-marker consumer
preserves the full local family, either prime, and the fixed G₁,M_Z,S,Q₁.
For general K, B_K≤M_Z is still unproved; these results do not assert
M_Z-invariance of its orbit. In particular the general source 15.1.20(2a)
assembly still requires that lower containment. Original 15.1.14 remains
explicit at the marker construction and with its existing assembly owner.

Source: Aschbacher--Smith 15.1.20(2a), printed pp.1094--1095, and the natural
Borel argument in 15.1.21(i), printed pp.1097--1098.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private theorem local_borel_sylow (d : CaseIComponentData T M Mc V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S) :
    ∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype = d.S ⊓ K ∧
      d.localSylowBorel K = (normalizer (P : Set K)).map K.subtype := by
  obtain ⟨P,hP⟩ := ComponentModels.source20_sylow_intersection hK.2
  have he : (P : Subgroup K) = (d.S ⊓ K).subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le inf_le_right]
  refine ⟨P,hP,?_⟩
  change d.localSylowBorel K = (normalizer ((P : Subgroup K) : Set K)).map K.subtype
  rw [he]
  exact d.localSylowBorel_eq K

/-- The natural Borel normalizes the original Thompson subgroup for every
eligible local member; only J(S), rather than all of S, normalizes K. -/
theorem localFamily_linearTwo_borel_thompson (d : CaseIComponentData T M Mc V)
    (h : PreparedChosenModule T M V) (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    {n : ℕ} (hb : IsL2EvenBlock K n) :
    d.localSylowBorel K ≤ normalizer (elementaryAbelianMaxJ d.S : Set G) := by
  obtain ⟨P,hP,hB⟩ := local_borel_sylow d hK
  rw [hB]
  exact hb.borel_normalizes_thompson K d.S (T.isPGroup'.to_le d.S_le_T) P
    (hP.le.trans inf_le_left)
    (d.localFamily_thompson_normalizes h hTM hu hK hq hout hb.2.1.fitting)

/-- The literal natural Borel is two-perfect on the whole original family. -/
theorem localFamily_linearTwo_borel_twoPerfect (d : CaseIComponentData T M Mc V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    {n : ℕ} (hb : IsL2EvenBlock K n) : IsPPerfect 2 (d.localSylowBorel K) := by
  obtain ⟨P,_,hB⟩ := local_borel_sylow d hK
  rw [hB]
  exact (hb.borel_twoPerfect P).of_surjective
    (K.subtype.subgroupMap _) (K.subtype.subgroupMap_surjective _)

/-- Centralizers are computed in the actual local group K S. This needs
no component hypothesis on K in the larger fixed centralizer G₁. -/
theorem localFamily_linearTwo_borel_centralizer (d : CaseIComponentData T M Mc V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    {n : ℕ} (hb : IsL2EvenBlock K n) :
    d.S ⊓ centralizer (d.localSylowBorel K : Set G) =
      d.S ⊓ centralizer (K : Set G) := by
  obtain ⟨P,_,hB⟩ := local_borel_sylow d hK
  apply le_antisymm
  · rw [hB]
    exact le_inf inf_le_left
      (hb.relative_borel_centralizer (K ⊔ d.S) K d.S le_sup_left le_sup_right
        hK.2.1 (T.isPGroup'.to_le d.S_le_T) P)
  · exact inf_le_inf_left _ (centralizer_le inf_le_left)

/-- The original maximal subgroup M contains the full natural Borel,
by the original equality J(S)=J(T) and Thompson-normalizer control. -/
theorem localFamily_linearTwo_borel_le_selected (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    {n : ℕ} (hb : IsL2EvenBlock K n) : d.localSylowBorel K ≤ M := by
  have hn := d.localFamily_linearTwo_borel_thompson h hM.1.2 hu hK hq hout hb
  have he := (h.caseI_marked_thompson_control hG T hM hJ d.Z1_le_fixed).1
  change elementaryAbelianMaxJ d.S = elementaryAbelianMaxJ (T : Subgroup G) at he
  rw [he] at hn
  exact hn.trans (source_centralizing_baumann_control hG T hM hJ).2.2.2.2.2.1

/-- The M-intersection is exactly the natural Borel, with the original K
and Sylow marking retained. The M_Z-intersection remains separately marked. -/
theorem localFamily_linearTwo_selected_borel (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    {n : ℕ} (hb : IsL2EvenBlock K n) : M ⊓ K = d.localSylowBorel K := by
  apply le_antisymm
  · obtain ⟨P,hP,hB⟩ := local_borel_sylow d hK
    rw [hB]
    have hA : M.subgroupOf K ≠ ⊤ := fun he =>
      d.localFamily_not_le_M hG hempty hM hu hK hout (subgroupOf_eq_top.mp he)
    obtain ⟨_,_,F,_,_,hF,_,r,⟨m⟩,_⟩ := hb
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    let q := m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
    have hq : Function.Surjective q := m.quotientIso.surjective.comp
      (QuotientGroup.mk'_surjective _)
    have hk : q.ker ≤ (P : Subgroup K) := by
      rw [MonoidHom.ker_comp_of_injective _ _ m.quotientIso.injective,QuotientGroup.ker_mk']
      exact pCore_isPGroup.le_sylow_of_normal P
    have hPA : (P : Subgroup K) ≤ M.subgroupOf K := by
      intro x hx
      exact hM.1.2 (d.S_le_T ((hP ▸ mem_map_of_mem K.subtype hx).1))
    have hn := Matrix.SpecialLinearGroup.proper_overgroup_le_sylow_normalizer_of_two_kernel
      q hq P hk (M.subgroupOf K) hPA hA
    intro x hx
    exact ⟨⟨x,hx.2⟩,hn hx.1,rfl⟩
  · exact le_inf (d.localFamily_linearTwo_borel_le_selected hG hM hJ hu h hK hq hout hb)
      inf_le_left

/-- Both original intersections retain the same marked Sylow core. The
selected intersection is the entire Borel, with its literal centralizer. -/
theorem localFamily_linearTwo_selected_geometry (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    {n : ℕ} (hb : IsL2EvenBlock K n) :
    M ⊓ K = d.localSylowBorel K ∧
      (M ⊓ K).pCoreIn 2 = d.S ⊓ K ∧
      (d.MZ ⊓ K).pCoreIn 2 = d.S ⊓ K ∧
      IsPPerfect 2 (M ⊓ K : Subgroup G) ∧
      d.S ⊓ centralizer ((M ⊓ K : Subgroup G) : Set G) = d.S ⊓ centralizer (K : Set G) ∧
      ⁅K,elementaryAbelianMaxJ d.S⁆ = K := by
  have he := d.localFamily_linearTwo_selected_borel hG hempty hM hJ hu h hK hq hout hb
  have hcore : (M ⊓ K).pCoreIn 2 = d.S ⊓ K := by
    obtain ⟨P,hP,_⟩ := local_borel_sylow d hK
    have hSM : d.S ⊓ K ≤ M ⊓ K :=
      inf_le_inf_right K (d.S_le_T.trans hM.1.2)
    obtain ⟨Q,hQ⟩ := P.exists_map_subtype_eq_of_le
      (show M ⊓ K ≤ K from inf_le_right) (hP ▸ hSM)
    apply le_antisymm ((pCoreIn_le_sylow _ Q).trans_eq (hQ.trans hP))
    exact le_pCoreIn_of_normalizes
      (T.isPGroup'.to_le (inf_le_left.trans d.S_le_T)) hSM (he ▸ inf_le_right)
  refine ⟨he,hcore,d.localFamily_linearTwo_core hu hK hout hb,?_,?_,?_⟩
  · rw [he]
    exact d.localFamily_linearTwo_borel_twoPerfect hK hb
  · rw [he]
    exact d.localFamily_linearTwo_borel_centralizer hK hb
  · exact (d.localFamily_normalizerAction hG hempty hM hJ hu h hK hq hout
      hb.2.1.fitting).movement.symm

/-- The actual S-orbit Borel has the natural-block Thompson and centralizer
properties on the entire local family, and is contained in M. This does
not assert invariance under M_Z or containment in M_Z. -/
theorem localFamily_linearTwo_orbit_geometry (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    {n : ℕ} (hb : IsL2EvenBlock K n) :
    IsPPerfect 2 (d.orbitSylowBorel K) ∧ d.orbitSylowBorel K ≤ M ∧
      d.orbitSylowBorel K ≤ normalizer (elementaryAbelianMaxJ d.S : Set G) ∧
      d.S ⊓ centralizer (d.orbitSylowBorel K : Set G) ≤
        d.S ⊓ centralizer (K : Set G) := by
  have hn := d.localFamily_linearTwo_borel_thompson h hM.1.2 hu hK hq hout hb
  have hSJ : d.S ≤ normalizer (elementaryAbelianMaxJ d.S : Set G) :=
    d.S.le_normalizer.trans (normalizer_le_normalizer_elementaryAbelianMaxJ d.S)
  refine ⟨RankOne.ChiProduct.conjugateSpan_twoPerfect _ _
    (d.localFamily_linearTwo_borel_twoPerfect hK hb),?_,?_,?_⟩
  · exact conjugateSpanBy_le
      (d.localFamily_linearTwo_borel_le_selected hG hM hJ hu h hK hq hout hb)
      ((d.S_le_T.trans hM.1.2).trans M.le_normalizer)
  · exact conjugateSpanBy_le hn
      (hSJ.trans (normalizer (elementaryAbelianMaxJ d.S : Set G)).le_normalizer)
  · exact (inf_le_inf_left _ (centralizer_le (le_conjugateSpanBy _ _))).trans_eq
      (d.localFamily_linearTwo_borel_centralizer hK hb)

/-- In the selected natural component, the two original intersections
are equal. The original source prime is retained without exchanged selection. -/
theorem PreExclusionSource.constrained_natural_intersections
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p n : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hb : IsL2EvenBlock d.L n) :
    M ⊓ d.L = d.ML ∧ IsPPerfect 2 d.ML ∧
      d.S ⊓ centralizer (d.ML : Set G) = d.S ⊓ centralizer (d.L : Set G) := by
  have hK : d.L ∈ Chapter1.LIn d.G1 d.S := ⟨d.L_component.1,s.local_component⟩
  have he := (s.constrained_linearTwo_borel (h := h) hG hM hu hne hmany hres hb).trans
    (d.localSylowBorel_eq d.L).symm
  refine ⟨(d.localFamily_linearTwo_selected_borel hG hempty hM hJ hu h hK
    s.quasisimple d.L_not_le_MZ hb).trans he.symm,?_,?_⟩
  · rw [he]
    exact d.localFamily_linearTwo_borel_twoPerfect hK hb
  · rw [he]
    exact d.localFamily_linearTwo_borel_centralizer hK hb

/-- The later exchanged source has the same literal intersections and
centralizer, retaining either exchanged-plane size. -/
theorem ExchangedSource.constrained_natural_intersections
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource) {n : ℕ}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hne : M ≠ Mc) (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hb : IsL2EvenBlock d.L n) :
    M ⊓ d.L = d.ML ∧ IsPPerfect 2 d.ML ∧
      d.S ⊓ centralizer (d.ML : Set G) = d.S ⊓ centralizer (d.L : Set G) := by
  have hK : d.L ∈ Chapter1.LIn d.G1 d.S := ⟨d.L_component.1,s.local_component⟩
  have he := (s.constrained_linearTwo_borel h hG hM hu hne hmany hres hb).trans
    (d.localSylowBorel_eq d.L).symm
  refine ⟨(d.localFamily_linearTwo_selected_borel hG hempty hM hJ hu h hK
    s.quasisimple d.L_not_le_MZ hb).trans he.symm,?_,?_⟩
  · rw [he]
    exact d.localFamily_linearTwo_borel_twoPerfect hK hb
  · rw [he]
    exact d.localFamily_linearTwo_borel_centralizer hK hb

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original marker supplies the natural Borel geometry for every
eligible member of the original L(G₁,S), retaining its row and either prime.
The lower M_Z containment is not a hypothesis or a conclusion of this export. -/
theorem PreparedChosenModule.source_preExclusion_local_natural_borels
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
      ∀ K ∈ Chapter1.LIn d.G1 d.S, IsQuasisimple (K ⧸ pCore 2 K) →
        ¬ K ≤ d.MZ → ∀ n : ℕ, ChapterC.IsL2EvenBlock K n →
          (M ⊓ K = d.localSylowBorel K ∧
            (M ⊓ K).pCoreIn 2 = d.S ⊓ K ∧
            (d.MZ ⊓ K).pCoreIn 2 = d.S ⊓ K ∧
            IsPPerfect 2 (M ⊓ K : Subgroup G) ∧
            d.S ⊓ centralizer ((M ⊓ K : Subgroup G) : Set G) = d.S ⊓ centralizer (K : Set G) ∧
            ⁅K,elementaryAbelianMaxJ d.S⁆ = K) ∧
          (IsPPerfect 2 (d.orbitSylowBorel K) ∧ d.orbitSylowBorel K ≤ M ∧
            d.orbitSylowBorel K ≤ normalizer (elementaryAbelianMaxJ d.S : Set G) ∧
            d.S ⊓ centralizer (d.orbitSylowBorel K : Set G) ≤
              d.S ⊓ centralizer (K : Set G)) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun _ hK hq hout _ hb =>
    ⟨d.localFamily_linearTwo_selected_geometry hG hempty hM hJ hu h hK hq hout hb,
      d.localFamily_linearTwo_orbit_geometry hG hM hJ hu h hK hq hout hb⟩⟩
end CFSG.Quasithin.Chapter15.Section01

