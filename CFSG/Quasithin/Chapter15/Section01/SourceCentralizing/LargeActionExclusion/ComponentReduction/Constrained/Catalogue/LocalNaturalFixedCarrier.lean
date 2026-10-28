module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalNaturalMathieuRadical


/-!
# Fixed-plane and hexad geometry of an original natural local escape

The remaining Mathieu carrier has the original fixed plane as C_V(L).
Indeed the cubic residual of M intersect G₁ is the literal residual of
M intersect L, and the proved ordinary centralizer identity applies to it.
The reverse containment follows from the already identified C_V(K).

In the remaining M₂₂ quotient, the image of V intersect L is exactly the
same moving four-group. The fixed summand lies in the covering center
whenever it lies in L, so this equality retains the full central cover.
The original Sylow normalizes this four-group, placing it in a native
hexad kernel. The image of M intersect L normalizes it, and its full
normalizer lies strictly inside the characteristic-two hexad stabilizer.

For the later exchanged source, fixed-plane noncentrality excludes every
natural local escape. This completes the local-family group/intersection
rows at that input, including the marked binary flag parabolics. Original
marker consumers retain the fixed-plane equality and literal hexad geometry;
they do not yet exclude the covered M₂₂ embedding. The original 15.1.20(2)
and constrained 15.1.22 assembly remain open, with original 15.1.14 and
whole-core A₆ reconstruction retaining their existing producers.

Source: Aschbacher--Smith 15.1.20(2), 15.1.22(**), 15.1.25(1),(3),
printed pp.1094--1102; native M₂₂ four-group geometry used in 15.3.43,
p.1140, with its model hypotheses verified here.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The original residual-fixed plane centralizes the entire selected carrier,
not just its escaping natural local member. Both original primes and the
full covering center are retained. -/
theorem PreExclusionSource.localFamily_linearTwo_fixed_carrier
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : V = localModule T M)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ d.MZ) {n : ℕ} (hb : IsL2EvenBlock K n) :
    V ⊓ centralizer
      ((pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype : Set G) =
        V ⊓ centralizer (d.L : Set G) := by
  obtain ⟨hp3,_,_,_⟩ := s.localFamily_linearTwo_moving_plane_four (h := h)
    hp hG hM hJ hu hfull hK hq hout hb
  have s3 : d.PreExclusionSource h.normalized 3 := hp3 ▸ s
  have hL : IsComponent d.G1 (d.L.subgroupOf d.G1) := by
    rcases d.ordinary_or_constrained s.odd_core with hc | hf
    · exact hc
    · exact (hout (s.localFamily_linearTwo_le_MZ_of_constrained_carrier (h := h)
        hp hG hempty hM hJ hu hne hmany hfull hres hK hq hb hf)).elim
  obtain ⟨name,hname,model⟩ := s.localFamily_linearTwo_carrier_mathieu (h := h)
    hp hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb
  have hn : name = .m12 ∨ name = .m22 ∨ name = .m23 ∨ name = .m24 ∨
      name = .j2 ∨ name = .he := by
    rcases hname with h22 | h23
    · exact .inr (.inl h22)
    · exact .inr (.inr (.inl h23))
  let e := (QuotientGroup.quotientMulEquivOfEq (s.ordinary hL).center_eq.symm).trans model.some
  have hf := s.surviving_sporadic_quotient_facts (h := h) hn e
  have heq := (s.sporadic_quotient_model_control (h := h) hM.1.2 hu hL hn e).2
    (s3.localThreeResidual_escape_of_cubic_model (h := h) hG hf)
  let := s.quasisimple
  have hY := (d.source_cubic_component hG h hf).2
  let := h.elementary
  have hVT : V ≤ (T : Subgroup G) := by
    let : (V.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer h.normalized
    let := IsElementaryAbelian.subgroupOf h.le_selected (p := 2)
    have hh := (IsElementaryAbelian.isPGroup 2 (V.subgroupOf M)).le_sylow_of_normal
      (T.subtype hM.1.2)
    simpa only [map_subgroupOf_eq_of_le h.le_selected,Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hM.1.2] using map_mono (f := M.subtype) hh
  have hVS : V ≤ d.S := le_inf hVT
    (V.le_centralizer.trans (centralizer_le (d.Z1_le_fixed.trans inf_le_left)))
  let Y := (primeToResidual 3 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype
  let R := (pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype
  have hYR : Y ≤ R := map_mono (le_pResidual_of_isPPerfect _
    (isPPerfect_primeToResidual 3 2 (by decide)))
  have heq' : d.S ⊓ centralizer (Y : Set G) = d.S ⊓ centralizer (d.L : Set G) := by
    dsimp only [Y]
    rw [hY]
    exact heq
  have hFC : V ⊓ centralizer (R : Set G) ≤ centralizer (d.L : Set G) :=
    ((le_inf (inf_le_left.trans hVS) (inf_le_right.trans (centralizer_le hYR))).trans
      heq'.le).trans inf_le_right
  have hKL := (s.localFamily_linearTwo_selected_carrier (h := h)
    hG hM hJ hu hne hmany hfull hres hK hq hout hb (by omega)).1.le
  have hfixed := (s.localFamily_linearTwo_full_action (h := h)
    hG hM hJ hu hfull hK hq hout hb (by omega)).2.2.1
  exact le_antisymm (le_inf inf_le_left hFC)
    ((inf_le_inf_left V (centralizer_le hKL)).trans_eq hfixed.symm)

/-- The same exchanged source excludes every natural member of its original
local family, without adding ambient C-componenthood to that member. -/
theorem ExchangedSource.localFamily_linearTwo_le_MZ
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (x : d.ExchangedSource) (s : d.PreExclusionSource h.normalized 3)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : V = localModule T M)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    {n : ℕ} (hb : IsL2EvenBlock K n) : K ≤ d.MZ := by
  by_contra hout
  have he := s.localFamily_linearTwo_fixed_carrier (h := h) (.inl rfl)
    hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb
  have hL : IsComponent d.G1 (d.L.subgroupOf d.G1) := by
    rcases d.ordinary_or_constrained s.odd_core with hc | hf
    · exact hc
    · exact (hout (s.localFamily_linearTwo_le_MZ_of_constrained_carrier (h := h)
        (.inl rfl) hG hempty hM hJ hu hne hmany hfull hres hK hq hb hf)).elim
  obtain ⟨name,hname,model⟩ := s.localFamily_linearTwo_carrier_mathieu (h := h)
    (.inl rfl) hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb
  have hn : name = .m12 ∨ name = .m22 ∨ name = .m23 ∨ name = .m24 ∨
      name = .j2 ∨ name = .he := by
    rcases hname with h22 | h23
    · exact .inr (.inl h22)
    · exact .inr (.inr (.inl h23))
  let e := (QuotientGroup.quotientMulEquivOfEq (s.ordinary hL).center_eq.symm).trans model.some
  exact x.fixed_noncentral (s.surviving_sporadic_quotient_facts (h := h) hn e)
    (he.le.trans inf_le_right)

/-- Full group and intersection rows on the whole exchanged local family.
The additional block assertions still require the source C-component branch. -/
theorem ExchangedSource.localFamily_constrained_source_rows
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (x : d.ExchangedSource) (s : d.PreExclusionSource h.normalized 3)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : V = localModule T M)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ d.MZ) (hf : generalizedFitting K = pCore 2 K) :
    ⁅K,elementaryAbelianMaxJ d.S⁆ = K ∧ LocalConstrainedSourceRows d K := by
  obtain ⟨hm,hr⟩ := d.localFamily_constrained_rows hG hempty hM hJ hu h hK hq hout hf
  refine ⟨hm,?_⟩
  cases hr with
  | naturalTwo n hb _ _ =>
    exact (hout (x.localFamily_linearTwo_le_MZ (h := h) s hG hempty hM hJ hu hne hmany
      hfull hres hK hq hb)).elim
  | alternatingFive hb he hc => exact .alternatingFive hb he hc
  | small model equiv marking => exact .small model equiv marking
  | linear n hn e t ht hz hm => exact .linear n hn e t ht hz hm

/-- The literal M₂₂ image of V intersect L is the original moving four-group.
Its full normalizer has a strict native hexad overgroup of characteristic two,
and it contains the original image of M intersect L. -/
theorem PreExclusionSource.localFamily_linearTwo_m22_hexad
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : V = localModule T M)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ d.MZ) {n : ℕ} (hb : IsL2EvenBlock K n) :
    let W := ⁅V,(pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype⁆
    ∃ e : (d.L ⧸ center d.L) ≃* Sporadic.Mathieu.M22,
      let q := e.toMonoidHom.comp (QuotientGroup.mk' (center d.L))
      let Wbar := (W.subgroupOf d.L).map q
      ∃ B ∈ Sporadic.Mathieu.m22Blocks,
        Nat.card Wbar = 4 ∧
        Wbar ≤ Sporadic.Mathieu.m22HexadPointwiseKernel B ∧
        (V.subgroupOf d.L).map q = Wbar ∧
        (M.subgroupOf d.L).map q ≤ normalizer (Wbar : Set Sporadic.Mathieu.M22) ∧
        normalizer (Wbar : Set Sporadic.Mathieu.M22) <
          MulAction.stabilizer Sporadic.Mathieu.M22 B ∧
        generalizedFitting (MulAction.stabilizer Sporadic.Mathieu.M22 B) =
          pCore 2 (MulAction.stabilizer Sporadic.Mathieu.M22 B) := by
  intro W
  obtain ⟨name,hname,model⟩ := s.localFamily_linearTwo_carrier_mathieu (h := h)
    hp hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb
  have model22 : Nonempty ((d.L ⧸ center d.L) ≃* Sporadic.Mathieu.M22) := by
    rcases hname with rfl | rfl
    · exact model
    · exact (s.localFamily_linearTwo_not_m23 (h := h)
        hp hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb model).elim
  let e := model22.some
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center d.L))
  let Wbar := (W.subgroupOf d.L).map q
  obtain ⟨_,_,hWU,_⟩ := s.localFamily_linearTwo_moving_plane_four (h := h)
    hp hG hM hJ hu hfull hK hq hout hb
  have hKL := (s.localFamily_linearTwo_selected_carrier (h := h)
    hG hM hJ hu hne hmany hfull hres hK hq hout hb (by omega)).1.le
  have hWL : W ≤ d.L := hWU.trans ((map_subtype_le _).trans hKL)
  obtain ⟨hsplit,_,_,_⟩ := s.localFamily_linearTwo_full_action (h := h)
    hG hM hJ hu hfull hK hq hout hb (by omega)
  let F := V ⊓ centralizer
    ((pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype : Set G)
  have hWV : W ≤ V := le_sup_left.trans hsplit.symm.le
  have hFC : F ≤ centralizer (d.L : Set G) :=
    (s.localFamily_linearTwo_fixed_carrier (h := h) hp hG hempty hM hJ hu hne hmany
      hfull hres hK hq hout hb).le.trans inf_le_right
  have himage : (V.subgroupOf d.L).map q = Wbar := by
    apply le_antisymm ?_ (map_mono (comap_mono hWV))
    rintro _ ⟨v,hv,rfl⟩
    have hWF : W ≤ normalizer (F : Set G) :=
      (le_centralizer_iff.mp (hFC.trans (centralizer_le hWL))).trans
        (Subgroup.centralizer_le_normalizer _)
    have hvm : v.val ∈ (W : Set G) * (F : Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right W F hWF]
      exact hsplit ▸ hv
    obtain ⟨w,hw,f,hf,hv'⟩ := hvm
    have hfL : f ∈ d.L := by
      have hh := d.L.mul_mem (d.L.inv_mem (hWL hw)) v.property
      rw [←hv',inv_mul_cancel_left] at hh
      exact hh
    let wL : d.L := ⟨w,hWL hw⟩
    let fL : d.L := ⟨f,hfL⟩
    have hcentral : fL ∈ center d.L := mem_center_iff.mpr
      (fun a => Subtype.ext (hFC hf a a.property))
    have hfq : q fL = 1 := by
      change e (QuotientGroup.mk' (center d.L) fL) = 1
      have hz : QuotientGroup.mk' (center d.L) fL = 1 :=
        (QuotientGroup.eq_one_iff fL).mpr hcentral
      rw [hz,e.map_one]
    refine ⟨wL,hw,?_⟩
    have he : wL * fL = v := Subtype.ext hv'
    rw [←he,map_mul,hfq,mul_one]
  have hc : Nat.card Wbar = 4 := by
    have hh := (s.localFamily_linearTwo_mathieu_image (h := h)
      hp hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb).2.2.2.2.2.2.2.2.2
    change Nat.card ((W.subgroupOf d.L).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (center d.L)))) = 4
    rw [←map_map,card_map_of_injective e.injective]
    exact hh
  let := h.elementary
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le hWV
  let : IsElementaryAbelian 2 (W.subgroupOf d.L) := IsElementaryAbelian.subgroupOf hWL
  have hWbar : IsElementaryAbelian 2 Wbar := IsElementaryAbelian.map q
  let C := M ⊓ d.G1
  let R := (pResidual 2 C).map C.subtype
  have hCR : C ≤ normalizer (R : Set G) := C.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image C (pResidual 2 C))
  have hCW : C ≤ normalizer (W : Set G) := by
    intro c hc
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [show W = ⁅V,R⁆ from rfl,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (h.normalized hc.1),
      mem_normalizer_iff_map_conj_eq.mp (hCR hc)]
  have hMW : M.subgroupOf d.L ≤ normalizer (W.subgroupOf d.L : Set d.L) := by
    apply le_normalizer_iff.mpr
    intro c hc w hw
    exact le_normalizer_iff.mp hCW c ⟨hc,d.L_component.1 c.property⟩ w hw
  have hMN : (M.subgroupOf d.L).map q ≤ normalizer (Wbar : Set Sporadic.Mathieu.M22) :=
    (map_mono hMW).trans ((W.subgroupOf d.L).le_normalizer_map q)
  have hVT : V ≤ (T : Subgroup G) := by
    let : (V.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer h.normalized
    let := IsElementaryAbelian.subgroupOf h.le_selected (p := 2)
    have hh := (IsElementaryAbelian.isPGroup 2 (V.subgroupOf M)).le_sylow_of_normal
      (T.subtype hM.1.2)
    simpa only [map_subgroupOf_eq_of_le h.le_selected,Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hM.1.2] using map_mono (f := M.subtype) hh
  have hVS : V ≤ d.S := le_inf hVT
    (V.le_centralizer.trans (centralizer_le (d.Z1_le_fixed.trans inf_le_left)))
  obtain ⟨P,hP⟩ := s.component_sylow
  have hPS : (P : Subgroup d.L) = d.S.subgroupOf d.L := by
    apply map_injective d.L.subtype_injective
    rw [hP,subgroupOf_map_subtype]
    rfl
  let Pbar := P.mapSurjective (f := q) (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hWP : Wbar ≤ (Pbar : Subgroup Sporadic.Mathieu.M22) := by
    change (W.subgroupOf d.L).map q ≤ (P : Subgroup d.L).map q
    rw [hPS]
    exact map_mono (comap_mono (hWV.trans hVS))
  have hPN : (Pbar : Subgroup Sporadic.Mathieu.M22) ≤ normalizer (Wbar : Set Sporadic.Mathieu.M22) := by
    apply le_trans (b := (M.subgroupOf d.L).map q) ?_ hMN
    change (P : Subgroup d.L).map q ≤ _
    rw [hPS]
    exact map_mono (comap_mono (d.S_le_T.trans hM.1.2))
  obtain ⟨B,hB,hWB⟩ := Sporadic.Mathieu.M22FourNormalizers.exists_hexad_kernel
    Pbar Wbar hWP hPN hWbar hc
  exact ⟨e,B,hB,hc,hWB,himage,hMN,
    Sporadic.Mathieu.M22FourNormalizers.normalizer_lt_hexad hB Wbar hWB hWbar hc,
    Sporadic.Mathieu.M22FourNormalizers.hexad_characteristicTwo hB⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Apply the fixed-plane identity to the original marker and its same selected
carrier. No exchanged-plane hypothesis is used. -/
theorem PreparedChosenModule.source_preExclusion_local_natural_fixed_carrier
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hp : m.prime = 3 ∨ m.prime = 5)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      ∀ K ∈ Chapter1.LIn d.G1 d.S, IsQuasisimple (K ⧸ pCore 2 K) →
        ¬ K ≤ d.MZ → ∀ n : ℕ, IsL2EvenBlock K n →
          m.fixedPlane = V ⊓ centralizer (d.L : Set G) ∧
            V ⊓ centralizer (K : Set G) = V ⊓ centralizer (d.L : Set G) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,?_⟩
  intro K hK hq hout n hb
  have he := s.localFamily_linearTwo_fixed_carrier (h := h) hp
    hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb
  have hk := (s.localFamily_linearTwo_full_action (h := h)
    hG hM hJ hu hfull hK hq hout hb (by omega)).2.2.1
  have hG1 : d.G1 = centralizer (m.Z1 : Set G) := by
    change centralizer (d.Z1 : Set G) = _
    rw [hZ]
  refine ⟨?_,hk.symm.trans he⟩
  rw [hG1] at he
  exact he


/-- The original marker supplies the actual moving four-group and hexad in
the literal M₂₂ central quotient, including the full V intersection and
selected-subgroup normalizer containment. -/
theorem PreparedChosenModule.source_preExclusion_local_natural_m22_hexad
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hp : m.prime = 3 ∨ m.prime = 5)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      ∀ K ∈ Chapter1.LIn d.G1 d.S, IsQuasisimple (K ⧸ pCore 2 K) →
        ¬ K ≤ d.MZ → ∀ n : ℕ, IsL2EvenBlock K n →
          ∃ e : (d.L ⧸ center d.L) ≃* Sporadic.Mathieu.M22,
            let q := e.toMonoidHom.comp (QuotientGroup.mk' (center d.L))
            let Wbar := (m.movingPlane.subgroupOf d.L).map q
            ∃ B ∈ Sporadic.Mathieu.m22Blocks,
              Nat.card Wbar = 4 ∧
              Wbar ≤ Sporadic.Mathieu.m22HexadPointwiseKernel B ∧
              (V.subgroupOf d.L).map q = Wbar ∧
              (M.subgroupOf d.L).map q ≤ normalizer (Wbar : Set Sporadic.Mathieu.M22) ∧
              normalizer (Wbar : Set Sporadic.Mathieu.M22) <
                MulAction.stabilizer Sporadic.Mathieu.M22 B ∧
              generalizedFitting (MulAction.stabilizer Sporadic.Mathieu.M22 B) =
                pCore 2 (MulAction.stabilizer Sporadic.Mathieu.M22 B) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,?_⟩
  intro K hK hq hout n hb
  have hh := s.localFamily_linearTwo_m22_hexad (h := h) hp
    hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb
  have hG1 : d.G1 = centralizer (m.Z1 : Set G) := by
    change centralizer (d.Z1 : Set G) = _
    rw [hZ]
  dsimp only at hh
  rw [hG1] at hh
  exact hh


end CFSG.Quasithin.Chapter15.Section01
