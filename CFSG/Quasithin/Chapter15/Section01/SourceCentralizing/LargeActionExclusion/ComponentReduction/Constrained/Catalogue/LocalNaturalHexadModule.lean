module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalNaturalHexadPushingUp

/-!
# The whole original module inside the covered-hexad radical

For an escaping natural local member, the moving plane lies in the
original Q₁. The intersection V ∩ Q₁ is invariant under T and the residual
of C_M(Z₁), hence under C_M(Z₁) and M. It contains the original central
seed: Z₁ lies in Q₁, and the seed bound supplies the moving summand.
The actual seed-span equality therefore gives V ≤ Q₁.

For the same full hexad lift H, the moving plane lies in O₂(H), while
the fixed plane centralizes H. The centralizer of H in HQ₁ is a normal
two-group, so both planes lie in O₂(HQ₁). Full M_Z-normalization and
radical saturation put this core inside Q₁. Consequently the entire
HQ₁-span of the original V stays in that core and in Q₁.

The original-marker application retains the same G₁, M_Z, S, Q₁, K, H,
L and literal central-cover map. No exchanged-plane premise or new
C-component assertion about K is used. The automorphic escape of O₂(H)
and the original 15.1.20(2)/15.1.22 assembly remain unresolved. Original
15.1.14 and whole-core A₆ reconstruction retain their existing producers.

Source: Aschbacher--Smith 15.1.16--20, printed pp.1092--1095;
C.2.1 and the radical saturation in C.2.7, printed pp.144,146.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterB ChapterC ChapterC.C27Source Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private theorem module_le_radical_of_moving_le
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hW : ⁅V,(pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype⁆ ≤ d.Q1) :
    V ≤ d.Q1 := by
  let C := M ⊓ d.G1
  let R := (pResidual 2 C).map C.subtype
  let A := V ⊓ d.Q1
  have hTV : (T : Subgroup G) ≤ normalizer (V : Set G) := hM.1.2.trans h.normalized
  have hTA : (T : Subgroup G) ≤ normalizer (A : Set G) :=
    (le_inf hTV s.sylow_normalizes_Q1).trans inf_normalizer_le_normalizer_inf
  have hRA : R ≤ normalizer (A : Set G) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    exact le_inf
      ((commutator_mono inf_le_left le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp
          (((map_subtype_le _).trans inf_le_left).trans h.normalized)))
      ((commutator_mono inf_le_left le_rfl).trans hW)
  have hSC : d.S ≤ C := le_inf (d.S_le_T.trans hM.1.2) d.S_le_G1
  obtain ⟨P,hP⟩ := s.centralizer_sylow.restrict hSC inf_le_right
  have hgen : R ⊔ d.S = C := by
    have hh := congrArg (map C.subtype) (pResidual_sup_sylow_eq_top P)
    simpa only [Subgroup.map_sup,hP,←MonoidHom.range_eq_map,range_subtype] using hh
  have hCA : C ≤ normalizer (A : Set G) :=
    hgen ▸ sup_le hRA (d.S_le_T.trans hTA)
  have hMA : M ≤ normalizer (A : Set G) := by
    rw [d.M_eq_centralizer_sup_sylow]
    exact sup_le hCA hTA
  have hZQ : d.Z1 ≤ d.Q1 := by
    let := h.elementary
    have hZV := d.Z1_le_fixed.trans inf_le_left
    have hZT : d.Z1 ≤ (T : Subgroup G) := by
      intro z hz
      exact thompsonJ_le _ _ ((mem_omegaOneCenterAmbient_iff _ _).mp
        (h.thompsonFixed_le_omega T hM (d.Z1_le_fixed hz))).1
    have hTMc : (T : Subgroup G) ≤ Mc := by
      have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
        hu ▸ Set.mem_singleton Mc
      intro t ht
      exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
    exact le_pCoreIn_of_normalizes
      ((IsElementaryAbelian.isPGroup 2 V).to_le hZV)
      (le_inf (hZV.trans (V.le_centralizer.trans (centralizer_le hZV))) (hZT.trans hTMc))
      (inf_le_left.trans (Subgroup.centralizer_le_normalizer _))
  have hseed : centralInvolutions T ⊓ V ≤ A :=
    le_inf inf_le_right (s.seed_bound.trans (sup_le hZQ hW))
  exact (h.seed_span.le.trans (conjugateSpanBy_le hseed hMA)).trans inf_le_right


private theorem centralizer_le_join_core (H Q : Subgroup G)
    (hfit : generalizedFitting H = pCore 2 H) (hQ : IsPGroup 2 Q)
    (hn : Q ≤ normalizer (H : Set G)) :
    (H ⊔ Q) ⊓ centralizer (H : Set G) ≤ (H ⊔ Q).pCoreIn 2 := by
  let J := H ⊔ Q
  let H0 := H.subgroupOf J
  let : H0.Normal := normal_subgroupOf_of_le_normalizer (sup_le H.le_normalizer hn)
  let C := centralizer (H0 : Set J)
  let q := QuotientGroup.mk' H0
  let f : C →* J ⧸ H0 := q.comp C.subtype
  have hgen : H0 ⊔ Q.subgroupOf J = ⊤ := by
    rw [←subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
  have hquot : IsPGroup 2 (J ⧸ H0) :=
    isPGroup_quotient_of_sup_eq_top H0 (Q.subgroupOf J) hQ.comap_subtype hgen
  have hker : IsPGroup 2 f.ker := by
    have hxH (x : f.ker) : x.val.val.val ∈ H :=
      (QuotientGroup.eq_one_iff (N := H0) x.val.val).mp x.property
    let g : f.ker →* pCore 2 H := {
      toFun := fun x => ⟨⟨x.val.val.val, hxH x⟩,by
        have hc : (⟨x.val.val.val,hxH x⟩ : H) ∈
            centralizer (pCore 2 H : Set H) := by
          intro y hy
          exact Subtype.ext (congrArg (fun z : J => z.val)
            (x.val.property ⟨y,mem_sup_left y.property⟩ y.property))
        exact hfit ▸ centralizer_generalizedFitting_le H (hfit ▸ hc)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    have hg : Function.Injective g := by
      intro x y he
      exact Subtype.ext (Subtype.ext (Subtype.ext
        (congrArg (fun z : pCore 2 H => z.val.val) he)))
    exact pCore_isPGroup.of_injective g hg
  have hpC : IsPGroup 2 C := by
    have hh := (hquot.to_subgroup (⊤ : Subgroup (J ⧸ H0))).comap_of_ker_isPGroup f hker
    rw [comap_top] at hh
    exact hh.of_equiv topEquiv
  have hCcore : C ≤ pCore 2 J := le_sSup ⟨inferInstance,hpC⟩
  intro x hx
  refine ⟨⟨x,hx.1⟩,hCcore ?_,rfl⟩
  intro y hy
  exact Subtype.ext (hx.2 y hy)

private theorem normalized_join_core_le_radical
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p) {H : Subgroup G}
    (hHG : H ≤ d.G1) (hnH : d.MZ ≤ normalizer (H : Set G)) :
    (H ⊔ d.Q1).pCoreIn 2 ≤ d.Q1 := by
  let A := (H ⊔ d.Q1).subgroupOf d.G1
  let R := d.Q1.subgroupOf d.G1
  have hQG : d.Q1 ≤ d.G1 := d.Q1_le_MZ.trans inf_le_left
  have hAG : H ⊔ d.Q1 ≤ d.G1 := sup_le hHG hQG
  have hR := caseI_intrinsic_core_radical d.G1 d.MZ inf_le_left
    s.core_nontrivial s.core_normalizer
  have hNR : normalizer (R : Set d.G1) = d.MZ.subgroupOf d.G1 := by
    rw [show R = d.Q1.subgroupOf d.G1 from rfl,←subgroupOf_normalizer_eq hQG]
    ext x
    change x.val ∈ normalizer (d.Q1 : Set G) ↔ x.val ∈ d.MZ
    exact ⟨fun hx => s.core_normalizer.le ⟨x.property,hx⟩,
      fun hx => (s.core_normalizer.ge hx).2⟩
  have hnQ : d.MZ ≤ normalizer (d.Q1 : Set G) :=
    fun _ hx => (s.core_normalizer.ge hx).2
  have hNA : normalizer (R : Set d.G1) ≤ normalizer (A : Set d.G1) := by
    rw [hNR]
    have hnJ := (le_inf hnH hnQ).trans
      (normalizer_inf_normalizer_le_normalizer_sup H d.Q1)
    exact (comap_mono hnJ).trans (le_normalizer_comap d.G1.subtype)
  have hcore : A.pCoreIn 2 ≤ R :=
    le_of_normalizer_le_normalizer_of_pCore_normalizer_le R _ hR.isPGroup
      (isPGroup_pCoreIn 2 A) hR.2.le (hNA.trans
        (normalizer_le_normalizer_characteristic_image A (pCore 2 A)))
  have hm := map_mono (f := d.G1.subtype) hcore
  rw [map_pCoreIn_of_injective 2 A _ d.G1.subtype_injective] at hm
  simpa only [A,R,map_subgroupOf_eq_of_le hAG,map_subgroupOf_eq_of_le hQG] using hm


/-- The whole original module and its span under the same full hexad join
lie in the join core and the original radical. -/
theorem PreExclusionSource.localFamily_linearTwo_m22_module_radical
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
    V ≤ d.Q1 ∧
    ∃ e : (d.L ⧸ center d.L) ≃* Sporadic.Mathieu.M22,
      ∃ B ∈ Sporadic.Mathieu.m22Blocks,
        let q := e.toMonoidHom.comp (QuotientGroup.mk' (center d.L))
        let H := ((MulAction.stabilizer Sporadic.Mathieu.M22 B).comap q).map d.L.subtype
        d.ML ≤ H ∧ d.MZ ≤ normalizer (H : Set G) ∧ K ⊔ H = d.L ∧
        V ⊔ H.pCoreIn 2 ≤ (H ⊔ d.Q1).pCoreIn 2 ∧
        (H ⊔ d.Q1).pCoreIn 2 ≤ d.Q1 ∧
        conjugateSpanBy V (H ⊔ d.Q1) ≤ (H ⊔ d.Q1).pCoreIn 2 := by
  obtain ⟨e,B,hB,hMH,hHL,hSH,hZH,hperfect,hfit,hcore,hV,hcard,hmodel,hindex,
      hnotM,hnotZ,hCN,hlocal,hmoved,hmax,hKH,hgen,hMLH,hMZN,hHQ,hVQ⟩ :=
    s.localFamily_linearTwo_m22_hexad_invariant (h := h) hp
      hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center d.L))
  let H := ((MulAction.stabilizer Sporadic.Mathieu.M22 B).comap q).map d.L.subtype
  let W := ⁅V,(pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype⁆
  let F := V ⊓ centralizer
    ((pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype : Set G)
  obtain ⟨hsplit,_,_,_⟩ := s.localFamily_linearTwo_full_action (h := h)
    hG hM hJ hu hfull hK hq hout hb (by omega)
  have hKL := (s.localFamily_linearTwo_selected_carrier (h := h)
    hG hM hJ hu hne hmany hfull hres hK hq hout hb (by omega)).1.le
  have hWU := (s.localFamily_linearTwo_moving_plane_bound (h := h)
    hG hM hJ hu hfull hK hq hout hb (by omega)).1
  have hWV : W ≤ V := le_sup_left.trans hsplit.symm.le
  have hWL : W ≤ d.L := hWU.trans ((map_subtype_le _).trans hKL)
  have hWQ : W ≤ d.Q1 := (le_inf hWV hWL).trans hVQ
  have hVQall := module_le_radical_of_moving_le (h := h) s hM hu hWQ
  have hn : d.Q1 ≤ normalizer (H : Set G) := d.Q1_le_MZ.trans hMZN
  have hQcore : H.pCoreIn 2 ≤ (H ⊔ d.Q1).pCoreIn 2 := by
    apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H)
      ((pCoreIn_le 2 H).trans le_sup_left)
    exact (sup_le H.le_normalizer hn).trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hFC : F ≤ centralizer (H : Set G) :=
    ((s.localFamily_linearTwo_fixed_carrier (h := h) hp
      hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb).le.trans inf_le_right).trans
        (centralizer_le hHL.le)
  have hFcore : F ≤ (H ⊔ d.Q1).pCoreIn 2 :=
    (le_inf ((inf_le_left.trans hVQall).trans le_sup_right) hFC).trans
      (centralizer_le_join_core H d.Q1 hfit (isPGroup_pCoreIn 2 d.MZ) hn)
  have hmodule : V ≤ (H ⊔ d.Q1).pCoreIn 2 :=
    hsplit.le.trans (sup_le (((le_inf hWV hWL).trans hV).trans hQcore) hFcore)
  refine ⟨hVQall,e,B,hB,hMLH,hMZN,hgen,sup_le hmodule hQcore,
    normalized_join_core_le_radical (h := h) s (hHL.le.trans d.L_component.1) hMZN,?_⟩
  exact conjugateSpanBy_le hmodule ((H ⊔ d.Q1).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (H ⊔ d.Q1)
      (pCore 2 (H ⊔ d.Q1 : Subgroup G))))

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterC.C27Source Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The whole original module and its hexad-join span lie in the same radical,
retaining the original marker, prime and full central-cover map. -/
theorem PreparedChosenModule.source_preExclusion_local_natural_m22_module_radical
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
          m.prime = 3 ∧ n = 2 ∧ V ≤ d.Q1 ∧
          ∃ e : (d.L ⧸ center d.L) ≃* Sporadic.Mathieu.M22,
            ∃ B ∈ Sporadic.Mathieu.m22Blocks,
              let q := e.toMonoidHom.comp (QuotientGroup.mk' (center d.L))
              let H := ((MulAction.stabilizer Sporadic.Mathieu.M22 B).comap q).map d.L.subtype
              d.ML ≤ H ∧ d.MZ ≤ normalizer (H : Set G) ∧ K ⊔ H = d.L ∧
              V ⊔ H.pCoreIn 2 ≤ (H ⊔ d.Q1).pCoreIn 2 ∧
              (H ⊔ d.Q1).pCoreIn 2 ≤ d.Q1 ∧
              conjugateSpanBy V (H ⊔ d.Q1) ≤ (H ⊔ d.Q1).pCoreIn 2 := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,?_⟩
  intro K hK hq hout n hb
  obtain ⟨hp3,hn,_,_⟩ := s.localFamily_linearTwo_moving_plane_four (h := h)
    hp hG hM hJ hu hfull hK hq hout hb
  exact ⟨hp3,hn,s.localFamily_linearTwo_m22_module_radical (h := h) hp
    hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb⟩

end CFSG.Quasithin.Chapter15.Section01
