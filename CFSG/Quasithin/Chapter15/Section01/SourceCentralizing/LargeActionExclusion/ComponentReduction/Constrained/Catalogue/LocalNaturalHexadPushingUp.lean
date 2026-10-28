module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalNaturalHexadInvariant
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.AlternatingSixMS

/-!
# Original pushing-up constraints on the full covered hexad

For an original natural escape, let H be the full hexad lift in the same
selected M₂₂ carrier. The proved M_Z-normalization makes H normal in
D = H M_Z. This D contains the whole G₁-normalizer M_Z of Q₁, so Q₁ remains
radical in D. The original characteristic-normalizer control also restricts
to D. Perfectness and the A₆ core quotient make H a genuine C-component
of D, giving C.2.7 without asserting that H is a C-component of G₁.

The original M_Z supplies the odd-index core witness for the MS conditions
on H Q₁. Centerlessness of H/O₂(H) makes the literal core-to-star map an
isomorphism. Thus the kernel, best-offender and A₆ MS inputs are all proved
on the actual original subgroups, with the complete central cover retained.

Characteristic control gives a further obstruction: some automorphism of
Q₁ moves O₂(H) outside O₂(H Q₁). Otherwise the characteristic subgroup
spanned by all its images stays in that core. Since
[O₂(H Q₁), H] ≤ O₂(H), H normalizes this nontrivial characteristic subgroup
of Q₁, contradicting H outside M_Z. In particular O₂(H) is not
characteristic in Q₁.

Excluding this automorphic escape through the covered-M₂₂ structure remains
open, as do general natural Borel containment and the final 15.1.20(2) and
15.1.22 assembly. No whole-core A₆ reconstruction is assumed here; that
independent input and original 15.1.14 retain their existing producers.

Source: Aschbacher--Smith C.1.3, C.1.31 and C.2.7, printed pp.122,135,
145--147; original 15.1.18--20 and 15.1.22, pp.1092--1100.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC ChapterC.C27Source Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private theorem hexad_join_input
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {H : Subgroup G} (hHG : H ≤ d.G1)
    (hn : d.MZ ≤ normalizer (H : Set G))
    (hp : Group.IsPerfect H) (hq : IsQuasisimple (H ⧸ pCore 2 H))
    (hf : generalizedFitting H = pCore 2 H) (hout : ¬ H ≤ d.MZ) :
    Input KnownSimple.IsKnownSimple (H ⊔ d.MZ) d.Q1 d.MZ H := by
  let D := H ⊔ d.MZ
  have hDG : D ≤ d.G1 := sup_le hHG inf_le_left
  have hQD : d.Q1 ≤ D := d.Q1_le_MZ.trans le_sup_right
  have hMN : d.MZ ≤ normalizer (d.Q1 : Set G) :=
    d.MZ.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image d.MZ (pCore 2 d.MZ))
  have hDN : D ⊓ normalizer (d.Q1 : Set G) = d.MZ := by
    apply le_antisymm
    · exact (inf_le_inf_right _ hDG).trans s.core_normalizer.le
    · exact le_inf le_sup_right hMN
  have hDC : D ⊓ Mc = d.MZ := le_antisymm
    (inf_le_inf_right _ hDG) (le_inf le_sup_right inf_le_right)
  have hcontrol : (d.Q1.subgroupOf D).characteristicNormalizerClosure ≤ d.MZ.subgroupOf D := by
    rw [←hDC]
    exact caseI_intrinsic_characteristic_control D Mc d.Q1 hQD s.characteristic_control
  let : (d.Q1.subgroupOf d.MZ).Normal := normal_subgroupOf_of_le_normalizer hMN
  have hclosure :
      (normalClosure (d.Q1.subgroupOf d.MZ : Set d.MZ)).map d.MZ.subtype = d.Q1 := by
    rw [normalClosure_eq_self,map_subgroupOf_eq_of_le d.Q1_le_MZ]
  have hsy : Chapter1.IsSylowIn 2 d.Q1
      ((normalClosure (d.Q1.subgroupOf d.MZ : Set d.MZ)).map d.MZ.subtype) := by
    rw [hclosure]
    exact Chapter1.isSylowIn_iff.mpr ⟨isPGroup_pCoreIn 2 d.MZ,le_rfl,
      fun U _ hQU hUQ => le_antisymm hUQ hQU⟩
  let H0 := H.subgroupOf D
  let e : H0 ≃* H := subgroupOfEquivOfLe le_sup_left
  let : H0.Normal := normal_subgroupOf_of_le_normalizer (sup_le H.le_normalizer hn)
  let : Group.IsPerfect H := hp
  let : Group.IsPerfect H0 := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : IsQuasisimple (H ⧸ pCore 2 H) := hq
  let : IsQuasisimple (H0 ⧸ pCore 2 H0) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hp0 : IsPPerfect 2 H0 := by
    intro N hN hquot
    let := hN
    let : Group.IsNilpotent (H0 ⧸ N) := hquot.isNilpotent
    exact top_le_iff.mp (le_of_isPerfect_of_solvable_quotient ⊤ N)
  have hc : H0.IsCComponent := isCComponent_of_isPPerfect_of_quasisimple_core_quotient
    (inferInstance : H0.Normal).isSubnormal hp0
  let := h.elementary
  have hsq := caseI_centralizer_sqtk hG d.Z1 d.Z1_ne_bot
    ((IsElementaryAbelian.isPGroup 2 V).to_le (d.Z1_le_fixed.trans inf_le_left))
  refine ⟨⟨?_,hQD,le_sup_right,
      caseI_intrinsic_core_radical D d.MZ le_sup_right s.core_nontrivial hDN,hcontrol,hsy⟩,
    ⟨le_sup_left,hc⟩,hq,hf,hout,d.Q1_le_MZ.trans hn⟩
  exact (IsSQTK.equiv (subgroupOfEquivOfLe hDG)).mp (hsq.subgroup (D.subgroupOf d.G1))

private theorem hexad_core_not_characteristic
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    {H : Subgroup G} (hHG : H ≤ d.G1) (hHQ : H.pCoreIn 2 ≤ d.Q1)
    (hne : H.pCoreIn 2 ≠ ⊥) (hout : ¬ H ≤ d.MZ) :
    ¬ ((H.pCoreIn 2).subgroupOf d.Q1).Characteristic := by
  intro hc
  let U := (H.pCoreIn 2).subgroupOf d.Q1
  let : U.Characteristic := hc
  have hmap : U.map d.Q1.subtype = H.pCoreIn 2 := map_subgroupOf_eq_of_le hHQ
  have hU : U ≠ ⊥ := by
    intro he
    rw [he,Subgroup.map_bot] at hmap
    exact hne hmap.symm
  have hn : H ≤ normalizer (U.map d.Q1.subtype : Set G) := by
    rw [hmap]
    exact H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hMc : H ≤ Mc := hn.trans
    ((normalizer_le_characteristicNormalizerClosure d.Q1 U hU).trans s.characteristic_control)
  exact hout (le_inf hHG hMc)

private theorem hexad_core_automorphic_escape
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    {H : Subgroup G} (hHG : H ≤ d.G1) (hHQ : H.pCoreIn 2 ≤ d.Q1)
    (hne : H.pCoreIn 2 ≠ ⊥) (hout : ¬ H ≤ d.MZ)
    (hn : d.Q1 ≤ normalizer (H : Set G)) :
    ∃ a : MulAut d.Q1,
      ¬ (((H.pCoreIn 2).subgroupOf d.Q1).map a.toMonoidHom).map d.Q1.subtype ≤
        (H ⊔ d.Q1).pCoreIn 2 := by
  classical
  let U := (H.pCoreIn 2).subgroupOf d.Q1
  let C : Subgroup d.Q1 := ⨆ a : MulAut d.Q1, U.map a.toMonoidHom
  let N := (H ⊔ d.Q1).pCoreIn 2
  have hUC : U ≤ C := by
    have he := le_iSup (fun a : MulAut d.Q1 => U.map a.toMonoidHom) (MulEquiv.refl d.Q1)
    change U.map (MonoidHom.id d.Q1) ≤ C at he
    simpa only [map_id] using he
  have hchar : C.Characteristic := by
    apply characteristic_iff_map_le.mpr
    intro a
    change (⨆ b : MulAut d.Q1, U.map b.toMonoidHom).map a.toMonoidHom ≤ C
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro b
    rw [map_map]
    exact le_iSup_of_le (b.trans a) le_rfl
  let : C.Characteristic := hchar
  have hcoreC : H.pCoreIn 2 ≤ C.map d.Q1.subtype := by
    rw [←map_subgroupOf_eq_of_le hHQ]
    exact map_mono hUC
  have hCne : C ≠ ⊥ := by
    intro he
    rw [he,Subgroup.map_bot] at hcoreC
    exact hne (bot_unique hcoreC)
  by_contra! hall
  have hCN : C.map d.Q1.subtype ≤ N := by
    change (⨆ a : MulAut d.Q1, U.map a.toMonoidHom).map d.Q1.subtype ≤ N
    rw [Subgroup.map_iSup]
    exact iSup_le hall
  have hNH : N ≤ normalizer (H : Set G) :=
    (pCoreIn_le 2 (H ⊔ d.Q1)).trans (sup_le H.le_normalizer hn)
  have hHN : H ≤ normalizer (N : Set G) :=
    (le_sup_left.trans (H ⊔ d.Q1).le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image (H ⊔ d.Q1) (pCore 2 (H ⊔ d.Q1 : Subgroup G)))
  have hcomm : ⁅N,H⁆ ≤ H.pCoreIn 2 :=
    (le_inf (le_normalizer_iff_commutator_le_right.mp hNH)
      (le_normalizer_iff_commutator_le_left.mp hHN)).trans
      (inf_pCoreIn_le_of_le 2 (show H ≤ H ⊔ d.Q1 from le_sup_left))
  have hHC : H ≤ normalizer (C.map d.Q1.subtype : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr
      (((commutator_mono hCN le_rfl).trans hcomm).trans hcoreC)
  exact hout (le_inf hHG (hHC.trans
    ((normalizer_le_characteristicNormalizerClosure d.Q1 C hCne).trans s.characteristic_control)))

/-- The original radical gives genuine C.2.7 and MS data on the covered
hexad join. Its automorphism orbit cannot remain inside the join's two-core. -/
theorem PreExclusionSource.localFamily_linearTwo_m22_hexad_pushingUp
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
    ∃ e : (d.L ⧸ center d.L) ≃* Sporadic.Mathieu.M22,
      ∃ B ∈ Sporadic.Mathieu.m22Blocks,
        let q := e.toMonoidHom.comp (QuotientGroup.mk' (center d.L))
        let H := ((MulAction.stabilizer Sporadic.Mathieu.M22 B).comap q).map d.L.subtype
        d.ML ≤ H ∧ d.MZ ≤ normalizer (H : Set G) ∧
        H.pCoreIn 2 ≤ d.Q1 ∧ K ⊔ H = d.L ∧
        ¬ ((H.pCoreIn 2).subgroupOf d.Q1).Characteristic ∧
        (∃ a : MulAut d.Q1,
          ¬ (((H.pCoreIn 2).subgroupOf d.Q1).map a.toMonoidHom).map d.Q1.subtype ≤
            (H ⊔ d.Q1).pCoreIn 2) ∧
        ∃ hi : Input KnownSimple.IsKnownSimple (H ⊔ d.MZ) d.Q1 d.MZ H,
          KernelConclusion H d.Q1 ∧ OffenderConclusion H d.Q1 ∧
          Nonempty (AlternatingSixMS.Input KnownSimple.IsKnownSimple
            (H.subgroupOf (H ⊔ d.Q1)) (d.Q1.subgroupOf (H ⊔ d.Q1))) ∧
          ∃ c : (H ⧸ pCore 2 H) ≃* starImage H d.Q1 H,
            ∀ x, c x = coreToStar hi.normalizes x := by
  obtain ⟨e,B,hB,hMH,hHL,hSH,hZH,hperfect,hfit,hcore,hV,hcard,hmodel,hindex,
      hnotM,hnotZ,hCN,hlocal,hmoved,hmax,hKH,hgen,hMLH,hMZN,hHQ,hVQ⟩ :=
    s.localFamily_linearTwo_m22_hexad_invariant (h := h) hp
      hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center d.L))
  let H := ((MulAction.stabilizer Sporadic.Mathieu.M22 B).comap q).map d.L.subtype
  obtain ⟨a⟩ := hmodel
  let : IsQuasisimple (alternatingGroup (Fin 6)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := by
      let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
      exact ((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  have hqH : IsQuasisimple (H ⧸ pCore 2 H) := IsQuasisimple.of_mulEquiv a.symm
  have hi := hexad_join_input (h := h) s hG (hHL.le.trans d.L_component.1)
    hMZN hperfect hqH hfit hnotZ
  have hSD : d.S ≤ H ⊔ d.MZ := by
    have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hu ▸ Set.mem_singleton Mc
    apply le_trans (b := d.MZ) _ le_sup_right
    exact le_inf d.S_le_G1 (fun x hx => hMc.2 (fun z hz =>
      (centralInvolutions_le_centralizer_sylow T hz x (d.S_le_T hx)).symm))
  obtain ⟨P,hP⟩ := s.centralizer_sylow.restrict hSD
    (sup_le (hHL.le.trans d.L_component.1) inf_le_left)
  have hPM : (P : Subgroup (H ⊔ d.MZ : Subgroup G)) ≤ d.MZ.subgroupOf (H ⊔ d.MZ) := by
    intro x hx
    have hxS : x.val ∈ d.S := hP ▸ mem_map_of_mem (H ⊔ d.MZ : Subgroup G).subtype hx
    have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hu ▸ Set.mem_singleton Mc
    exact ⟨d.S_le_G1 hxS,hMc.2 (fun z hz =>
      (centralInvolutions_le_centralizer_sylow T hz x (d.S_le_T hxS)).symm)⟩
  have hodd := msOddIndexRadical_of_first_core hi d.MZ le_sup_right le_rfl P hPM rfl
  have hz : center (H ⧸ pCore 2 H) = ⊥ := by
    apply bot_unique
    intro x hx
    exact a.map_eq_one_iff.mp
      ((alternatingGroup.center_eq_bot (by simp)).le ((centerCongr a ⟨x,hx⟩).property))
  let c : (H ⧸ pCore 2 H) ≃* starImage H d.Q1 H := MulEquiv.ofBijective
    (coreToStar hi.normalizes)
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (bot_unique
      ((coreToStar_ker_central_from_source hi).trans hz.le)),coreToStar_surjective hi.normalizes⟩
  have hcoreNe : H.pCoreIn 2 ≠ ⊥ := by
    intro he
    have he' : pCore 2 H = ⊥ := map_injective H.subtype_injective
      (he.trans (Subgroup.map_bot H.subtype).symm)
    change Nat.card (pCore 2 H) = _ at hcard
    rw [he',card_bot] at hcard
    have hp := Nat.card_pos (α := center d.L)
    omega
  have hnotchar := hexad_core_not_characteristic (h := h) s (hHL.le.trans d.L_component.1)
    hHQ hcoreNe hnotZ
  have hescape := hexad_core_automorphic_escape (h := h) s
    (hHL.le.trans d.L_component.1) hHQ hcoreNe hnotZ hi.normalizes
  obtain ⟨hkernel,hoffender⟩ := kernel_offender_from_source hi
  exact ⟨e,B,hB,hMLH,hMZN,hHQ,hgen,hnotchar,hescape,hi,hkernel,hoffender,
    ⟨alternatingSixMSInput_from_source hi hodd (c.symm.trans a)⟩,c,fun _ => rfl⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData


namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterC.C27Source Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The original marker gives the actual hexad pushing-up and MS inputs,
with its original prime, radical and full central-cover map. -/
theorem PreparedChosenModule.source_preExclusion_local_natural_m22_hexad_pushingUp
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
          m.prime = 3 ∧ n = 2 ∧
          ∃ e : (d.L ⧸ center d.L) ≃* Sporadic.Mathieu.M22,
            ∃ B ∈ Sporadic.Mathieu.m22Blocks,
              let q := e.toMonoidHom.comp (QuotientGroup.mk' (center d.L))
              let H := ((MulAction.stabilizer Sporadic.Mathieu.M22 B).comap q).map d.L.subtype
              d.ML ≤ H ∧ d.MZ ≤ normalizer (H : Set G) ∧
              H.pCoreIn 2 ≤ d.Q1 ∧ K ⊔ H = d.L ∧
              ¬ ((H.pCoreIn 2).subgroupOf d.Q1).Characteristic ∧
              (∃ a : MulAut d.Q1,
                ¬ (((H.pCoreIn 2).subgroupOf d.Q1).map a.toMonoidHom).map d.Q1.subtype ≤
                  (H ⊔ d.Q1).pCoreIn 2) ∧
              ∃ hi : Input KnownSimple.IsKnownSimple (H ⊔ d.MZ) d.Q1 d.MZ H,
                KernelConclusion H d.Q1 ∧ OffenderConclusion H d.Q1 ∧
                Nonempty (AlternatingSixMS.Input KnownSimple.IsKnownSimple
                  (H.subgroupOf (H ⊔ d.Q1)) (d.Q1.subgroupOf (H ⊔ d.Q1))) ∧
                ∃ c : (H ⧸ pCore 2 H) ≃* starImage H d.Q1 H,
                  ∀ x, c x = coreToStar hi.normalizes x := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,?_⟩
  intro K hK hq hout n hb
  obtain ⟨hp3,hn,_,_⟩ := s.localFamily_linearTwo_moving_plane_four (h := h)
    hp hG hM hJ hu hfull hK hq hout hb
  exact ⟨hp3,hn,s.localFamily_linearTwo_m22_hexad_pushingUp (h := h) hp
    hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb⟩

end CFSG.Quasithin.Chapter15.Section01
