module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalNaturalFixedCarrier
public import Theory.Mathieu.M22.CentralCover.HexadPerfect
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.Ambient
public import Theory.GroupTheory.GeneralizedFitting.CentralCoverLift

/-!
# The full hexad lift of an original natural local escape

The remaining M₂₂ geometry lifts through the literal map L → L/Z(L) → M₂₂.
The full hexad preimage H is perfect, has characteristic two and quotient
H/O₂(H) isomorphic to A₆. Its two-core is the full inverse image of the
native hexad kernel, of order 16·|Z(L)|, and contains V intersect L.
It has index 77 in L and strictly contains the original M intersect L.

The original C_M(Z₁) normalizes the same moving four-group and L. Full
M₂₂ automorphism coverage shows that it preserves the four-group's fixed
hexad. Hence it normalizes H, so H belongs to the original L(G₁,S).
The original natural Borel witnesses H escaping M_Z, and the existing
local-family action theorem gives [H,J(S)] = H.

The original-marker application retains the same component, cubic prime,
natural degree two, row and full central cover. This constructs an eligible
larger local member; it does not yet exclude the original natural escape.
The ambient exclusion and 15.1.20(2)/15.1.22 assembly remain with this owner.
Original 15.1.14 and the whole-core A₆ reconstruction retain their producers.

Source: Aschbacher--Smith 15.1.20(2), 15.1.22, printed pp.1094--1100;
I.2.2(6), p.412, for the full hexad cover; native four-group geometry as
used in 15.3.43, p.1140, with the actual source hypotheses verified here.
-/

public section
open Subgroup Theory.GroupTheory Sporadic.Mathieu
open Sporadic.Mathieu.M22CentralCover
open scoped Pointwise

private theorem hexad_core_eq {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    pCore 2 (MulAction.stabilizer M22 B) = (m22SetAction B).ker := by
  let H := MulAction.stabilizer M22 B
  let N := (m22SetAction B).ker
  let e := m22HexadQuotientAlternatingEquiv hB
  let := m22HexadKernel_elementaryAbelian hB
  have hbot : pCore 2 (alternatingGroup (Fin 6)) = ⊥ := by
    rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top (by simp : 5 ≤ Nat.card (Fin 6))
      (N := pCore 2 (alternatingGroup (Fin 6))) with hh | hh
    · exact hh
    · have hp := pCore_isPGroup (p := 2) (G := alternatingGroup (Fin 6))
      have hc : Nat.card (pCore 2 (alternatingGroup (Fin 6))) = 360 := by
        rw [hh,card_top,nat_card_alternatingGroup,Nat.card_fin]
        decide
      obtain ⟨n,hn⟩ := hp.exists_card_eq
      have hd : 3 ∣ 2 ^ n := hn ▸ hc.symm ▸ (by decide : 3 ∣ 360)
      exact False.elim ((by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd))
  let f := e.toMonoidHom.comp (QuotientGroup.mk' N)
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = N := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hfk : IsPGroup 2 f.ker := hk ▸ IsElementaryAbelian.isPGroup 2 N
  have hh := f.comap_pCore_of_ker_isPGroup hf hfk
  rw [hbot] at hh
  change f.ker = pCore 2 (MulAction.stabilizer M22 B) at hh
  exact hh.symm.trans hk

private theorem full_hexad_shape {A : Type*} [Group A] [Finite A] [Group.IsPerfect A]
    (e : (A ⧸ center A) ≃* M22) (hZ : IsPGroup 2 (center A))
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    let H := preimage e (MulAction.stabilizer M22 B)
    Group.IsPerfect H ∧ generalizedFitting H = pCore 2 H ∧
      H.pCoreIn 2 = preimage e (m22HexadPointwiseKernel B) ∧
      Nat.card (pCore 2 H) = 16 * Nat.card (center A) ∧
      Nonempty ((H ⧸ pCore 2 H) ≃* alternatingGroup (Fin 6)) ∧
      H.index = 77 := by
  intro H
  let f := localProjection e (MulAction.stabilizer M22 B)
  have hf := localProjection_surjective e (MulAction.stabilizer M22 B)
  have hk : IsPGroup 2 f.ker := by
    rw [localProjection_ker]
    exact hZ.comap_subtype
  have hfit : generalizedFitting H = pCore 2 H := by
    apply le_antisymm ?_ ((pCore_le_fitting H 2).trans (fitting_le_generalizedFitting H))
    have hh := map_generalizedFitting_le_of_surjective f hf
    rw [M22FourNormalizers.hexad_characteristicTwo hB] at hh
    have he := map_le_iff_le_comap.mp hh
    rwa [f.comap_pCore_of_ker_isPGroup hf hk] at he
  have hcore : H.pCoreIn 2 = preimage e (m22HexadPointwiseKernel B) := by
    change (pCore 2 (preimage e (MulAction.stabilizer M22 B))).map
      (preimage e (MulAction.stabilizer M22 B)).subtype = _
    rw [←preimage_twoCore e hZ,hexad_core_eq hB]
    rfl
  have hc : Nat.card (pCore 2 H) = 16 * Nat.card (center A) := by
    rw [←card_map_of_injective (f := H.subtype) H.subtype_injective]
    change Nat.card (H.pCoreIn 2) = _
    rw [hcore,preimage_card,m22HexadPointwiseKernel_card hB]
  have he : Nonempty ((H ⧸ pCore 2 H) ≃* alternatingGroup (Fin 6)) :=
    ⟨(f.pCoreQuotientEquiv hf hk).trans
      ((QuotientGroup.quotientMulEquivOfEq (hexad_core_eq hB)).trans
        (m22HexadQuotientAlternatingEquiv hB))⟩
  have hi : H.index = 77 := by
    change ((MulAction.stabilizer M22 B).comap (projection e)).index = 77
    rw [index_comap_of_surjective _ (projection_surjective e)]
    have hh := (MulAction.stabilizer M22 B).card_mul_index
    rw [m22Hexad_stabilizer_card hB,m22_order] at hh
    omega
  exact ⟨hexadPreimage_isPerfect e hZ hB,hfit,hcore,hc,he,hi⟩


private theorem hexad_invariant_of_four_invariant
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (W : Subgroup M22) (hW : W ≤ m22HexadPointwiseKernel B) (hne : W ≠ ⊥)
    (a : MulAut M22) (ha : W.map a.toMonoidHom = W) :
    (MulAction.stabilizer M22 B).map a.toMonoidHom = MulAction.stabilizer M22 B := by
  open M22ValueBound.Concrete in
  obtain ⟨g,hg⟩ := m22DesignAutToAut_surjective a
  have hcomp : (MulAut.conj g).toMonoidHom.comp M22ValueBound.Concrete.inclusion =
      M22ValueBound.Concrete.inclusion.comp a.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    change g.val * x.val * g.val⁻¹ = (a x).val
    rw [←hg,m22DesignAutToAut_apply_perm]
  have hgn : g ∈ normalizer (W.map M22ValueBound.Concrete.inclusion : Set m22DesignAut) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (W.map M22ValueBound.Concrete.inclusion).map
      (MulAut.conj g).toMonoidHom = _
    rw [map_map,hcomp,←map_map,ha]
  have hgb := M22FourNormalizers.outer_normalizer_le_hexad hB W hW hne hgn
  have hfix : (g.val : Equiv.Perm (Fin 22)) • B = B := hgb
  have hfixi : (g.val⁻¹ : Equiv.Perm (Fin 22)) • B = B := by
    have hh := congrArg (fun C : Finset (Fin 22) => g.val⁻¹ • C) hfix
    simpa only [inv_smul_smul] using hh.symm
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x,hx,rfl⟩
    change (a x).val • B = B
    rw [←hg,m22DesignAutToAut_apply_perm,mul_smul,mul_smul,hfixi]
    change g.val • (x.val • B) = B
    rw [show x.val • B = B from hx,hfix]
  · rw [card_map_of_injective (f := a.toMonoidHom) a.injective]

private theorem full_hexad_normalized
    {A : Type*} [Group A] [Finite A] (L C W : Subgroup A)
    (hCL : C ≤ normalizer (L : Set A)) (hCW : C ≤ normalizer (W : Set A))
    (e : (L ⧸ center L) ≃* M22)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (hWB : (W.subgroupOf L).map (projection e) ≤ m22HexadPointwiseKernel B)
    (hne : (W.subgroupOf L).map (projection e) ≠ ⊥) :
    C ≤ normalizer ((preimage e (MulAction.stabilizer M22 B)).map L.subtype : Set A) := by
  apply le_normalizer_iff.mpr
  intro c hc x hx
  obtain ⟨l,hl,rfl⟩ := hx
  let a := L.normalizerMonoidHom ⟨c,hCL hc⟩
  let b := MulAut.centralQuotientAction e a
  have ha : (W.subgroupOf L).map a.toMonoidHom = W.subgroupOf L := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨w,hw,rfl⟩
      exact le_normalizer_iff.mp hCW c hc w hw
    · rw [card_map_of_injective (f := a.toMonoidHom) a.injective]
  have hcomp : (projection e).comp a.toMonoidHom = b.toMonoidHom.comp (projection e) := by
    apply MonoidHom.ext
    intro y
    exact (MulAut.centralQuotientAction_apply e a y).symm
  have hb : ((W.subgroupOf L).map (projection e)).map b.toMonoidHom =
      (W.subgroupOf L).map (projection e) := by
    rw [map_map,←hcomp,←map_map,ha]
  have hBfix := hexad_invariant_of_four_invariant hB _ hWB hne b hb
  have him : b (projection e l) ∈ MulAction.stabilizer M22 B :=
    hBfix ▸ mem_map_of_mem b.toMonoidHom hl
  refine ⟨a l,?_,rfl⟩
  change projection e (a l) ∈ MulAction.stabilizer M22 B
  exact (MulAut.centralQuotientAction_apply e a l) ▸ him


namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC Section03 Section03.InitialSource ChapterA.Section05To06 Stellmacher
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- An escaping original natural member supplies a larger eligible local
subgroup through the full central cover. Its original selected intersection,
two-core, A₆ quotient, normalizer action and Thompson movement are retained. -/
theorem PreExclusionSource.localFamily_linearTwo_m22_full_hexad
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
    ∃ e : (d.L ⧸ center d.L) ≃* M22, ∃ B ∈ m22Blocks,
      let q := e.toMonoidHom.comp (QuotientGroup.mk' (center d.L))
      let H := ((MulAction.stabilizer M22 B).comap q).map d.L.subtype
      (M ⊓ d.L) < H ∧ H < d.L ∧ d.SL ≤ H ∧
      (center d.L).map d.L.subtype ≤ H ∧
      Group.IsPerfect H ∧ generalizedFitting H = pCore 2 H ∧
      H.pCoreIn 2 = ((m22HexadPointwiseKernel B).comap q).map d.L.subtype ∧
      V ⊓ d.L ≤ H.pCoreIn 2 ∧
      Nat.card (pCore 2 H) = 16 * Nat.card (center d.L) ∧
      Nonempty ((H ⧸ pCore 2 H) ≃* alternatingGroup (Fin 6)) ∧
      H.relIndex d.L = 77 ∧ ¬ H ≤ M ∧ ¬ H ≤ d.MZ ∧
      M ⊓ d.G1 ≤ normalizer (H : Set G) ∧ H ∈ Chapter1.LIn d.G1 d.S ∧
      ⁅H,elementaryAbelianMaxJ d.S⁆ = H := by
  obtain ⟨e,B,hB,hW,hWB,hV,hMN,hstrict,_⟩ :=
    s.localFamily_linearTwo_m22_hexad (h := h) hp
      hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb
  let q := projection e
  let J := preimage e (MulAction.stabilizer M22 B)
  let H := J.map d.L.subtype
  have hL : IsComponent d.G1 (d.L.subgroupOf d.G1) := by
    rcases d.ordinary_or_constrained s.odd_core with hc | hf
    · exact hc
    · exact (hout (s.localFamily_linearTwo_le_MZ_of_constrained_carrier (h := h)
        hp hG hempty hM hJ hu hne hmany hfull hres hK hq hb hf)).elim
  let : IsQuasisimple d.L := IsQuasisimple.of_mulEquiv (hG := hL.2)
    (subgroupOfEquivOfLe d.L_component.1)
  have hZ := (s.ordinary hL).center_two
  obtain ⟨hperfect,hfit,hcore,hcard,hmodel,hindex⟩ := full_hexad_shape e hZ hB
  let : Group.IsPerfect J := hperfect
  let eJ : J ≃* H := J.equivMapOfInjective d.L.subtype d.L.subtype_injective
  have hMLJ : M.subgroupOf d.L ≤ J := map_le_iff_le_comap.mp (hMN.trans hstrict.le)
  have hMstrict : M.subgroupOf d.L < J := by
    refine lt_iff_le_not_ge.mpr ⟨hMLJ,?_⟩
    intro hh
    have him : J.map q = MulAction.stabilizer M22 B :=
      map_comap_eq_self_of_surjective (projection_surjective e) _
    exact hstrict.not_ge (him.symm.le.trans ((map_mono hh).trans hMN))
  have hMH : M ⊓ d.L < H := by
    have hh := hMstrict
    refine lt_iff_le_not_ge.mpr ⟨?_,?_⟩
    · rintro x ⟨hxM,hxL⟩
      exact ⟨⟨x,hxL⟩,hMLJ hxM,rfl⟩
    · intro hle
      apply hh.not_ge
      intro x hx
      exact (hle (mem_map_of_mem d.L.subtype hx)).1
  have hHL : H ≤ d.L := map_subtype_le J
  have hidx : H.relIndex d.L = 77 := by
    change (H.subgroupOf d.L).index = 77
    rw [show H.subgroupOf d.L = J from
      comap_map_eq_self_of_injective d.L.subtype_injective J]
    exact hindex
  have hlt : H < d.L := by
    apply lt_of_le_of_ne hHL
    intro he
    rw [he,relIndex_self] at hidx
    omega
  have hHS : d.SL ≤ H :=
    (inf_le_inf_right d.L (d.S_le_T.trans hM.1.2)).trans hMH.le
  have hHZ : (center d.L).map d.L.subtype ≤ H :=
    map_mono (center_le_preimage e _)
  have hpH : Group.IsPerfect H := Group.IsPerfect.ofSurjective
    (f := eJ.toMonoidHom) eJ.surjective
  have hfH : generalizedFitting H = pCore 2 H :=
    characteristicTwo_of_mulEquiv eJ.symm hfit
  have hcH : H.pCoreIn 2 = ((m22HexadPointwiseKernel B).comap q).map d.L.subtype := by
    rw [show H = J.map d.L.subtype from rfl,
      ←map_pCoreIn_of_injective 2 J d.L.subtype d.L.subtype_injective,hcore]
    rfl
  have hVC : V ⊓ d.L ≤ H.pCoreIn 2 := by
    rw [hcH]
    rintro v ⟨hv,hvL⟩
    refine ⟨⟨v,hvL⟩,?_,rfl⟩
    apply hWB
    rw [←hV]
    exact mem_map_of_mem q hv
  have hcardH : Nat.card (pCore 2 H) = 16 * Nat.card (center d.L) := by
    rw [←pCore_map_iso 2 eJ,card_map_of_injective eJ.injective]
    exact hcard
  have hmodelH : Nonempty ((H ⧸ pCore 2 H) ≃* alternatingGroup (Fin 6)) := by
    obtain ⟨f⟩ := hmodel
    exact ⟨(eJ.toMonoidHom.pCoreQuotientEquiv eJ.surjective
      (by rw [(MonoidHom.ker_eq_bot_iff _).mpr eJ.injective];
          exact IsPGroup.of_card (n := 0) (by simp))).symm.trans f⟩
  have hnotM : ¬ H ≤ M := fun hh => hMH.not_ge (le_inf hh hHL)
  have hBK : d.localSylowBorel K ≤ H := by
    have hKL := (s.localFamily_linearTwo_selected_carrier (h := h)
      hG hM hJ hu hne hmany hfull hres hK hq hout hb (by omega)).1.le
    exact (le_inf (d.localFamily_linearTwo_borel_le_selected hG hM hJ hu h hK hq hout hb)
      (inf_le_left.trans hKL)).trans hMH.le
  have hnotZ : ¬ H ≤ d.MZ := fun hh =>
    s.localFamily_linearTwo_borel_not_le_MZ (h := h) hG hM hJ hu hfull hK hq hout hb
      (hBK.trans hh)
  let C := M ⊓ d.G1
  let R := (pResidual 2 C).map C.subtype
  let W := ⁅V,R⁆
  have hGL := (s.localFamily_linearTwo_selected_carrier (h := h)
    hG hM hJ hu hne hmany hfull hres hK hq hout hb (by omega)).2.2.2.1
  have hCR : C ≤ normalizer (R : Set G) := C.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image C (pResidual 2 C))
  have hCW : C ≤ normalizer (W : Set G) := by
    intro c hc
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [show W = ⁅V,R⁆ from rfl,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (h.normalized hc.1),
      mem_normalizer_iff_map_conj_eq.mp (hCR hc)]
  have hWne : (W.subgroupOf d.L).map (projection e) ≠ ⊥ := by
    intro he
    change Nat.card ((W.subgroupOf d.L).map (projection e)) = 4 at hW
    rw [he,card_bot] at hW
    omega
  have hCN : C ≤ normalizer (H : Set G) := full_hexad_normalized d.L C W
    (inf_le_right.trans hGL) hCW e hB hWB hWne
  have hSN : d.S ≤ normalizer (H : Set G) :=
    (le_inf (d.S_le_T.trans hM.1.2) d.S_le_G1).trans hCN
  let : Group.IsPerfect H := hpH
  let : IsQuasisimple (alternatingGroup (Fin 6)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := by
      let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
      exact ((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  let : IsQuasisimple (H ⧸ pCore 2 H) := IsQuasisimple.of_mulEquiv hmodelH.some.symm
  have hcoreNe : H.pCoreIn 2 ≠ ⊥ := by
    intro he
    have he' : pCore 2 H = ⊥ := map_injective H.subtype_injective
      (he.trans (map_bot H.subtype).symm)
    rw [he',card_bot] at hcardH
    have hp := Nat.card_pos (α := center d.L)
    omega
  have hlocal : H ∈ Chapter1.LIn d.G1 d.S :=
    Chapter1.mem_LIn_of_normalized_perfect s.centralizer_sylow
      (hHL.trans d.L_component.1) hSN hcoreNe
  have hmoved : ⁅H,elementaryAbelianMaxJ d.S⁆ = H :=
    (d.localFamily_normalizerAction hG hempty hM hJ hu h hlocal inferInstance
      hnotZ hfH).movement.symm
  exact ⟨e,B,hB,hMH,hlt,hHS,hHZ,hpH,hfH,hcH,hVC,hcardH,hmodelH,hidx,hnotM,hnotZ,hCN,hlocal,hmoved⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC Section03 Section03.InitialSource ChapterA.Section05To06 Stellmacher
variable {G : Type*} [Group G] [Finite G]

/-- Apply the full-cover hexad construction to every escaping natural member
of the original marker's local family, preserving its prime and selected row. -/
theorem PreparedChosenModule.source_preExclusion_local_natural_m22_full_hexad
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
          ∃ e : (d.L ⧸ center d.L) ≃* M22, ∃ B ∈ m22Blocks,
            let q := e.toMonoidHom.comp (QuotientGroup.mk' (center d.L))
            let H := ((MulAction.stabilizer M22 B).comap q).map d.L.subtype
            (M ⊓ d.L) < H ∧ H < d.L ∧ d.SL ≤ H ∧
            (center d.L).map d.L.subtype ≤ H ∧
            Group.IsPerfect H ∧ generalizedFitting H = pCore 2 H ∧
            H.pCoreIn 2 = ((m22HexadPointwiseKernel B).comap q).map d.L.subtype ∧
            V ⊓ d.L ≤ H.pCoreIn 2 ∧
            Nat.card (pCore 2 H) = 16 * Nat.card (center d.L) ∧
            Nonempty ((H ⧸ pCore 2 H) ≃* alternatingGroup (Fin 6)) ∧
            H.relIndex d.L = 77 ∧ ¬ H ≤ M ∧ ¬ H ≤ d.MZ ∧
            M ⊓ d.G1 ≤ normalizer (H : Set G) ∧ H ∈ Chapter1.LIn d.G1 d.S ∧
            ⁅H,elementaryAbelianMaxJ d.S⁆ = H := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,?_⟩
  intro K hK hq hout n hb
  obtain ⟨hp3,hn,_,_⟩ := s.localFamily_linearTwo_moving_plane_four (h := h)
    hp hG hM hJ hu hfull hK hq hout hb
  exact ⟨hp3,hn,s.localFamily_linearTwo_m22_full_hexad (h := h) hp
    hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb⟩

end CFSG.Quasithin.Chapter15.Section01
