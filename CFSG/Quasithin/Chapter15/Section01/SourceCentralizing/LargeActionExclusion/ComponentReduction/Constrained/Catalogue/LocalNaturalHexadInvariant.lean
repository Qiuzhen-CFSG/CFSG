module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalNaturalHexadGeneration

/-!
# Full marked-normalizer invariance of the covered hexad

For the remaining original natural escape, the full hexad lift H contains
M_Z intersect L and is normalized by the whole original M_Z. The proof keeps
the literal quotient L → L/Z(L) → M₂₂. Properness of the original Sylow-center
centralizer supplies a nonidentity image of a central Sylow element. It lies
in the self-centralizing hexad kernel and fixes exactly the same hexad.
Thus the marked intersection lies in H. Its image contains the native hexad
kernel, so the full design-normalizer theorem and automorphism coverage force
M_Z to preserve H through the central quotient.

The normal two-core of H then lies in Q₁: it lies in a Sylow of H M_Z and is
normalized by M_Z. Consequently V intersect L also lies in the original Q₁.
The full-cover shape, local-family membership, maximality and generation
with K are retained in the same witness and original-marker application.

The remaining ambient M₂₂ exclusion, general natural Borel containment and
15.1.20(2)/15.1.22 assembly stay open. Original 15.1.14 and the independent
whole-core A₆ reconstruction retain their existing producers.

Source: Aschbacher--Smith 15.1.18--20 and 15.1.22, printed pp.1092--1100;
I.2.2(6), p.412, for the full hexad cover. The native fixed-hexad and
full-design normalizer calculations are imported with their original markings.
-/

public section
open Subgroup Theory.GroupTheory Sporadic.Mathieu
open Sporadic.Mathieu.M22CentralCover
open scoped Pointwise

private theorem hexad_invariant_of_sylow_overgroup
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (W : Subgroup M22) (hW : W ≤ MulAction.stabilizer M22 B)
    (hkernel : m22HexadPointwiseKernel B ≤ W)
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
  have hgb := M22SolvableSylow.normalizer_le_hexad_stabilizer hB W hW hkernel hgn
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

private theorem full_hexad_normalized_of_sylow_overgroup
    {A : Type*} [Group A] [Finite A] (L C W : Subgroup A)
    (hCL : C ≤ normalizer (L : Set A)) (hCW : C ≤ normalizer (W : Set A))
    (e : (L ⧸ center L) ≃* M22)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (hWB : (W.subgroupOf L).map (projection e) ≤ MulAction.stabilizer M22 B)
    (hkernel : m22HexadPointwiseKernel B ≤ (W.subgroupOf L).map (projection e)) :
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
  have hBfix := hexad_invariant_of_sylow_overgroup hB _ hWB hkernel b hb
  have him : b (projection e l) ∈ MulAction.stabilizer M22 B :=
    hBfix ▸ mem_map_of_mem b.toMonoidHom hl
  refine ⟨a l,?_,rfl⟩
  change projection e (a l) ∈ MulAction.stabilizer M22 B
  exact (MulAut.centralQuotientAction_apply e a l) ▸ him


private theorem cover_centralizer_le_hexad
    {A : Type*} [Group A] [Finite A]
    (e : (A ⧸ center A) ≃* M22) (P : Sylow 2 A)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (hPB : ((P.mapSurjective (projection_surjective e) : Sylow 2 M22) : Subgroup M22) ≤
      MulAction.stabilizer M22 B)
    (hproper : centralizer ((center P).map (P : Subgroup A).subtype : Set A) ≠ ⊤) :
    centralizer ((center P).map (P : Subgroup A).subtype : Set A) ≤
      preimage e (MulAction.stabilizer M22 B) := by
  let q := projection e
  let Z := (center P).map (P : Subgroup A).subtype
  let Pbar := P.mapSurjective (projection_surjective e)
  have hz : ∃ z ∈ Z, q z ≠ 1 := by
    by_contra! hz
    apply hproper
    apply top_unique
    intro x _ z hzZ
    have hzq : QuotientGroup.mk' (center A) z = 1 :=
      e.injective ((hz z hzZ).trans e.map_one.symm)
    exact (mem_center_iff.mp ((QuotientGroup.eq_one_iff z).mp hzq) x).symm
  obtain ⟨z,hzZ,hzne⟩ := hz
  have hzP : q z ∈ centralizer (Pbar : Set M22) := by
    obtain ⟨w,hw,rfl⟩ := hzZ
    rintro _ ⟨x,hx,rfl⟩
    change q x * q w.val = q w.val * q x
    rw [←map_mul,←map_mul]
    exact congrArg q (congrArg Subtype.val (mem_center_iff.mp hw (⟨x,hx⟩ : P)))
  have hzB : q z ∈ m22HexadPointwiseKernel B :=
    m22HexadPointwiseKernel_selfCentralizing hB
      ((centralizer_le (M22SolvableSylow.kernel_le_of_sylow hB Pbar hPB)) hzP)
  have heB : m22FixedPoints (q z) = B := by
    ext a
    exact (mem_m22FixedPoints _ _).trans (M22SolvableSylow.kernel_fixed_iff hB hzB hzne a)
  intro x hx
  have hc : q x ∈ centralizer ({q z} : Set M22) := by
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul] using congrArg q (hx z hzZ).symm
  change q x ∈ MulAction.stabilizer M22 B
  rw [←heB]
  exact m22_centralizer_le_fixedPoints_stabilizer _ hc

private theorem normalized_core_le_sylow_overgroup_core
    {A : Type*} [Group A] [Finite A] (P : Sylow 2 A) (N K : Subgroup A)
    (hPN : (P : Subgroup A) ≤ N) (hn : N ≤ normalizer (K : Set A)) :
    K.pCoreIn 2 ≤ N.pCoreIn 2 := by
  let Q := K.pCoreIn 2
  have hnQ : N ≤ normalizer (Q : Set A) := hn.trans
    (normalizer_le_normalizer_characteristic_image K (pCore 2 K))
  have hQN : Q ≤ N := by
    let D := K ⊔ N
    have hQD : Q ≤ D := (pCoreIn_le 2 K).trans le_sup_left
    have hDQ : D ≤ normalizer (Q : Set A) := sup_le
      (K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K))) hnQ
    have hPD : (P : Subgroup A) ≤ D := hPN.trans le_sup_right
    have hc := le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 K) hQD hDQ
    have hs := pCoreIn_le_sylow D (P.subtype hPD)
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hPD] at hs
    exact (hc.trans hs).trans hPN
  exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 K) hQN hnQ

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC Section03 Section03.InitialSource ChapterA.Section05To06 Stellmacher
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The original full hexad contains the marked intersection and is invariant
under all of M_Z. Its whole two-core and V intersect L lie in the original Q₁. -/
theorem PreExclusionSource.localFamily_linearTwo_m22_hexad_invariant
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
      ⁅H,elementaryAbelianMaxJ d.S⁆ = H ∧
      IsCoatom (H.subgroupOf d.L) ∧ ¬ K ≤ H ∧ K ⊔ H = d.L ∧
      d.ML ≤ H ∧ d.MZ ≤ normalizer (H : Set G) ∧
      H.pCoreIn 2 ≤ d.Q1 ∧ V ⊓ d.L ≤ d.Q1 := by
  obtain ⟨e,B,hB,hMH,hHL,hSH,hZH,hperfect,hfit,hcore,hV,hcard,hmodel,hindex,
      hnotM,hnotZ,hCN,hlocal,hmoved,hmax,hKH,hgen⟩ :=
    s.localFamily_linearTwo_m22_hexad_generation (h := h) hp
      hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb
  let q := projection e
  let J := preimage e (MulAction.stabilizer M22 B)
  let H := J.map d.L.subtype
  have hJH : H.subgroupOf d.L = J :=
    comap_map_eq_self_of_injective d.L.subtype_injective J
  have hL : IsComponent d.G1 (d.L.subgroupOf d.G1) := by
    rcases d.ordinary_or_constrained s.odd_core with hc | hf
    · exact hc
    · exact (hout (s.localFamily_linearTwo_le_MZ_of_constrained_carrier (h := h)
        hp hG hempty hM hJ hu hne hmany hfull hres hK hq hb hf)).elim
  let ec := (QuotientGroup.quotientMulEquivOfEq (s.ordinary hL).center_eq.symm).trans e
  have hc := s.surviving_sporadic_centralizer_eq (h := h) hG hempty hM hu hL
    (name := .m22) (Or.inr (Or.inl rfl)) ec
  obtain ⟨P,hP⟩ := s.component_sylow
  let Pbar := P.mapSurjective (projection_surjective e)
  have hPB : (Pbar : Subgroup M22) ≤ MulAction.stabilizer M22 B := by
    rintro _ ⟨x,hx,rfl⟩
    have hxH := hSH (hP ▸ mem_map_of_mem d.L.subtype hx)
    have hxJ : x ∈ J := by
      rw [←hJH]
      exact hxH
    exact hxJ
  let Z := (center P).map (P : Subgroup d.L).subtype
  have hZ : Z.map d.L.subtype = (center d.SL).map d.SL.subtype := by
    change ((center P).map (P : Subgroup d.L).subtype).map d.L.subtype = _
    rw [map_map,←map_center_image_of_injective (P : Subgroup d.L)
      d.L.subtype d.L.subtype_injective,hP]
  have hC : d.ML.subgroupOf d.L = centralizer (Z : Set d.L) := by
    rw [hc]
    ext x
    constructor
    · intro hx v hv
      exact Subtype.ext (hx.2 v (hZ ▸ mem_map_of_mem d.L.subtype hv))
    · intro hx
      refine ⟨x.property,?_⟩
      intro v hv
      obtain ⟨w,hw,rfl⟩ := hZ.symm ▸ hv
      exact congrArg Subtype.val (hx w hw)
  have hproper : centralizer (Z : Set d.L) ≠ ⊤ := by
    rw [←hC]
    exact fun he => d.L_not_le_MZ ((subgroupOf_eq_top.mp he).trans inf_le_left)
  have hMLJ : d.ML.subgroupOf d.L ≤ J :=
    hC ▸ cover_centralizer_le_hexad e P hB hPB hproper
  have hMLH : d.ML ≤ H := by
    intro x hx
    exact ⟨⟨x,hx.2⟩,hMLJ hx,rfl⟩
  have hGL := (s.localFamily_linearTwo_selected_carrier (h := h)
    hG hM hJ hu hne hmany hfull hres hK hq hout hb (by omega)).2.2.2.1
  have hMZN : d.MZ ≤ normalizer (H : Set G) := by
    apply full_hexad_normalized_of_sylow_overgroup d.L d.MZ d.ML
      (inf_le_left.trans hGL)
      ((le_inf d.MZ.le_normalizer (inf_le_left.trans hGL)).trans
        inf_normalizer_le_normalizer_inf) e hB
    · exact map_le_iff_le_comap.mpr hMLJ
    · apply (M22SolvableSylow.kernel_le_of_sylow hB Pbar hPB).trans
      rintro _ ⟨x,hx,rfl⟩
      refine mem_map_of_mem q ?_
      have hxS : x.val ∈ d.SL := hP ▸ mem_map_of_mem d.L.subtype hx
      have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
        hu ▸ Set.mem_singleton Mc
      refine ⟨⟨d.S_le_G1 hxS.1,hMc.2 ?_⟩,x.property⟩
      intro z hz
      exact (centralInvolutions_le_centralizer_sylow T hz x
        (d.S_le_T hxS.1)).symm
  have hHQ : H.pCoreIn 2 ≤ d.Q1 := by
    obtain ⟨P1,hP1⟩ := s.centralizer_sylow
    let H0 := H.subgroupOf d.G1
    let N := d.MZ.subgroupOf d.G1
    have hSM : (P1 : Subgroup d.G1) ≤ N := by
      intro x hx
      have hxS : x.val ∈ d.S := hP1 ▸ mem_map_of_mem d.G1.subtype hx
      have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
        hu ▸ Set.mem_singleton Mc
      exact ⟨x.property,hMc.2 (fun z hz =>
        (centralInvolutions_le_centralizer_sylow T hz x (d.S_le_T hxS)).symm)⟩
    have hn : N ≤ normalizer (H0 : Set d.G1) := by
      apply le_normalizer_iff.mpr
      intro x hx y hy
      exact le_normalizer_iff.mp hMZN x hx y hy
    have hi := map_mono (f := d.G1.subtype)
      (normalized_core_le_sylow_overgroup_core P1 N H0 hSM hn)
    rw [map_pCoreIn_of_injective 2 H0 _ d.G1.subtype_injective,
      map_pCoreIn_of_injective 2 N _ d.G1.subtype_injective] at hi
    dsimp only [H0,N] at hi
    rw [map_subgroupOf_eq_of_le (show H ≤ d.G1 from hHL.le.trans d.L_component.1),
      map_subgroupOf_eq_of_le (show d.MZ ≤ d.G1 from inf_le_left)] at hi
    exact hi
  exact ⟨e,B,hB,hMH,hHL,hSH,hZH,hperfect,hfit,hcore,hV,hcard,hmodel,hindex,
    hnotM,hnotZ,hCN,hlocal,hmoved,hmax,hKH,hgen,hMLH,hMZN,hHQ,hV.trans hHQ⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC Section03 Section03.InitialSource ChapterA.Section05To06 Stellmacher
variable {G : Type*} [Group G] [Finite G]

/-- Apply whole-M_Z invariance and Q₁ containment to the original marker,
retaining its component, prime, row and full central cover. -/
theorem PreparedChosenModule.source_preExclusion_local_natural_m22_hexad_invariant
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
            ⁅H,elementaryAbelianMaxJ d.S⁆ = H ∧
            IsCoatom (H.subgroupOf d.L) ∧ ¬ K ≤ H ∧ K ⊔ H = d.L ∧
            d.ML ≤ H ∧ d.MZ ≤ normalizer (H : Set G) ∧
            H.pCoreIn 2 ≤ d.Q1 ∧ V ⊓ d.L ≤ d.Q1 := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,?_⟩
  intro K hK hq hout n hb
  obtain ⟨hp3,hn,_,_⟩ := s.localFamily_linearTwo_moving_plane_four (h := h)
    hp hG hM hJ hu hfull hK hq hout hb
  exact ⟨hp3,hn,s.localFamily_linearTwo_m22_hexad_invariant (h := h) hp
    hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb⟩

end CFSG.Quasithin.Chapter15.Section01
