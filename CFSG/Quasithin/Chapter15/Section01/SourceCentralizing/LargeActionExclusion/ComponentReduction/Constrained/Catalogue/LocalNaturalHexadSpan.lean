module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalNaturalHexadModule

/-!
# The original module generates the hexad radical modulo its covering center

Let H be the full hexad lift for an escaping original natural local member,
and put A = ⟨(V ∩ L)^H⟩. Its image under the same L → L/Z(L) → M₂₂
is the entire elementary hexad kernel. Consequently
A Z(L) = O₂(H), with the full covering center retained.

Every nonidentity kernel element fixes precisely the hexad. Involution fusion
therefore gives a conjugator inside its stabilizer, proving that any nonzero
kernel subgroup spans the full kernel. Apply this to the image of V ∩ L,
which contains the injectively surviving original moving four-group, and
pull back through the literal central quotient.

The original fixed summand centralizes H. Since Q₁ normalizes both H and V,
the exact whole-module span is ⟨V^(HQ₁)⟩ = V A. Both A and V stay in Q₁.
The original-marker consumer preserves G₁, M_Z, S, Q₁, K, L and H.
This identifies the module contribution to the full core; the automorphic
escape exclusion and original 15.1.20(2)/15.1.22 assembly remain open.
Original 15.1.14 and whole-core A₆ reconstruction retain their producers.

Source: Aschbacher--Smith 15.1.16--20 and 15.1.22, pp.1092--1100,
and I.2.2(6), p.412, for the full M₂₂ hexad cover.
-/

public section
open Subgroup Theory.GroupTheory Sporadic.Mathieu Stellmacher
open scoped Pointwise

private theorem hexad_kernel_span {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (W : Subgroup M22) (hW : W ≤ m22HexadPointwiseKernel B) (hne : W ≠ ⊥) :
    conjugateSpanBy W (MulAction.stabilizer M22 B) = m22HexadPointwiseKernel B := by
  let E := m22HexadPointwiseKernel B
  let H := MulAction.stabilizer M22 B
  let := m22HexadPointwiseKernel_elementaryAbelian hB
  have hnorm : H ≤ normalizer (E : Set M22) :=
    (m22HexadPointwiseKernel_normalizer hB).symm.le
  refine le_antisymm (conjugateSpanBy_le hW hnorm) ?_
  obtain ⟨w,hw,hwn⟩ := W.bot_or_exists_ne_one.resolve_left hne
  have hord (x : M22) (hx : x ∈ E) (hxn : x ≠ 1) : orderOf x = 2 := by
    have hd := orderOf_dvd_of_pow_eq_one (elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx)
    exact (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left
      (fun he => hxn (orderOf_eq_one_iff.mp he))
  intro x hx
  by_cases hx1 : x = 1
  · exact hx1 ▸ one_mem _
  obtain ⟨g,hg⟩ := isConj_iff.mp
    (m22_involutions_isConj w x (hord w (hW hw) hwn) (hord x hx hx1))
  have hfix (y : M22) (hy : y ∈ E) (hyn : y ≠ 1) : m22FixedPoints y = B := by
    ext a
    exact (mem_m22FixedPoints y a).trans (M22SolvableSylow.kernel_fixed_iff hB hy hyn a)
  have hgb : g ∈ H := by
    change g • B = B
    rw [←hfix w (hW hw) hwn,←m22FixedPoints_conj]
    change m22FixedPoints (g * w * g⁻¹) = m22FixedPoints w
    rw [hg,hfix x hx hx1,hfix w (hW hw) hwn]
  exact subset_closure ⟨g,hgb,w,hw,hg⟩


private theorem span_subgroupOf {G : Type*} [Group G] (W H L : Subgroup G)
    (hW : W ≤ L) (hH : H ≤ L) :
    (conjugateSpanBy W H).subgroupOf L =
      conjugateSpanBy (W.subgroupOf L) (H.subgroupOf L) := by
  apply map_injective L.subtype_injective
  rw [map_subgroupOf_eq_of_le (conjugateSpanBy_le hW (hH.trans L.le_normalizer)),
    map_conjugateSpanBy,map_subgroupOf_eq_of_le hW,map_subgroupOf_eq_of_le hH]

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC ChapterC.C27Source Section03 Section03.InitialSource ChapterA.Section05To06 Stellmacher
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The original module generates the whole hexad kernel modulo the full
covering center. Its exact span under HQ₁ is V joined to that same lift. -/
theorem PreExclusionSource.localFamily_linearTwo_m22_hexad_span
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
    ∃ e : (d.L ⧸ center d.L) ≃* M22, ∃ B ∈ m22Blocks,
      let q := e.toMonoidHom.comp (QuotientGroup.mk' (center d.L))
      let H := ((MulAction.stabilizer M22 B).comap q).map d.L.subtype
      let A := conjugateSpanBy (V ⊓ d.L) H
      d.ML ≤ H ∧ d.MZ ≤ normalizer (H : Set G) ∧ K ⊔ H = d.L ∧
      A ≤ H.pCoreIn 2 ∧ H.pCoreIn 2 ≤ d.Q1 ∧
      (A.subgroupOf d.L).map q = m22HexadPointwiseKernel B ∧
      A ⊔ (center d.L).map d.L.subtype = H.pCoreIn 2 ∧
      conjugateSpanBy V (H ⊔ d.Q1) = V ⊔ A := by
  obtain ⟨e,B,hB,hMH,hHL,hSH,hZH,hperfect,hfit,hcore,hV,hcard,hmodel,hindex,
      hnotM,hnotZ,hCN,hlocal,hmoved,hmax,hKH,hgen,hMLH,hMZN,hHQ,hVQ⟩ :=
    s.localFamily_linearTwo_m22_hexad_invariant (h := h) hp
      hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center d.L))
  let H := ((MulAction.stabilizer M22 B).comap q).map d.L.subtype
  let A := conjugateSpanBy (V ⊓ d.L) H
  let W := ⁅V,(pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype⁆
  let F := V ⊓ centralizer
    ((pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype : Set G)
  have hAQ : A ≤ H.pCoreIn 2 := conjugateSpanBy_le hV
    (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  have hAL : A ≤ d.L := hAQ.trans ((pCoreIn_le 2 H).trans hHL.le)
  have hVQall := (s.localFamily_linearTwo_m22_module_radical (h := h) hp
    hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb).1
  obtain ⟨hsplit,_,_,_⟩ := s.localFamily_linearTwo_full_action (h := h)
    hG hM hJ hu hfull hK hq hout hb (by omega)
  have hWV : W ≤ V := le_sup_left.trans hsplit.symm.le
  have hKL := (s.localFamily_linearTwo_selected_carrier (h := h)
    hG hM hJ hu hne hmany hfull hres hK hq hout hb (by omega)).1.le
  have hWL : W ≤ d.L :=
    (s.localFamily_linearTwo_moving_plane_bound (h := h)
      hG hM hJ hu hfull hK hq hout hb (by omega)).1.trans ((map_subtype_le _).trans hKL)
  have hWseed : W ≤ V ⊓ d.L := le_inf hWV hWL
  have hseedImage : (V.subgroupOf d.L).map q ≤ m22HexadPointwiseKernel B := by
    intro x hx
    obtain ⟨v,hv,rfl⟩ := hx
    obtain ⟨w,hw,he⟩ := hcore ▸ hV (show v.val ∈ V ⊓ d.L from ⟨hv,v.property⟩)
    exact (Subtype.ext he : w = v) ▸ hw
  have hWcard : Nat.card ((W.subgroupOf d.L).map q) = 4 := by
    rw [show q = e.toMonoidHom.comp (QuotientGroup.mk' (center d.L)) from rfl,
      ←map_map,card_map_of_injective e.injective]
    exact (s.localFamily_linearTwo_mathieu_image (h := h) hp
      hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb).2.2.2.2.2.2.2.2.2
  have hseedNe : (V.subgroupOf d.L).map q ≠ ⊥ := by
    intro he
    have hh : (W.subgroupOf d.L).map q = ⊥ := bot_unique
      ((map_mono (comap_mono hWV)).trans he.le)
    rw [hh,card_bot] at hWcard
    omega
  have hAimage : (A.subgroupOf d.L).map q = m22HexadPointwiseKernel B := by
    rw [show A = conjugateSpanBy (V ⊓ d.L) H from rfl,
      span_subgroupOf _ _ _ inf_le_right hHL.le,map_conjugateSpanBy,
      inf_subgroupOf_right,show H.subgroupOf d.L = (MulAction.stabilizer M22 B).comap q from
        comap_map_eq_self_of_injective d.L.subtype_injective _,
      map_comap_eq_self_of_surjective
        (e.surjective.comp (QuotientGroup.mk'_surjective _))]
    exact hexad_kernel_span hB _ hseedImage hseedNe
  have hAcore : A ⊔ (center d.L).map d.L.subtype = H.pCoreIn 2 := by
    have hh := congrArg (fun C : Subgroup M22 => C.comap q) hAimage
    rw [comap_map_eq,MonoidHom.ker_comp_of_injective _ _ e.injective,
      QuotientGroup.ker_mk'] at hh
    have hm := congrArg (map d.L.subtype) hh
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hAL] at hm
    exact hm.trans hcore.symm
  have hQS := d.catalogue_radical_le_sylow s.centralizer_sylow hu
  have hQV : d.Q1 ≤ normalizer (V : Set G) :=
    (hQS.trans (d.S_le_T.trans hM.1.2)).trans h.normalized
  have hFC : F ≤ centralizer (H : Set G) :=
    ((s.localFamily_linearTwo_fixed_carrier (h := h) hp
      hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb).le.trans inf_le_right).trans
        (centralizer_le hHL.le)
  have hFA : conjugateSpanBy V H = F ⊔ A := by
    apply le_antisymm
    · apply conjugateSpanBy_le
        (hsplit.le.trans (sup_le ((hWseed.trans (le_conjugateSpanBy _ _)).trans le_sup_right)
          le_sup_left))
      exact (le_inf ((le_centralizer_iff.mp hFC).trans (Subgroup.centralizer_le_normalizer _))
        (le_normalizer_conjugateSpanBy _ _)).trans
          (normalizer_inf_normalizer_le_normalizer_sup F A)
    · exact sup_le (inf_le_left.trans (le_conjugateSpanBy _ _))
        (conjugateSpanBy_mono inf_le_left le_rfl)
  have hspan : conjugateSpanBy V (H ⊔ d.Q1) = V ⊔ A := by
    rw [conjugateSpanBy_sup_of_normalizes_seed V H d.Q1 hQV (d.Q1_le_MZ.trans hMZN)]
    apply le_antisymm
    · exact hFA.le.trans (sup_le (inf_le_left.trans le_sup_left) le_sup_right)
    · exact sup_le (le_conjugateSpanBy _ _) (conjugateSpanBy_mono inf_le_left le_rfl)
  exact ⟨hVQall,e,B,hB,hMLH,hMZN,hgen,hAQ,hHQ,hAimage,hAcore,hspan⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterC.C27Source Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The original marker supplies the exact hexad span and central supplement,
with the original prime, radical and full covering projection. -/
theorem PreparedChosenModule.source_preExclusion_local_natural_m22_hexad_span
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
              let A := conjugateSpanBy (V ⊓ d.L) H
              d.ML ≤ H ∧ d.MZ ≤ normalizer (H : Set G) ∧ K ⊔ H = d.L ∧
              A ≤ H.pCoreIn 2 ∧ H.pCoreIn 2 ≤ d.Q1 ∧
              (A.subgroupOf d.L).map q = Sporadic.Mathieu.m22HexadPointwiseKernel B ∧
              A ⊔ (center d.L).map d.L.subtype = H.pCoreIn 2 ∧
              conjugateSpanBy V (H ⊔ d.Q1) = V ⊔ A := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,?_⟩
  intro K hK hq hout n hb
  obtain ⟨hp3,hn,_,_⟩ := s.localFamily_linearTwo_moving_plane_four (h := h)
    hp hG hM hJ hu hfull hK hq hout hb
  exact ⟨hp3,hn,s.localFamily_linearTwo_m22_hexad_span (h := h) hp
    hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb⟩

end CFSG.Quasithin.Chapter15.Section01
