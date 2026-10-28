module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalNaturalHexadElementary
public import Theory.Mathieu.M22.UniversalMultiplier.TwoPrimary.HexadLifting

/-!
# The original span is the full covered-hexad core

Let H be the full hexad lift of an original natural escape and let
A = ⟨(V ∩ L)^H⟩. The native A₆ complement lifts through the original
central two-cover of M₂₂. The existing equality A Z(L) = O₂(H) therefore
makes A together with that lifted complement a central supplement in H.
Perfectness removes the central supplement; the complement meets the full
two-core trivially, so A = O₂(H).

Consequently the original full span is exactly V O₂(H), and this whole
subgroup is elementary abelian. The center has not been discarded: the
proof shows that the original span contains it. The original-marker
application retains G₁, M_Z, S, Q₁, K and the literal central quotient.

The automorphic displacement exclusion, general natural Borel containment
and original 15.1.20(2)/15.1.22 assembly remain open. Original 15.1.14 and
whole-core A₆ reconstruction retain their existing producers.

Source: Aschbacher--Smith I.2.2(6), printed p.412, and 15.1.16--20 and
15.1.22, printed pp.1092--1100. The native A₆ lift uses the proved
central-cover splitting through the specified hexad section.
-/

public section
open Subgroup
open scoped Pointwise IsMulCommutative

private theorem perfect_split_central_kernel
    {G : Type*} [Group G] [Group.IsPerfect G]
    (A Z N P : Subgroup G) [A.Normal]
    (hAZ : A ⊔ Z = N) (hZ : Z ≤ center G)
    (hNP : N ⊔ P = ⊤) (hd : Disjoint N P) : A = N := by
  let F := A ⊔ P
  have hFC : F ⊔ center G = ⊤ := by
    apply top_unique
    rw [←hNP,←hAZ]
    exact sup_le (sup_le (le_sup_left.trans le_sup_left)
      (hZ.trans le_sup_right)) (le_sup_right.trans le_sup_left)
  let : F.Normal := normalizer_eq_top_iff.mp (top_unique (hFC ▸
    sup_le F.le_normalizer (Subgroup.center_le_normalizer (F : Set G))))
  have hF : F = ⊤ := by
    apply top_unique
    rw [←Group.IsPerfect.commutator_eq_top (G := G)]
    exact Normal.commutator_le_of_self_sup_commutative_eq_top hFC inferInstance
  apply le_antisymm (hAZ ▸ le_sup_left)
  intro x hx
  obtain ⟨a,ha,b,hb,hab⟩ := mem_sup_of_normal_left.mp (hF ▸ mem_top x : x ∈ F)
  have hbN : b ∈ N := by
    have hh := N.mul_mem (N.inv_mem ((hAZ ▸ le_sup_left) ha)) hx
    rwa [←hab,inv_mul_cancel_left] at hh
  have hb1 : b = 1 := (disjoint_def.mp hd) hbN hb
  rwa [←hab,hb1,mul_one]

open Sporadic.Mathieu Sporadic.Mathieu.M22CentralCover

private theorem full_hexad_kernel_eq_of_normal_image
    {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]
    (e : (L ⧸ center L) ≃* M22) (hZ : IsPGroup 2 (center L))
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (W : Subgroup (preimage e (MulAction.stabilizer M22 B))) [W.Normal]
    (hW : W.map (localProjection e (MulAction.stabilizer M22 B)) = (m22SetAction B).ker) :
    W = ((m22SetAction B).ker).comap (localProjection e (MulAction.stabilizer M22 B)) := by
  let J := preimage e (MulAction.stabilizer M22 B)
  let D := MulAction.stabilizer M22 B
  let f := localProjection e D
  let N := ((m22SetAction B).ker).comap f
  let : Group.IsPerfect J := hexadPreimage_isPerfect e hZ hB
  obtain ⟨s,hs⟩ := M22UniversalMultiplier.exists_hexadSection_lift
    (projection e) (projection_surjective e) (by rw [projection_ker])
    (by rw [projection_ker]; exact hZ) hB
  have hsJ (a : alternatingGroup (Fin 6)) : s a ∈ J := by
    change projection e (s a) ∈ D
    rw [show projection e (s a) = (m22HexadSection hB a).val from DFunLike.congr_fun hs a]
    exact (m22HexadSection hB a).property
  let r : alternatingGroup (Fin 6) →* J := s.codRestrict J hsJ
  have hfr : f.comp r = m22HexadSection hB := by
    apply MonoidHom.ext
    intro a
    apply Subtype.ext
    exact DFunLike.congr_fun hs a
  have hNP : N ⊔ r.range = ⊤ := by
    have hm : (N ⊔ r.range).map f = (⊤ : Subgroup J).map f := by
      rw [Subgroup.map_sup,map_comap_eq_self_of_surjective (localProjection_surjective e D),
        ←MonoidHom.range_comp,hfr,(m22HexadSection_isComplement hB).sup_eq_top,
        ←MonoidHom.range_eq_map,MonoidHom.range_eq_top.mpr (localProjection_surjective e D)]
    have hh := map_eq_map_iff.mp hm
    rw [sup_eq_left.mpr ((f.ker_le_comap _).trans le_sup_left),top_sup_eq] at hh
    exact hh
  have hd : Disjoint N r.range := by
    apply disjoint_def.mpr
    intro x hx hxP
    obtain ⟨a,rfl⟩ := hxP
    have ha : m22HexadSection hB a = 1 := by
      exact (disjoint_def.mp (m22HexadSection_isComplement hB).disjoint)
        ((DFunLike.congr_fun hfr a) ▸ hx) ⟨a,rfl⟩
    have ha1 : a = 1 := (m22HexadSection_injective hB) (ha.trans (map_one _).symm)
    exact ha1 ▸ r.map_one
  have hcentral : f.ker ≤ center J := by
    rw [localProjection_ker]
    intro z hz
    exact mem_center_iff.mpr (fun x => Subtype.ext (mem_center_iff.mp hz x))
  apply perfect_split_central_kernel W f.ker N r.range _ hcentral hNP hd
  rw [←comap_map_eq,hW]

open Representation Representation.BinaryOffender Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterD.UniqueFactor ChapterC ChapterC.C27Source Section03 Section03.InitialSource ChapterA.Section05To06 Stellmacher
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The actual original moving span equals the entire covered core, including
its central kernel. Its join with the original module is elementary. -/
theorem PreExclusionSource.localFamily_linearTwo_m22_hexad_full_core
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
      A = H.pCoreIn 2 ∧ H.pCoreIn 2 ≤ d.Q1 ∧
      IsElementaryAbelian 2 (V ⊔ H.pCoreIn 2 : Subgroup G) ∧
      conjugateSpanBy V (H ⊔ d.Q1) = V ⊔ H.pCoreIn 2 ∧
      V ≤ centralizer (H.pCoreIn 2 : Set G) := by
  obtain ⟨hVQ,e,B,hB,hMLH,hMZN,hgen,hAQ,hHQ,hAimage,hAcore,hspan,hE,hcore,hVcore⟩ :=
    s.localFamily_linearTwo_m22_hexad_elementary (h := h) hp
      hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb
  let q := projection e
  let D := MulAction.stabilizer M22 B
  let J := preimage e D
  let H := J.map d.L.subtype
  let A := conjugateSpanBy (V ⊓ d.L) H
  let A0 := A.subgroupOf d.L
  let W := A0.subgroupOf J
  let f := localProjection e D
  have hL : IsComponent d.G1 (d.L.subgroupOf d.G1) := by
    rcases d.ordinary_or_constrained s.odd_core with hc | hf
    · exact hc
    · exact (hout (s.localFamily_linearTwo_le_MZ_of_constrained_carrier (h := h)
        hp hG hempty hM hJ hu hne hmany hfull hres hK hq hb hf)).elim
  let : IsQuasisimple d.L := IsQuasisimple.of_mulEquiv (hG := hL.2)
    (subgroupOfEquivOfLe d.L_component.1)
  have hZ := (s.ordinary hL).center_two
  have hHJ : H.subgroupOf d.L = J := comap_map_eq_self_of_injective d.L.subtype_injective J
  have hAJ : A0 ≤ J := hHJ ▸ comap_mono (hAQ.trans (pCoreIn_le 2 H))
  have hn : J ≤ normalizer (A0 : Set d.L) := by
    apply le_normalizer_iff.mpr
    intro j hj x hx
    exact le_normalizer_iff.mp (le_normalizer_conjugateSpanBy (V ⊓ d.L) H)
      j.val (mem_map_of_mem d.L.subtype hj) x.val hx
  let : W.Normal := normal_subgroupOf_of_le_normalizer hn
  have hW : W.map f = (m22SetAction B).ker := by
    apply map_injective D.subtype_injective
    rw [map_map,show D.subtype.comp f = q.comp J.subtype from rfl,
      ←map_map,map_subgroupOf_eq_of_le hAJ]
    exact hAimage
  have hWeq := full_hexad_kernel_eq_of_normal_image e hZ hB W hW
  have hZA : (center d.L).map d.L.subtype ≤ A := by
    rintro _ ⟨z,hz,rfl⟩
    let zj : J := ⟨z,center_le_preimage e D hz⟩
    have hzker : zj ∈ f.ker := by
      rw [localProjection_ker]
      exact hz
    have hzW : zj ∈ W := hWeq.ge ((f.ker_le_comap _) hzker)
    exact hzW
  have hAeq : A = H.pCoreIn 2 := (sup_eq_left.mpr hZA).symm.trans hAcore
  refine ⟨hVQ,e,B,hB,hMLH,hMZN,hgen,hAeq,hHQ,?_,?_,hVcore⟩
  · change IsElementaryAbelian 2 (V ⊔ H.pCoreIn 2 : Subgroup G)
    rw [←hAeq]
    exact hE
  · change conjugateSpanBy V (H ⊔ d.Q1) = V ⊔ H.pCoreIn 2
    rw [←hAeq]
    exact hspan

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterC.C27Source Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The original marker generates the full covered hexad core. The full
HQ₁-span is the elementary join of V with that same complete two-core. -/
theorem PreparedChosenModule.source_preExclusion_local_natural_m22_hexad_full_core
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
              A = H.pCoreIn 2 ∧ H.pCoreIn 2 ≤ d.Q1 ∧
              IsElementaryAbelian 2 (V ⊔ H.pCoreIn 2 : Subgroup G) ∧
              conjugateSpanBy V (H ⊔ d.Q1) = V ⊔ H.pCoreIn 2 ∧
              V ≤ centralizer (H.pCoreIn 2 : Set G) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,?_⟩
  intro K hK hq hout n hb
  obtain ⟨hp3,hn,_,_⟩ := s.localFamily_linearTwo_moving_plane_four (h := h)
    hp hG hM hJ hu hfull hK hq hout hb
  exact ⟨hp3,hn,s.localFamily_linearTwo_m22_hexad_full_core (h := h) hp
    hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb⟩

end CFSG.Quasithin.Chapter15.Section01
