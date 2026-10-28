module
public import Theory.GroupTheory.ReducedNormal.SylowMovedEight
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.FullSeed

/-!
# The original centralizer orbit has binary rank three

For H=C_G(z), the reduced module V_H=⟨Ω₁Z(T)^H⟩ has a moved plane
[V_H,I], and the full-seed calculation gives C_{Ω₁Z(T)}(I)=⟨z⟩.
Sylow averaging and normality give V_H=[V_H,I]⟨z⟩. If z belonged to
the plane, V_H would be a reduced four-group with a nonidentity central
fixed vector. Its automorphism image would be a two-group, contradicting
nontrivial movement. Hence z lies outside the plane and |V_H|=8.

Every transport uses the literal inclusion H→G, the original Sylow T,
and I=⟨J(R₁)^H⟩. The endpoint derives the plane and fixed-line premises
from the original-R₁ source product. This supplies the rank-three step in
13.4.9 without assuming H₀'s amalgam classification. The chief-factor
condition, H₀ quotient, C₃ geometry and ambient fusion remain with
qt-d-1341-solvable-source; earlier-source discharge stays with
qt-d-1341-fixed-core-source.
Source: Aschbacher–Smith13.4.9, printed p.906.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The literal omega orbit in C_G(z) is a rank-three elementary group. -/
theorem centralizer_omega_eight_of_thompson_fixed
    (h₀ : Hypothesis1331 T L) {z : G}
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (R : Subgroup G) (hRT : R ≤ T)
    (hrank : Representation.BinaryOffender.rank
      (⁅centralizerOmegaOrbit T z,
        conjugateSpanBy (elementaryAbelianMaxJ R) (centralizer ({z} : Set G))⁆ : Subgroup G) = 2)
    (hfixed : omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (conjugateSpanBy (elementaryAbelianMaxJ R)
        (centralizer ({z} : Set G)) : Set G) = zpowers z) :
    let U := centralizerOmegaOrbit T z
    let I := conjugateSpanBy (elementaryAbelianMaxJ R) (centralizer ({z} : Set G))
    U = (⁅U,I⁆ : Subgroup G) ⊔ zpowers z ∧ z ∉ (⁅U,I⁆ : Subgroup G) ∧
      Nat.card U = 8 ∧ Representation.BinaryOffender.rank U = 3 := by
  let H := centralizer ({z} : Set G)
  let U := (centralizerOmegaOrbit T z).subgroupOf H
  let S := T.subtype (original_sylow_le_centralizer hz)
  let A := (elementaryAbelianMaxJ R).subgroupOf H
  let N := conjugateSpanBy A ⊤
  have hU := centralizerOmegaOrbit_reduced h₀ hz hz1
  let := hU.normal
  let := hU.elementary
  have hTH : (T : Subgroup G) ≤ H := original_sylow_le_centralizer hz
  have hRH : R ≤ H := hRT.trans hTH
  have hAH : elementaryAbelianMaxJ R ≤ H :=
    (sSup_le fun _ hA => hA.1).trans hRH
  have hUS : U ≤ S := hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal S)
  have hSmap : (S : Subgroup H).map H.subtype = (T : Subgroup G) := by
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]
  have hZmap : (omegaOneCenterAmbient (S : Subgroup H)).map H.subtype =
      omegaOneCenterAmbient (T : Subgroup G) := by
    rw [← omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective,hSmap]
  have hNmap : N.map H.subtype =
      conjugateSpanBy (elementaryAbelianMaxJ R) H := by
    rw [map_conjugateSpanBy,map_subgroupOf_eq_of_le hAH,
      ← MonoidHom.range_eq_map,range_subtype]
  have hWmap : (⁅U,N⁆ : Subgroup H).map H.subtype =
      ⁅centralizerOmegaOrbit T z,conjugateSpanBy (elementaryAbelianMaxJ R) H⁆ := by
    rw [map_commutator,map_subgroupOf_eq_of_le (centralizerOmegaOrbit_le hz),hNmap]
  let W := ⁅U,N⁆
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_injective
    (inclusion (commutator_le_left U N)) (inclusion_injective _)
  have hcard : Nat.card W = 4 := by
    have hr : Nat.log 2 (Nat.card W) = 2 := by
      change Nat.log 2 _ = 2 at hrank
      rw [← hWmap,card_map_of_injective H.subtype_injective] at hrank
      exact hrank
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 W).exists_card_eq
    rw [hn,Nat.log_pow Nat.one_lt_two] at hr
    rw [hn,hr]
    rfl
  have hspan : U = conjugateSpanBy (omegaOneCenterAmbient (S : Subgroup H)) ⊤ := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le (centralizerOmegaOrbit_le hz),map_conjugateSpanBy,
      hZmap,← MonoidHom.range_eq_map,range_subtype]
    rfl
  let zh : H := ⟨z,mem_centralizer_singleton_iff.mpr rfl⟩
  have hzS : zh ∈ omegaOneCenterAmbient (S : Subgroup H) := by
    have hzmap : z ∈ (omegaOneCenterAmbient (S : Subgroup H)).map H.subtype := hZmap.symm ▸ hz
    obtain ⟨a,ha,he⟩ := hzmap
    exact (show a = zh from Subtype.ext he) ▸ ha
  have hzc : zh ∈ center H := by
    apply mem_center_iff.mpr
    intro g
    exact Subtype.ext (mem_centralizer_singleton_iff.mp g.property)
  have hfix : omegaOneCenterAmbient (S : Subgroup H) ⊓ centralizer (N : Set H) = zpowers zh := by
    apply map_injective H.subtype_injective
    rw [← map_inf_centralizer_of_injective H.subtype H.subtype_injective,
      hZmap,hNmap,MonoidHom.map_zpowers]
    exact hfixed
  obtain ⟨hgen,hnot,h8⟩ := hU.omegaCenter_span_eight_of_moved_plane U S hUS hspan A hcard
    zh (fun he => hz1 (congrArg Subtype.val he)) hzS hzc hfix
  have hg := congrArg (map H.subtype) hgen
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (centralizerOmegaOrbit_le hz),
    hWmap,MonoidHom.map_zpowers] at hg
  have hn : z ∉ (⁅centralizerOmegaOrbit T z,
      conjugateSpanBy (elementaryAbelianMaxJ R) H⁆ : Subgroup G) := by
    intro hzW
    rw [←hWmap] at hzW
    obtain ⟨a,ha,he⟩ := hzW
    exact hnot ((show a = zh from Subtype.ext he) ▸ ha)
  have hc : Nat.card (centralizerOmegaOrbit T z) = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe (centralizerOmegaOrbit_le hz)).toEquiv).symm.trans h8
  refine ⟨hg,hn,hc,?_⟩
  change Nat.log 2 _ = 3
  rw [hc]
  decide

/-- Apply the rank-three orbit calculation with all local premises supplied by the original R₁ product. -/
theorem original_R1_centralizer_eight
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hcase : normalizer (ChapterB.baumann (firstFlagCore h structural D m) : Set G) ≤
      normalizer (L : Set G) ∨ ChapterC.IsShort L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hVJ : V ≤ elementaryAbelianMaxJ (firstFlagCore h structural D m))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ (Y = selectedFirstResidual T L V z.val ∧ Nat.card (Y ⧸ pCore 2 Y) = 3))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G)))
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (h1342 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      (primeToResidual 3 (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype = L) :
    let U := centralizerOmegaOrbit T z.val
    let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore h structural D m))
      (centralizer ({z.val} : Set G))
    U = (⁅U,I⁆ : Subgroup G) ⊔ zpowers z.val ∧ z.val ∉ (⁅U,I⁆ : Subgroup G) ∧
      Nat.card U = 8 ∧ Representation.BinaryOffender.rank U = 3 := by
  obtain ⟨_,_,_,hrank,_,_,_,_,_⟩ := centralizer_pair_quotient_of_original_R1
    h₀ h structural D m hcase z hz hzL hVJ hout hfusion h1339 hsolv hindex h1342
  obtain ⟨_,_,hfixed,_,_⟩ := original_R1_full_seed
    h₀ h structural D m hcase z hz hzL hVJ hout hfusion h1339 hsolv hindex h1342
  exact centralizer_omega_eight_of_thompson_fixed h₀ hz (fun he => hzL (he ▸ one_mem _))
    (firstFlagCore h structural D m) (firstFlagCore_local_data h structural D m z hz hzL).1
    hrank hfixed

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
