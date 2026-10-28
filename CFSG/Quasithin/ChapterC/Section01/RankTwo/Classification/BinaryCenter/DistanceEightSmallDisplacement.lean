module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Center.SmallDisplacement

/-!
# Small displacement on the original large-distance commutator core

The source core in the free amalgam has no new central elements after quotient
by a locally central subgroup of order at most two. The original commutator
core maps onto that precise core under the injective replacement embedding.
Restricting the original central subgroup and transporting commutators along
this embedding yields the same conclusion in the original group.

This uses centrality of the specified subgroup in the original group. It does
not infer such centrality from the replacement's fixed factor.

Source: Meierfrankenfeld--Stellmacher (1993), section 7; Aschbacher--Smith
C.1.34(4) and the large binary branch of 15.3.31, printed pp.136--137,1132.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.InputSetup
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}}
  {L R : Subgroup J} {h : Input κ L R} (t : InputSetup h)

private theorem core_le_replacement : commutatorCore L ≤ t.reduction.overgroup := by
  rw [← t.core_pullback]
  exact map_subtype_le _

private theorem core_image :
    ((commutatorCore L).subgroupOf t.reduction.overgroup).map (embedM t.reduction.radical) =
      core t.reduction.radical (alpha t.reduction.radical) := by
  rw [← t.core_pullback]
  change (((core t.reduction.radical (alpha t.reduction.radical)).comap
    (embedM t.reduction.radical)).map t.reduction.overgroup.subtype |>.comap
    t.reduction.overgroup.subtype).map (embedM t.reduction.radical) = _
  rw [comap_map_eq_self_of_injective t.reduction.overgroup.subtype_injective]
  rw [core_alpha _ t.source.two_group t.source.core_le t.source.residual,
    comap_map_eq_self_of_injective (embedM_injective _)]

/-- A central subgroup of order at most two creates no new central elements in
 the original commutator core, using the actual large-distance source layers. -/
theorem large_core_small_displacement
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
    {A N : Subgroup J} (hA : A ≤ commutatorCore L) (hN : N ≤ commutatorCore L)
    (hcentral : N ≤ center J) (hcard : Nat.card N ≤ 2)
    (hcomm : ⁅A,commutatorCore L⁆ ≤ N) :
    A ≤ centralizer (commutatorCore L : Set J) := by
  let P := t.reduction.overgroup
  let f := embedM t.reduction.radical
  let A' := (A.subgroupOf P).map f
  let N' := (N.subgroupOf P).map f
  have hAP : A ≤ P := hA.trans (core_le_replacement t)
  have hNP : N ≤ P := hN.trans (core_le_replacement t)
  have hA' : A' ≤ core t.reduction.radical (alpha t.reduction.radical) := by
    rw [← core_image t]
    exact map_mono (comap_mono hA)
  have hN' : N' ≤ centralizer
      (stabilizer t.reduction.radical (alpha t.reduction.radical) : Set _) := by
    rintro x ⟨n,hn,rfl⟩ y hy
    rw [alpha,stabilizer_m_base] at hy
    obtain ⟨m,rfl⟩ := hy
    change f m * f n = f n * f m
    rw [← map_mul,← map_mul]
    apply congrArg f
    apply Subtype.ext
    exact mem_center_iff.mp (hcentral hn) m
  have hc : Nat.card N' ≤ 2 := by
    rw [card_map_of_injective (embedM_injective _),
      Nat.card_congr (subgroupOfEquivOfLe hNP).toEquiv]
    exact hcard
  have hh : ⁅A',core t.reduction.radical (alpha t.reduction.radical)⁆ ≤ N' := by
    rw [← core_image t,← map_commutator]
    apply map_mono
    intro x hx
    have hm := mem_map_of_mem P.subtype hx
    rw [map_commutator,map_subgroupOf_eq_of_le hAP,
      map_subgroupOf_eq_of_le (core_le_replacement t)] at hm
    exact hcomm hm
  have hNK : N' ≤ core t.reduction.radical (alpha t.reduction.radical) := by
    rw [← core_image t]
    exact map_mono (comap_mono hN)
  have hf := DistanceEight.CoreFactors.Center.small_core_displacement_centralizes
    common earlier A' N' hA' hNK hN' hc hh
  intro a ha x hx
  let aP : P := ⟨a,hAP ha⟩
  let xP : P := ⟨x,(core_le_replacement t) hx⟩
  have ha' : f aP ∈ A' := mem_map_of_mem _ ha
  have hx' : f xP ∈ core t.reduction.radical (alpha t.reduction.radical) := by
    rw [← core_image t]
    exact mem_map_of_mem _ hx
  have he := hf ha' (f xP) hx'
  rw [← map_mul,← map_mul] at he
  exact congrArg Subtype.val ((embedM_injective t.reduction.radical) he)
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.InputSetup
