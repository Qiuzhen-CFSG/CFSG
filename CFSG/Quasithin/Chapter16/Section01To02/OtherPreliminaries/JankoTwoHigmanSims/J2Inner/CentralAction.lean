module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.J2CentralClass
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.KernelExclusion

/-!
# The self-centralizing two-kernel in the central J₂ class

For each of the radical's five sixteen-point orbits, a marked radical element
fixes its base point and has no fixed points in any of the other four orbits.
An element centralizing the radical must therefore fix every color. The
previously constructed five-point action identifies its kernel with the radical,
which is the intrinsic two-core. This proves the action condition required to
exclude components, independently of the central-product shape.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 16.1.5(8) and
16.1.7(f), printed pp.1172–1173. The five finite checks use the existing certified
ATLAS radical tables; no additional group enumeration is needed.
-/

public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.J2Inner

open Subgroup Theory.GroupTheory
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.GeneratorPair
open Sporadic.LeechRelated.J2.ExceptionalParabolics
open Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic
open Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.QuotientActions
open Sporadic.LeechRelated.J2.ExceptionalParabolics.Seed
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims

private def marker : Fin 5 → Fin 32 := ![1, 7, 25, 2, 3]

set_option maxRecDepth 100000 in
private theorem marker_fixed : ∀ i,
    RadicalStructureData.tablePerm (marker i) (basePoint i) = basePoint i := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem marker_color : ∀ i x j,
    RadicalStructureData.tablePerm (marker i) x = x → color x = some j → j = i := by
  decide +kernel

/-- The radical centralizer in the literal central involution centralizer lies in the radical. -/
theorem radical_centralizer_le : centralizer (radical.subgroupOf l₁ : Set l₁) ≤ radical.subgroupOf l₁ := by
  intro g hg
  rw [← innerAction_ker card_radical]
  change innerAction g = 1
  apply Subtype.ext
  apply Equiv.ext
  intro i
  have hq : radicalElement (marker i) ∈ radical := radicalElement_mem _
  let q : l₁ := ⟨radicalElement (marker i), radical_le_l₁ hq⟩
  have hcomm : q * g = g * q := mem_centralizer_iff.mp hg q hq
  have hpoint := congrArg (fun z : l₁ => inclusion z.val (basePoint i)) hcomm
  change inclusion (radicalElement (marker i) * g.val) (basePoint i) =
    inclusion (g.val * radicalElement (marker i)) (basePoint i) at hpoint
  simp only [map_mul, Equiv.Perm.mul_apply, radicalElement_inclusion, marker_fixed] at hpoint
  apply marker_color i (inclusion g.val (basePoint i)) ((innerAction g).val i) hpoint
  simpa only [color_basePoint, Option.map_some] using innerAction_spec g (basePoint i)

/-- The central representative has a self-centralizing normal two-kernel. -/
theorem t_selfCentralizing :
    HasSelfCentralizingNormalTwoSubgroup
      (Subgroup.centralizer ({FirstFusion.t} : Set Carrier)) := by
  change HasSelfCentralizingNormalTwoSubgroup l₁
  refine ⟨pCore 2 l₁, inferInstance, pCore_isPGroup, ?_⟩
  rw [l₁_core_eq_of_radical_action card_radical innerAction innerAction_surjective
    (innerAction_ker card_radical)]
  exact radical_centralizer_le

/-- No component occurs in the central inner class. -/
theorem t_not_isComponent
    (K : Subgroup (Subgroup.centralizer ({FirstFusion.t} : Set Carrier))) :
    ¬ IsComponent (Subgroup.centralizer ({FirstFusion.t} : Set Carrier)) K :=
  t_selfCentralizing.not_isComponent K

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.J2Inner
