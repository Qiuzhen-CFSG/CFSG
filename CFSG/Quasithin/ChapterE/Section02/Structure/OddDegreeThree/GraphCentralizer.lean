module
public import Theory.SpecificGroups.SL3.GraphInvariantLevi
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Geometry.RootGeneration
public import Theory.GroupTheory.CentralizerEquivBounds
import all CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Geometry.RootGeneration
/-!
# Inner involution centralizers in the full odd PSL₃ graph extension

Inverse transpose exchanges the two complementary parabolics containing the
GL₂ Levi. The graph-invariant Levi theorem therefore makes the full graph
extension centralizer maximal. Literal matrix lifts and inner conjugation
carry the statement to every inner involution. No maximality in PSL₃ itself
is asserted. The intentional internal import reuses the existing marked
innerSL action equations without changing their public boundary.

Source: Aschbacher–Smith E.2.2(2d), printed pp.215–216.
-/
public section
open Subgroup Matrix
open scoped MatrixGroups
open Matrix.PSL3 Matrix.PSL3.OuterSolvable
open Matrix.PSL3.OddPrimeGraphExtension
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
open CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerGenerationGeometry
namespace CFSG.Quasithin.ChapterE.Structure.OddDegreeThree.GraphCentralizer
variable (F:Type*) [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]

omit [Finite F] [IsSimpleGroup PSL(3,F)] in
private theorem standard_eq_of_proper (h2:(2:F)≠0)
    (M:Subgroup (graphExtension F))
    (hC:centralizer ({standardInner F}:Set (graphExtension F))≤M) (hM:M≠⊤) :
    M=centralizer ({standardInner F}:Set (graphExtension F)) := by
  have hgamma : graphElement F∈M := hC (graphElement_centralizes_standard F)
  have hpre : M.comap (innerSL F) = centralizer ({SL3.standardInvolution F}:Set SL(3,F)) := by
    apply SL3.LeviGraph.eq_centralizer F h2
    · intro y hy
      apply hC
      apply mem_centralizer_singleton_iff.mpr
      exact (map_mul (innerSL F) y _).symm.trans
        ((congrArg (innerSL F) (mem_centralizer_singleton_iff.mp hy)).trans
          (map_mul (innerSL F) _ y))
    · intro y hy
      change innerSL F (graphSL F y)∈M
      rw [innerSL_graph]
      exact M.mul_mem (M.mul_mem hgamma hy) (M.inv_mem hgamma)
    · intro he
      apply hM
      apply eq_top_of_standard_block_plane F M hC
        (SpecialLinearGroup.transvection (show (1:Fin 3)≠2 by decide) 1)
      · exact show _∈M.comap (innerSL F) from he ▸ mem_top _
      all_goals simp [SpecialLinearGroup.transvection_coe]
  apply le_antisymm _ hC
  intro x hx
  have hxin : x.val∈graphExtension F := x.property
  obtain ⟨i,hi,c,hc,hic⟩ := mem_sup_of_normal_left.mp hxin
  have hi' : ∃y:SL(3,F), (innerSL F y).val=i := by
    obtain ⟨z,rfl⟩ := hi
    obtain ⟨y,rfl⟩ := projection_surjective F z
    exact ⟨y,rfl⟩
  obtain ⟨y,rfl⟩ := hi'
  have hc' : ∃d∈zpowers (graphElement F), (d:graphExtension F).val=c := by
    obtain ⟨n,rfl⟩ := hc
    exact ⟨graphElement F^n, zpow_mem (mem_zpowers _) _, rfl⟩
  obtain ⟨d,hd,rfl⟩ := hc'
  have hxyd : x=innerSL F y*d := Subtype.ext hic.symm
  have hdC : d∈centralizer ({standardInner F}:Set (graphExtension F)) :=
    zpowers_le.mpr (graphElement_centralizes_standard F) hd
  have hyM : innerSL F y∈M := by
    have hh := M.mul_mem hx (M.inv_mem (hC hdC))
    simpa only [hxyd,mul_inv_cancel_right] using hh
  have hyC : y∈centralizer ({SL3.standardInvolution F}:Set SL(3,F)) :=
    hpre ▸ hyM
  rw [hxyd]
  apply mul_mem _ hdC
  apply mem_centralizer_singleton_iff.mpr
  exact (map_mul (innerSL F) y _).symm.trans
    ((congrArg (innerSL F) (mem_centralizer_singleton_iff.mp hyC)).trans
      (map_mul (innerSL F) _ y))

/-- Full graph-extension centralizers of inner involutions are maximal;
the intrinsic projective centralizer need not be maximal. -/
theorem isCoatom (h2:(2:F)≠0) (z:graphExtension F)
    (hz:orderOf z=2) (hzI:z∈innerPart F) :
    IsCoatom (centralizer ({z}:Set (graphExtension F))) := by
  obtain ⟨s,hs⟩ := exists_standard_coordinates F h2 z hz hzI
  have hn : centralizer ({z}:Set (graphExtension F))≠⊤ := by
    intro he
    have hzC : z∈centralizer (innerPart F:Set (graphExtension F)) := by
      rw [mem_centralizer_iff]
      intro y hy
      exact (mem_centralizer_singleton_iff.mp (show y∈centralizer ({z}:Set (graphExtension F)) from he ▸ mem_top y))
    rw [innerPart_centralizer,mem_bot] at hzC
    simp [hzC] at hz
  apply isCoatom_iff_ge_of_le.mpr ⟨hn,?_⟩
  intro M hM hCM
  let e := MulAut.conj (innerSL F s)
  have hez : e (standardInner F)=z := hs
  have hCpre : centralizer ({standardInner F}:Set (graphExtension F))≤M.comap e.toMonoidHom := by
    intro y hy
    apply hCM
    apply mem_centralizer_singleton_iff.mpr
    change e y*z=z*e y
    rw [← hez,← map_mul,← map_mul,mem_centralizer_singleton_iff.mp hy]
  have hpre : M.comap e.toMonoidHom≠⊤ := by
    intro he
    apply hM
    rw [← map_comap_eq_self_of_surjective (f:=e.toMonoidHom) e.surjective M,he,
      map_top_of_surjective _ e.surjective]
  have hpreC := standard_eq_of_proper F h2 _ hCpre hpre
  intro y hy
  obtain ⟨x,rfl⟩ := e.surjective y
  have hx : x∈centralizer ({standardInner F}:Set (graphExtension F)) := hpreC ▸ hy
  apply mem_centralizer_singleton_iff.mpr
  rw [← hez,← map_mul,← map_mul,mem_centralizer_singleton_iff.mp hx]
end CFSG.Quasithin.ChapterE.Structure.OddDegreeThree.GraphCentralizer
