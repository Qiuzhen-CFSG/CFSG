module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernelNondegenerate
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.NumericalGeometry
public import Theory.Quasithin.Rank

/-!
# Original odd-rank bounds for the orthogonal constituent

The original small-actor geometry identifies the dotted action kernel with
O₂ of the point normalizer. Odd-prime ranks therefore descend to the actual
terminal quotient. Centerlessness of the constituent image then removes
its central kernel and transports those bounds through the faithful action.

The orthogonal consumer separates degrees four and six from degrees at
least eight. Low dimensions require centerlessness and either module
invariance or a cubic-rank obstruction. Higher dimensions require
centerlessness and cubic rank at least three. This avoids asserting
universal natural-module invariance in the triality case. These intrinsic
model premises remain explicit; this module does not finish their exclusion.

Source: Aschbacher--Smith G.10.15, printed p.363, with the original
14.3.12--15 small-actor hypotheses, printed pp.993--994.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open scoped IsMulCommutative
namespace ExchangedCentralSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : ExchangedCentralSource T M Mc F g B v L I)


include s

/-- The original small-actor geometry makes the dotted quotient kernel a
 two-group, so its odd-prime ranks retain the source bounds. -/
theorem terminal_odd_primeRank_le_two (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    primeRank p F.TerminalHdot ≤ 2 := by
  let h := source_lemma_14_2_4 s.simple T s.empty s.maximal s.unique_overgroup
    s.many_overgroups s.seed_card (Classical.choice s.centralizer_quotient)
  let d := Recognition.rankTwo_closure_geometry h F s.nonabelian
  have hk := (Recognition.rankTwo_small_actor_geometry h F g d s.nonabelian
    s.parabolic_mem s.normalizer_not_mem s.hypothesis s.small_actor).2.2.2.2
  have htwo : IsPGroup 2 F.terminalHatAction.ker := by
    rw [hk]
    exact pCore_isPGroup
  exact (primeRank_quotient_le_of_isTwoGroup p hp _ htwo).trans
    ((Recognition.pointNormalizer_sqtk s.simple F (by decide)).stronglyQuasithin
      p Fact.out hp)

/-- Centerlessness removes the central constituent kernel before transporting
 the original odd-rank bound to its image. -/
theorem constituentImage_odd_primeRank_le_two
    (hc : center s.constituentLinearAction.range = ⊥)
    (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    primeRank p s.constituentLinearAction.range ≤ 2 := by
  let e : (componentOrbit L ⊤) ≃* s.constituentLinearAction.range :=
    MonoidHom.ofInjective
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) I).injective.comp
        (s.faithful_of_constituentImage_centerless hc))
  rw [← primeRank_equiv p e]
  exact (_root_.primeRank_le_of_injective p (componentOrbit L ⊤).subtype
    (componentOrbit L ⊤).subtype_injective).trans (s.terminal_odd_primeRank_le_two p hp)

/-- A sufficient orthogonal-model contract separates low-degree module
 invariance from the cubic-rank obstruction in higher degree. These two
 intrinsic model assertions remain explicit. -/
theorem false_of_orthogonal_model_inputs
    (hproper : ¬ Function.Surjective
      (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
        s.selected.invariant).toRepresentation.asGroupHom)
    (hnd : (B.restrict I).Nondegenerate)
    (q : QuadraticForm (ZMod 2) I) (hq : q.polarBilin = B.restrict I)
    (heq : s.constituentLinearAction.range =
      ChapterG.Section12.embeddedResidual q.isometrySubgroup)
    (hlow : q.polarBilin.Nondegenerate → 2 < finrank (ZMod 2) I →
      finrank (ZMod 2) I ≤ 6 →
      center (ChapterG.Section12.embeddedResidual q.isometrySubgroup) = ⊥ ∧
      (ImageAutomorphismsLinear (ChapterG.Section12.embeddedResidual q.isometrySubgroup) ∨
        3 ≤ primeRank 3 (ChapterG.Section12.embeddedResidual q.isometrySubgroup)))
    (hhigh : q.polarBilin.Nondegenerate → 8 ≤ finrank (ZMod 2) I →
      center (ChapterG.Section12.embeddedResidual q.isometrySubgroup) = ⊥ ∧
      3 ≤ primeRank 3 (ChapterG.Section12.embeddedResidual q.isometrySubgroup)) : False := by
  have hqn : q.polarBilin.Nondegenerate := hq.symm ▸ hnd
  by_cases hd : finrank (ZMod 2) I ≤ 6
  · have hl := hlow hqn s.dimension_gt_two hd
    rw [← heq] at hl
    rcases hl.2 with hlin | hrank
    · exact s.not_imageAutomorphismsLinear_of_constituentImage_centerless hproper hl.1 hlin
    · have hb := s.constituentImage_odd_primeRank_le_two hl.1 3 (by decide)
      omega
  · obtain ⟨n,hn⟩ := AlternatingForm.even_finrank (B.restrict I)
      (fun w => s.hypothesis.alternating w) hnd
    have hh := hhigh hqn (by omega)
    rw [← heq] at hh
    have hb := s.constituentImage_odd_primeRank_le_two hh.1 3 (by decide)
    omega

end ExchangedCentralSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
