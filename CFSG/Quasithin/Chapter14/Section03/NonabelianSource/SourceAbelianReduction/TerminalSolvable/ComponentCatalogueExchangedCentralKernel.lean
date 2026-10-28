module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernelSource
public import Theory.Representation.NormalComponentConstituents.Exchanged

/-!
# Assembling the exchanged dual pair after the model obstructions

Properness supplies the spanning pair through the original G.10 completion.
Excluding the nondegenerate alternative makes the original constituent
isotropic. The literal form pairing and homogeneous selection then prove
faithfulness, non-self-duality and duality with every moved X-conjugate.

The full-GL and nondegenerate model obstructions are explicit premises of
this conditional assembly. They remain independent source obligations;
this module does not assert the completed central-kernel branch.

Source: Aschbacher--Smith G.10.15, printed pp.362--363.
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

/-- Once the two independent model obstructions have been proved, the
original form alternative is isotropic. The spanning exchanged pair then
supplies all the faithful constituent data, including non-self-duality.
Neither central-kernel triviality nor a model isomorphism is assumed here. -/
theorem faithful_data_of_proper_not_nondegenerate
    (hproper : ¬ Function.Surjective
      (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
        s.selected.invariant).toRepresentation.asGroupHom)
    (hnot : ¬ (B.restrict I).Nondegenerate) :
    ExchangedFaithfulConstituentData F.terminalRepresentation B L
      (F.terminalDot (F.X g)) I s.selected := by
  let H := componentOrbit L ⊤
  let : H.Normal := componentOrbit_top_normal L
  let X := F.terminalDot (F.X g)
  have hiso := s.form_cases.resolve_right hnot
  obtain ⟨hgeo,hspan,_,_⟩ := Recognition.source_terminal_exchanged_constituent_completion
    s.simple T s.empty s.maximal s.unique_overgroup s.many_overgroups s.seed_card
    (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
    s.normalizer_not_mem s.nonsolvable s.hypothesis s.component s.moved
    s.selected s.point_not_mem hproper
  have hxinv (x : X) : (x : F.TerminalHdot)⁻¹ = x :=
    inv_eq_iff_mul_eq_one.mpr (by
      simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2)
        (x : F.TerminalHdot) x.property)
  have hpair (x : X) (hx : I.map (F.terminalRepresentation (x : F.TerminalHdot)⁻¹) ≠ I) :
      I ⊔ I.map (F.terminalRepresentation (x : F.TerminalHdot)⁻¹) = ⊤ := by
    rw [hxinv] at hx ⊢
    exact (s.hypothesis.independent_orbit_pair I s.dimension_gt_two
      s.independent x hx).1.symm.trans hspan
  obtain ⟨x,hx,_⟩ := hgeo
  have hex : ∃ x : X, I.map (F.terminalRepresentation (x : F.TerminalHdot)⁻¹) ≠ I :=
    ⟨x,by rwa [hxinv]⟩
  obtain ⟨hf,hs,hd⟩ := s.selected.faithful_dual_of_isotropic_pair
    F.terminalRepresentation s.hypothesis.faithful B s.hypothesis.nondegenerate
    s.hypothesis.preserves s.fixedSpace_eq_bot s.irreducible hiso hex hpair
  refine ⟨hf,hs,hiso,?_⟩
  intro y hy
  exact hd y (by rwa [hxinv])

end ExchangedCentralSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
