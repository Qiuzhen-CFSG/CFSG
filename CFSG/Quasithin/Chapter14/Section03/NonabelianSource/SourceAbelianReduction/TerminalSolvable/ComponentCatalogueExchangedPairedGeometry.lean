module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedPairedSylow
public import Theory.GroupTheory.GeneralizedFitting.ElementarySylowOrbit
public import Theory.SpecificGroups.BinaryLinear.OrderFour
public import Theory.Representation.NormalComponentConstituents.Exchanged
public import CFSG.Quasithin.ChapterG.Section10.Components.ExchangedCompletion

/-!
# Properness and geometry of the original paired constituent

The original component's elementary Sylow condition passes to its two-component
orbit and then the literal constituent image. The full binary linear group
contains an element of order four, so this image is proper. Original G.10
completion now gives the spanning exchanged pair and the faithful stabilizer,
with its sharp rank. An isotropic constituent would make H faithful on it,
contradicting the noncentral kernel. Hence the original restricted form is
nondegenerate and supplies self-duality for exactly the same H-action.

No paired-A5 recognition or component-image model is assumed. Those are the
remaining classification obligations after these source premises.
Source: Aschbacher--Smith G.10.15, printed pp.362--363; 14.3.12--15,
printed pp.993--994.
-/

@[expose] public noncomputable section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Representation Representation.BinaryOffender
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
namespace ExchangedPairedSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : ExchangedPairedSource T M Mc F g B v L I)

include s

/-- Elementary Sylow subgroups of the literal original normal component orbit. -/
theorem orbit_sylow_elementary (P : Sylow 2 (componentOrbit L ⊤)) :
    IsElementaryAbelian 2 P :=
  Theory.GroupTheory.ExchangedOrbit.orbit_sylow_elementary s.component s.normalizer_index_eq_two
    s.component_sylow_elementary P

/-- Elementary Sylow subgroups of the literal chosen-constituent action image. -/
theorem image_sylow_elementary
    (P : Sylow 2 (invariantSubspace F.terminalRepresentation
      (componentOrbit L ⊤) I s.selected.invariant).toRepresentation.asGroupHom.range) :
    IsElementaryAbelian 2 P := by
  let f := (invariantSubspace F.terminalRepresentation
    (componentOrbit L ⊤) I s.selected.invariant).toRepresentation.asGroupHom
  let : Finite f.range := Finite.of_surjective _ f.rangeRestrict_surjective
  exact Theory.GroupTheory.ExchangedOrbit.elementary_sylow_image f.rangeRestrict
    f.rangeRestrict_surjective s.orbit_sylow_elementary P

/-- The original chosen constituent has proper H-image in its full linear group. -/
theorem not_fullLinear : ¬ Function.Surjective
    (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
      s.selected.invariant).toRepresentation.asGroupHom := by
  intro hs
  let f : (componentOrbit L ⊤) →* LinearMap.GeneralLinearGroup (ZMod 2) I :=
    (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
      s.selected.invariant).toRepresentation.asGroupHom
  let : Finite (LinearMap.GeneralLinearGroup (ZMod 2) I) := Finite.of_surjective f hs
  exact BinaryLinear.not_elementary_sylow_of_finrank_ge_three (V:=I) (by have := s.dimension_gt_two; omega)
    (Theory.GroupTheory.ExchangedOrbit.elementary_sylow_image f hs s.orbit_sylow_elementary)

/-- The exchanged pair spans the whole original module; the exact stabilizer
acts faithfully both on the constituent and on its normal component orbit. -/
theorem completion :
    ChapterG.Section10.ExchangedConstituentGeometry F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g)) I ∧
    Homogeneous.orbitSpan F.terminalRepresentation (F.terminalDot (F.X g)) I = ⊤ ∧
    let Y := (subspaceStabilizer F.terminalRepresentation I).subgroupOf (F.terminalDot (F.X g))
    (∀ y : Y, (∀ u : I, F.terminalRepresentation ((y : F.terminalDot (F.X g)) : F.TerminalHdot) u = u) → y = 1) ∧
    (∀ y : Y, ((y : F.terminalDot (F.X g)) : F.TerminalHdot) ∈
      centralizer (componentOrbit L ⊤ : Set F.TerminalHdot) → y = 1) :=
  Recognition.source_terminal_exchanged_constituent_completion s.simple T s.empty
    s.maximal s.unique_overgroup s.many_overgroups s.seed_card
    (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
    s.normalizer_not_mem s.nonsolvable s.hypothesis s.component s.moved
    s.selected s.point_not_mem s.not_fullLinear

/-- The sharp degree on the literal subgroup N_X(I), with its inherited
binary vector-space structure. -/
theorem stabilizer_degree :
    let Y := (subspaceStabilizer F.terminalRepresentation I).subgroupOf (F.terminalDot (F.X g))
    letI : IsElementaryAbelian 2 Y :=
      IsElementaryAbelian.of_injective Y.subtype Y.subtype_injective
    finrank (ZMod 2) I = finrank (ZMod 2) (Additive Y) + 2 :=
  source_exchanged_stabilizer_degree_eq s.simple T s.empty s.maximal
    s.unique_overgroup s.many_overgroups s.seed_card
    (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
    s.normalizer_not_mem s.nonsolvable s.hypothesis s.component s.moved
    s.selected s.point_not_mem s.not_fullLinear s.small_actor

/-- The original constituent is nondegenerate: isotropy would force faithfulness
on H and contradict its retained noncentral kernel. -/
theorem nondegenerate : (B.restrict I).Nondegenerate := by
  rcases s.form_cases with hiso | hnd
  · exfalso
    let H := componentOrbit L ⊤
    let : H.Normal := componentOrbit_top_normal L
    let X := F.terminalDot (F.X g)
    obtain ⟨hgeo,hspan,_,_⟩ := s.completion
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
    obtain ⟨hf,_,_⟩ := s.selected.faithful_dual_of_isotropic_pair
      F.terminalRepresentation s.hypothesis.faithful B s.hypothesis.nondegenerate
      s.hypothesis.preserves s.fixedSpace_eq_bot s.irreducible hiso hex hpair
    apply s.noncentral_kernel
    rw [(MonoidHom.ker_eq_bot_iff _).mpr hf]
    exact bot_le
  · exact hnd

/-- Self-duality for the same literal H-action, induced by the original form. -/
theorem constituent_selfDual : Nonempty (Representation.Equiv
    (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
      s.selected.invariant).toRepresentation
    (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
      s.selected.invariant).toRepresentation.dual) := by
  refine ⟨.mk ((B.restrict I).toDual s.nondegenerate) ?_⟩
  intro a
  ext u w
  change B (F.terminalRepresentation a u) w =
    B u (F.terminalRepresentation (a⁻¹:componentOrbit L ⊤) w)
  have he := s.hypothesis.preserves (a:F.TerminalHdot) (u:Additive F.Uhat)
    (F.terminalRepresentation (a⁻¹:componentOrbit L ⊤) w)
  simpa only [← Module.End.mul_apply,←map_mul,Subgroup.coe_inv,mul_inv_cancel,map_one,
    Module.End.one_apply] using he

end ExchangedPairedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
