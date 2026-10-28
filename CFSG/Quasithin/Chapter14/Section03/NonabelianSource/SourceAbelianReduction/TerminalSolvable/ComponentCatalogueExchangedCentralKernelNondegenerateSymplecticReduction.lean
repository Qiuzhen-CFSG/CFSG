module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernelNondegenerate
public import Theory.Representation.NormalComponentConstituents.FullLinear

/-!
# The original elementary actor on a centerless constituent image

The full elementary actor X acts faithfully by conjugation on the normal
component orbit H. An element in the conjugation kernel must stabilize I:
otherwise homogeneous selection says its conjugation is outer. Once it
stabilizes I, the original faithfulness of Y = N_X(I) on H kills it.

When the constituent image is centerless, the proved central-kernel argument
identifies H with that actual image. Transporting X through this very action
map gives an elementary automorphism subgroup of order 2^(dim I - 1), with
an element that does not preserve the constituent module. The order uses
the exact stabilizer degree supplied by the original small-actor hypothesis.
In degree four this retains an elementary group of order eight, permitting
the natural-S6 placement theorem for Aut(A6); invariance under every
A6 automorphism would be false.

The final theorem reduces the symplectic residual row to two explicit model
facts, in degree four and in degree at least six. Neither model fact is
asserted here. Recognition remains the literal residual equality on the
same constituent. This is a specialized alternative to the exceptional
Sylow-commutator step of Aschbacher--Smith G.10.15, printed p.363 of
`refs/quasithin.pdf`, using the stronger original 14.3.15 rank data.
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

/-- The original actor embeds in the automorphisms of the literal constituent
image, with its exact order and a specified failure of module invariance.
Centerlessness is an explicit premise, used to discharge the central kernel. -/
theorem exists_constituent_actor_obstruction
    (hproper : ¬ Function.Surjective
      (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
        s.selected.invariant).toRepresentation.asGroupHom)
    (hc : center s.constituentLinearAction.range = ⊥) :
    ∃ E : Subgroup (MulAut s.constituentLinearAction.range),
      IsElementaryAbelian 2 E ∧ Nat.card E = 2 ^ (finrank (ZMod 2) I - 1) ∧
      ∃ α ∈ E, ¬ ∃ c : I ≃ₗ[ZMod 2] I,
        ∀ k : s.constituentLinearAction.range, ∀ u : I,
          c (k.val u) = (α k).val (c u) := by
  let H := componentOrbit L ⊤
  let X := F.terminalDot (F.X g)
  let : H.Normal := componentOrbit_top_normal L
  let Y := (subspaceStabilizer F.terminalRepresentation I).subgroupOf X
  let : IsElementaryAbelian 2 Y :=
    IsElementaryAbelian.of_injective Y.subtype Y.subtype_injective
  obtain ⟨hgeo,_,_,hY⟩ := Recognition.source_terminal_exchanged_constituent_completion
    s.simple T s.empty s.maximal s.unique_overgroup s.many_overgroups s.seed_card
    (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
    s.normalizer_not_mem s.nonsolvable s.hypothesis s.component s.moved
    s.selected s.point_not_mem hproper
  let f : X →* MulAut H := MulAut.conjNormal.comp X.subtype
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro z hz
    have hz1 : f z = 1 := hz
    have hzinv : (z : F.TerminalHdot)⁻¹ = z := inv_eq_iff_mul_eq_one.mpr (by
      simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2)
        (z : F.TerminalHdot) z.property)
    have hzY : (z : F.TerminalHdot) ∈ subspaceStabilizer F.terminalRepresentation I := by
      by_contra hn
      have hm : I.map (F.terminalRepresentation (z : F.TerminalHdot)⁻¹) ≠ I := by
        rw [hzinv]
        exact fun he => hn ((subspace_map_eq_iff F.terminalRepresentation I _).mp he)
      have ho := s.selected.conjugation_not_inner F.terminalRepresentation
        s.fixedSpace_eq_bot z hm
      apply ho
      change f z ∈ MulAut.innerSubgroup H
      rw [hz1]
      exact (MulAut.innerSubgroup H).one_mem
    have hzc : (z : F.TerminalHdot) ∈ centralizer (H : Set F.TerminalHdot) := by
      rw [mem_centralizer_iff]
      intro h hh
      have he := congrArg (fun a : MulAut H => (a ⟨h,hh⟩ : F.TerminalHdot)) hz1
      change (z : F.TerminalHdot) * h * (z : F.TerminalHdot)⁻¹ = h at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    have he := hY (⟨z,hzY⟩ : Y) hzc
    exact mem_bot.mpr (congrArg Subtype.val he)
  let e : H ≃* s.constituentLinearAction.range := MonoidHom.ofInjective
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) I).injective.comp
      (s.faithful_of_constituentImage_centerless hc))
  let a : X →* MulAut s.constituentLinearAction.range :=
    (MulAut.congr e).toMonoidHom.comp f
  have ha : Function.Injective a := (MulAut.congr e).injective.comp hf
  let E := a.range
  have hE : IsElementaryAbelian 2 E :=
    IsElementaryAbelian.of_injective (MonoidHom.ofInjective ha).symm.toMonoidHom
      (MonoidHom.ofInjective ha).symm.injective
  have hcard : Nat.card E = 2 ^ (finrank (ZMod 2) I - 1) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective ha).toEquiv]
    have hr : finrank (ZMod 2) (Additive Y) + 1 =
        finrank (ZMod 2) (Additive X) := (source_exchanged_stabilizer_degree s.simple T s.empty s.maximal
      s.unique_overgroup s.many_overgroups s.seed_card
      (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
      s.normalizer_not_mem s.nonsolvable s.hypothesis s.component s.moved
      s.selected s.point_not_mem).1
    have hd : finrank (ZMod 2) I = finrank (ZMod 2) (Additive Y) + 2 :=
      source_exchanged_stabilizer_degree_eq s.simple T s.empty s.maximal
      s.unique_overgroup s.many_overgroups s.seed_card
      (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
      s.normalizer_not_mem s.nonsolvable s.hypothesis s.component s.moved
      s.selected s.point_not_mem hproper s.small_actor
    change Nat.card (Additive X) = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    congr 1
    omega
  obtain ⟨x,hx,_⟩ := hgeo
  refine ⟨E,hE,hcard,a x,⟨x,rfl⟩,?_⟩
  rintro ⟨c,hc'⟩
  let R := invariantSubspace F.terminalRepresentation H I s.selected.invariant
  have hα (h : H) : a x (e h) = e (MulAut.conjNormal (x : F.TerminalHdot) h) := by
    change e (MulAut.conjNormal (x : F.TerminalHdot) (e.symm (e h))) = _
    rw [e.symm_apply_apply]
  let b : RepEquiv R.toRepresentation
      (conjugateRep R.toRepresentation (x : F.TerminalHdot)) := .mk c (by
    intro h
    apply LinearMap.ext
    intro u
    have he := hc' (e h) u
    rw [hα] at he
    exact he)
  have hxi : (x : F.TerminalHdot)⁻¹ = x := inv_eq_iff_mul_eq_one.mpr (by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2)
      (x : F.TerminalHdot) x.property)
  exact s.selected.not_equiv_moved F.terminalRepresentation s.fixedSpace_eq_bot x
    (by rwa [hxi])
    ⟨(b.trans (conjugateSubrepresentationEquiv F.terminalRepresentation H R
      (x : F.TerminalHdot)).symm).toRepresentationEquiv⟩

/-- The literal symplectic recognition equality is excluded once the two
independent model facts are proved. The degree-four premise only concerns
large elementary automorphism subgroups, rather than all automorphisms. -/
theorem false_of_symplectic_model_inputs
    (hproper : ¬ Function.Surjective
      (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
        s.selected.invariant).toRepresentation.asGroupHom)
    (hnd : (B.restrict I).Nondegenerate)
    (heq : s.constituentLinearAction.range = ChapterG.Section12.embeddedResidual
      (ChapterG.Section12.formStabilizer (B.restrict I)))
    (hfour : finrank (ZMod 2) I = 4 →
      let K := ChapterG.Section12.embeddedResidual
        (ChapterG.Section12.formStabilizer (B.restrict I))
      center K = ⊥ ∧ ∀ E : Subgroup (MulAut K),
        IsElementaryAbelian 2 E → 8 ≤ Nat.card E →
        ∀ α ∈ E, ∃ c : I ≃ₗ[ZMod 2] I,
          ∀ k : K, ∀ u : I, c (k.val u) = (α k).val (c u))
    (hhigher : 6 ≤ finrank (ZMod 2) I →
      let K := ChapterG.Section12.embeddedResidual
        (ChapterG.Section12.formStabilizer (B.restrict I))
      center K = ⊥ ∧ ImageAutomorphismsLinear K) : False := by
  obtain ⟨n,hn⟩ := AlternatingForm.even_finrank (B.restrict I)
    (fun w => s.hypothesis.alternating w) hnd
  have hd := s.dimension_gt_two
  by_cases h4 : finrank (ZMod 2) I = 4
  · have hm := hfour h4
    dsimp only at hm
    rw [← heq] at hm
    obtain ⟨E,hE,hcard,α,hα,hno⟩ := s.exists_constituent_actor_obstruction hproper hm.1
    exact hno (hm.2 E hE (by rw [hcard,h4]; decide) α hα)
  · have hm := hhigher (by omega)
    dsimp only at hm
    rw [← heq] at hm
    exact s.not_imageAutomorphismsLinear_of_constituentImage_centerless hproper hm.1 hm.2

end ExchangedCentralSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
