module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedKernelHigher.NaturalModels
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedKernelHigher.TransvectionTransport

/-!
# Complete image recognition at higher marked multiplicity

The orthogonal constituent supplies a rank-one action and G.6.4 gives the
natural A₅–A₈ rows on the original component orbit. The small rows and A₇
already give the image catalogue, including equality with the whole orbit.
For A₈, the natural module's trivial commutant makes each same-orbit
intertwiner equivariant for the chosen actor. Thus the rank-one action
transfers to the original marked constituent. Its actual S₈ normalizer
realization sends every nontrivial actor to a transposition. Sign gives at
most two actions, contradicting the original fixed-line condition.

This closes the higher-multiplicity branch and its literal local lift.
Faithful-actor and the other two-copy recognition branches remain separate.
Source: Aschbacher--Smith G.11.9, printed p.369;14.3.15, p.994.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
namespace MarkedSource
variable {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : MarkedSource T M Mc F g B v L I)
include s
open MarkedHigherTransport

/-- Transfer the actual rank-one orthogonal witness to the original marked
constituent using the trivial commutant of its natural A₈ action. -/
theorem source_higher_natural_eight_rank_one
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : 2 * Module.finrank (ZMod 2) I < Module.finrank (ZMod 2) (Additive F.Uhat))
    (hm : ChapterG.Section09.Quasiequivalent
      (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I s.selected.invariant).toRepresentation
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 8)))
    (x : F.terminalDot (F.X g))
    (hx : (x : F.TerminalHdot) ∉ centralizer (componentOrbit L ⊤ : Set F.TerminalHdot)) :
    Module.finrank (ZMod 2)
      (LinearMap.range ((F.terminalRepresentation x - 1).comp I.subtype)) = 1 := by
  let H := componentOrbit L ⊤
  let : H.Normal := componentOrbit_top_normal L
  obtain ⟨e,c,hc⟩ := hm
  obtain ⟨J,hJ,_,_,hxJ,hr⟩ := s.source_exists_orthogonal_constituent_rank_one hk hd x hx
  let R := invariantSubspace F.terminalRepresentation H J hJ.choose
  have hi : IsIrreducible R.toRepresentation :=
    hJ.irreducible_of_normal_restriction F.terminalRepresentation
      (s.hypothesis.irreducible_of_not_solvable s.nonsolvable) H
  obtain ⟨E,hE⟩ := s.constituents_sameModule R hi
  let X := zpowers (x : F.TerminalHdot)
  have hXI : X ≤ subspaceStabilizer F.terminalRepresentation I :=
    zpowers_le.mpr (s.actor_stabilizes x.property)
  have hXJ : X ≤ subspaceStabilizer F.terminalRepresentation J := zpowers_le.mpr hxJ
  let P := H ⊔ X
  have hHP : H ≤ P := le_sup_left
  let σ := ChapterG.Section09.constituentAction F.terminalRepresentation H X I s.selected.invariant hXI
  let τ := ChapterG.Section09.constituentAction F.terminalRepresentation H X J hJ.choose hXJ
  have hEP : ∀ p : P, ∀ u, E (σ p u) = τ p (E u) := by
    apply Representation.marked_equivariant_of_trivial_normal_commutant σ τ (H.subgroupOf P) E
    · intro h u
      exact hE ⟨h.val.val,h.property⟩ u
    · intro f hf
      apply natural_eight_commuting_eq_refl
        (invariantSubspace F.terminalRepresentation H I s.selected.invariant).toRepresentation
        e c hc f
      intro h u
      exact hf ⟨⟨h,hHP h.property⟩,h.property⟩ u
  let xp : P := ⟨x,(show X ≤ P from le_sup_right) (mem_zpowers _)⟩
  have ht := LinearMap.FixedSpaceTransport.finrank_range_sub_one_equiv
    E (σ xp) (τ xp) (hEP xp)
  have hrI := constituent_displacement_rank F.terminalRepresentation H X I
    s.selected.invariant hXI ⟨x,mem_zpowers _⟩
  have hrJ := constituent_displacement_rank F.terminalRepresentation H X J
    hJ.choose hXJ ⟨x,mem_zpowers _⟩
  exact hrI.symm.trans (ht.trans (hrJ.trans hr))

/-- The natural A₈ higher-multiplicity row contradicts the actual marked
fixed line. Its orthogonal rank-one witnesses force at most two actions. -/
theorem not_higher_natural_eight
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : 2 * Module.finrank (ZMod 2) I < Module.finrank (ZMod 2) (Additive F.Uhat))
    (hm : ChapterG.Section09.Quasiequivalent
      (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I s.selected.invariant).toRepresentation
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 8))) : False := by
  let H := componentOrbit L ⊤
  let X := F.terminalDot (F.X g)
  let : H.Normal := componentOrbit_top_normal L
  let P := H ⊔ X
  have hHP : H ≤ P := le_sup_left
  have hXP : X ≤ P := le_sup_right
  let σ := MarkedAction.action F.terminalRepresentation H X I s.selected.invariant s.actor_stabilizes
  let j : X →* X.subgroupOf P := {
    toFun := fun x => ⟨⟨x,hXP x.property⟩,x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hfix (x : X) : σ (j x) = 1 ↔ (x : F.TerminalHdot) ∈ centralizer (H : Set F.TerminalHdot) := by
    rw [← source_marked_constituent_fixes_iff_centralizes s.simple T s.empty s.maximal
      s.unique_overgroup s.many_overgroups s.seed_card (Classical.choice s.centralizer_quotient)
      F s.nonabelian g s.parabolic_mem s.normalizer_not_mem s.nonsolvable s.hypothesis
      s.component s.moved s.selected.isIrrPlus s.point_mem x]
    constructor
    · intro he u
      exact congrArg Subtype.val (LinearMap.congr_fun he u)
    · intro he
      ext u
      exact he u
  have hn : ¬ X ≤ centralizer (H : Set F.TerminalHdot) := by
    intro h
    exact (ne_of_lt s.actor_centralizer_lt) (inf_eq_left.mpr h)
  obtain ⟨a,ha,haC⟩ := SetLike.not_le_iff_exists.mp hn
  let aX : X := ⟨a,ha⟩
  have haσ : σ (j aX) ≠ 1 := fun he => haC ((hfix aX).mp he)
  obtain ⟨e,c,hc⟩ := hm
  let eH := (subgroupOfEquivOfLe hHP).trans e
  have hacts := two_actions_of_natural_eight_rank_one σ (H.subgroupOf P) (X.subgroupOf P)
    eH c (fun h u => hc ⟨h.val.val,h.property⟩ u) ?_ ?_ (j aX) haσ
  · apply s.false_of_two_actor_actions (s.source_fixedSpace_eq_point_of_higher_dimension hd) aX
    · intro x
      rcases hacts (j x) with h | h
      · exact Or.inl (fun u => congrArg Subtype.val (h u))
      · exact Or.inr (fun u => congrArg Subtype.val (h u))
    · exact (s.source_higher_natural_eight_rank_one hk hd ⟨e,c,hc⟩ aX haC).le
  · intro x
    apply Subtype.ext
    apply Subtype.ext
    simpa only [Subgroup.coe_pow,Subgroup.coe_one] using
      congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 X) ⟨x.val.val,x.property⟩)
  · intro x hx
    let xX : X := ⟨x.val.val,x.property⟩
    have hxC : (xX : F.TerminalHdot) ∉ centralizer (H : Set F.TerminalHdot) :=
      fun h => hx ((hfix xX).mpr h)
    exact (constituent_displacement_rank F.terminalRepresentation H X I
      s.selected.invariant s.actor_stabilizes xX).trans
      (s.source_higher_natural_eight_rank_one hk hd ⟨e,c,hc⟩ xX hxC)

/-- Complete original image recognition at higher marked multiplicity. -/
theorem imageCases_of_higher_dimension
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : 2 * Module.finrank (ZMod 2) I < Module.finrank (ZMod 2) (Additive F.Uhat)) :
    s.ImageCases := by
  obtain ⟨n,hn5,hn8,hm⟩ := s.source_higher_natural_model hk hd
  by_cases he : n = 8
  · subst n
    exact (s.not_higher_natural_eight hk hd hm).elim
  · obtain ⟨e,_,_⟩ := hm
    exact s.imageCases_of_natural_orbit_below_eight n hn5 (by omega) e

/-- The higher-multiplicity branch supplies the original local lift and
its intrinsic two-core quotient without any recognition callback. -/
theorem local_lift_of_higher_dimension
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : 2 * Module.finrank (ZMod 2) I < Module.finrank (ZMod 2) (Additive F.Uhat)) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K :=
  s.local_lift_of_image_cases (s.imageCases_of_higher_dimension hk hd)

end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
