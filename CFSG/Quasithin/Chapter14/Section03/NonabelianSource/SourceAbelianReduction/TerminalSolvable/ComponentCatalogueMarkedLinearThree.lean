module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedLinearThreeDuality
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedRankOne
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.AbsoluteExhaustion
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.FieldDescent
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.CentralRank
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.SourceBound

/-!
# Excluding the two-copy SL₃ central-cover row

The original actor image has rank dim(I)-2. Conjugation embeds this actor
in the automorphism group of its faithful irreducible component, whose
rank is at most 2n for every central quotient of SL₃(2ⁿ). The exhaustive
binary SL₃ alternatives have degree exceeding 2n+2 when self-dual: the
natural and dual-natural actions are excluded by their invariant forms,
and the tensor and remaining alternatives exceed the degree bound.

The source application uses the literal constituent quotient, actual
central covering map and equality with the whole component orbit. Its
local component-lift consumer retains every original ambient hypothesis.
Source: Aschbacher–Smith G.9.3(8),(17), G.11.8 and original 14.3.15,
printed pp.354–357,368–369,994.
-/

@[expose] public noncomputable section
open Matrix Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.MarkedLinearThree
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition

section Small
variable {K V : Type*} [Field K] [Finite K] [CharP K 2]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- Nontrivial self-dual binary SL₃ modules exceed the actual two-copy degree
window. Both absolute natural alternatives are excluded on their descended
binary actions; the tensor and remaining alternatives exceed the window. -/
theorem selfDual_degree_gt
    (ρ : Representation (ZMod 2) SL(3,K) V) [IsIrreducible ρ]
    (hact : ∃ g, ρ g ≠ 1) (hs : Nonempty (ρ.Equiv ρ.dual))
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card K = 2 ^ n) :
    2 * n + 2 < Module.finrank (ZMod 2) V := by
  by_contra! hsmall
  let := ZMod.algebra K 2
  obtain ⟨hpos, hmodel⟩ := AbsoluteExhaustion.absolute_model_trichotomy ρ hact n hn hcard
  rcases hmodel with ⟨hschur, _, hnatural⟩ | ⟨hnt, hdeg, _⟩ | hlarge
  · have hdesc := descend_absolute_natural ρ n hcard hschur hnatural
    change Nonempty (ρ.Equiv (naturalBinary K)) ∨ Nonempty (ρ.Equiv (dualBinary K)) at hdesc
    rcases hdesc with hnat | hdual
    · obtain ⟨e⟩ := hnat
      apply natural_not_selfDual (k := K)
      exact selfDual_of_quasiequivalent ρ (naturalBinary K)
        ⟨MulEquiv.refl _, e.toLinearEquiv,
          fun g v => IntertwiningMap.isIntertwining ρ _ e.toIntertwiningMap g v⟩ hs
    · obtain ⟨e⟩ := hdual
      apply dualNatural_not_selfDual (k := K)
      exact selfDual_of_quasiequivalent ρ (dualBinary K)
        ⟨MulEquiv.refl _, e.toLinearEquiv,
          fun g v => IntertwiningMap.isIntertwining ρ _ e.toIntertwiningMap g v⟩ hs
  · omega
  · omega
end Small

section Component
universe u w
variable {D : Type u} [Group D] [Finite D]
  {V : Type w} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {C : GroupClass.{u}} {ρ : Representation (ZMod 2) D V}
  {A L : Subgroup D} {m : ℕ}
  {K : Type*} [Field K] [Finite K] [CharP K 2]
open Theory.GroupTheory Subgroup ChapterG.Section09

/-- The single-component two-copy window excludes every actual central
quotient of binary SL₃. The original covering homomorphism is retained. -/
theorem not_two_copy_linear_three
    (h : ComponentHypothesis C ρ A L L m)
    (hs : Nonempty (Representation.Equiv (ρ.comp L.subtype)
      (Representation.dual (ρ.comp L.subtype))))
    (hd : Module.finrank (ZMod 2) V ≤ m + 2)
    (π : SL(3,K) →* L) (hπ : Function.Surjective π)
    (hcentral : π.ker ≤ center SL(3,K))
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card K = 2 ^ n) : False := by
  let τ := ρ.comp L.subtype
  let : IsIrreducible τ := h.irreducible
  let : Nontrivial L := L.nontrivial_iff_ne_bot.mpr (by
    intro hL
    exact h.noncentral (by rw [hL, commutator_bot_left]))
  let : IsIrreducible (τ.comp π) :=
    (irreducible_comp_surjective_iff π hπ τ).mpr inferInstance
  have hnon : ∃ g, (τ.comp π) g ≠ 1 := by
    obtain ⟨x, hx⟩ := exists_ne (1 : L)
    obtain ⟨g, rfl⟩ := hπ x
    refine ⟨g, fun hg => hx ((h.faithful.comp L.subtype_injective) ?_)⟩
    exact hg.trans τ.map_one.symm
  have hm := h.toSetup.rank_le_automorphisms (L := L) (by
    rw [normalizer_eq_top_iff.mpr h.normal_H]
    exact le_top)
  have hr := central_quotient_automorphism_rank_le π hπ hcentral
  rw [Matrix.PSL3Even.automorphism_two_rank_eq K hn hcard] at hr
  have hdeg := selfDual_degree_gt (τ.comp π) hnon (selfDual_comp τ π hs) n hn hcard
  omega
end Component

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.MarkedLinearThree

namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Subgroup Representation.BinaryOffender Theory.GroupTheory
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
namespace MarkedSource
variable {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : MarkedSource T M Mc F g B v L I)
  {k : Type*} [Field k] [Finite k] [CharP k 2]
include s

/-- The full binary SL₃ central-cover row is impossible in the original
marked two-copy source, with the same I, actor image and whole component orbit. -/
theorem not_double_dimension_linear_three_cover
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    (hHL : componentOrbit L ⊤ = L)
    (π : SL(3,k) →* MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L)
    (hπ : Function.Surjective π) (hcentral : π.ker ≤ center SL(3,k))
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card k = 2 ^ n) : False := by
  have hc := s.singleOrbit_componentHypothesis_of_double_dimension hk hd hHL
  have he : MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes (componentOrbit L ⊤) =
    MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L :=
    congrArg (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes) hHL
  let H := componentOrbit L ⊤
  let X := F.terminalDot (F.X g)
  let σ := MarkedAction.action F.terminalRepresentation H X I
    s.selected.invariant s.actor_stabilizes
  let Hbar := MarkedAction.image F.terminalRepresentation H X I
    s.selected.invariant s.actor_stabilizes H
  have hsource := (Recognition.source_terminal_constituent_homogeneous_of_point_mem
    s.simple T s.empty s.maximal s.unique_overgroup s.many_overgroups s.seed_card
    (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
    s.normalizer_not_mem s.nonsolvable s.hypothesis s.component s.moved
    s.selected.isIrrPlus s.point_mem).2.2.1
  have hdual : Nonempty (Representation.Equiv ((kerRepresentation σ).comp Hbar.subtype)
      (Representation.dual ((kerRepresentation σ).comp Hbar.subtype))) :=
    MarkedAction.selfDual_image F.terminalRepresentation H X I
      s.selected.invariant s.actor_stabilizes hsource
  dsimp only at hc
  change Nonempty (Representation.Equiv ((kerRepresentation σ).comp
      (MarkedAction.image F.terminalRepresentation H X I s.selected.invariant s.actor_stabilizes H).subtype)
    (Representation.dual ((kerRepresentation σ).comp
      (MarkedAction.image F.terminalRepresentation H X I s.selected.invariant s.actor_stabilizes H).subtype))) at hdual
  rw [he] at hc hdual
  apply MarkedLinearThree.not_two_copy_linear_three hc hdual _ π hπ hcentral n hn hcard
  have hi := s.dimension_gt_two
  omega

/-- The literal local component-lift consumer closes the excluded SL₃ row. -/
theorem local_lift_of_double_dimension_linear_three_cover
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    (hHL : componentOrbit L ⊤ = L)
    (π : SL(3,k) →* MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L)
    (hπ : Function.Surjective π) (hcentral : π.ker ≤ center SL(3,k))
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card k = 2 ^ n) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K :=
  (s.not_double_dimension_linear_three_cover hk hd hHL π hπ hcentral n hn hcard).elim

end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
