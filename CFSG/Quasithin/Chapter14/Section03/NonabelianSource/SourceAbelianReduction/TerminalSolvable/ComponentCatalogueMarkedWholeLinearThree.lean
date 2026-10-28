module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedWholeRankOne
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.SelfDual

/-!
# Excluding whole marked binary SL₃ central covers

A self-dual irreducible binary SL₃ module has degree at least 8n: the actual
natural and dual actions are not self-dual, nor is the descended half-field
tensor. The original G.9 degree bound is at most 4n+2, using the automorphism
rank of the exact central quotient. Thus no such component can occur.

The source adapter retains the original constituent image, central covering
map and whole component orbit, and concludes the literal local lift.
Source: Aschbacher--Smith G.9.3(8),(17), G.11.7 and 14.3.15.
-/

@[expose] public noncomputable section
open Matrix Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.MarkedLinearThree
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition

section Small
variable {K V : Type*} [Field K] [Finite K] [CharP K 2]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- Every nontrivial self-dual binary SL₃ module has degree at least 8n.
The natural and half-field tensor alternatives are excluded on their actual
binary descended actions. -/
theorem selfDual_degree_ge_eight
    (ρ : Representation (ZMod 2) SL(3,K) V) [IsIrreducible ρ]
    (hact : ∃ g, ρ g ≠ 1) (hs : Nonempty (ρ.Equiv ρ.dual))
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card K = 2 ^ n) :
    8 * n ≤ Module.finrank (ZMod 2) V := by
  let := ZMod.algebra K 2
  obtain ⟨hpos, hmodel⟩ := AbsoluteExhaustion.absolute_model_trichotomy ρ hact n hn hcard
  rcases hmodel with ⟨hschur, _, hnatural⟩ | ⟨hnt, hdeg, hmodel⟩ | hlarge
  · have hdesc := descend_absolute_natural ρ n hcard hschur hnatural
    change Nonempty (ρ.Equiv (naturalBinary K)) ∨ Nonempty (ρ.Equiv (dualBinary K)) at hdesc
    rcases hdesc with hnat | hdual
    · obtain ⟨e⟩ := hnat
      exfalso
      apply natural_not_selfDual (k := K)
      exact selfDual_of_quasiequivalent ρ (naturalBinary K)
        ⟨MulEquiv.refl _, e.toLinearEquiv,
          fun g v => IntertwiningMap.isIntertwining ρ _ e.toIntertwiningMap g v⟩ hs
    · obtain ⟨e⟩ := hdual
      exfalso
      apply dualNatural_not_selfDual (k := K)
      exact selfDual_of_quasiequivalent ρ (dualBinary K)
        ⟨MulEquiv.refl _, e.toLinearEquiv,
          fun g v => IntertwiningMap.isIntertwining ρ _ e.toIntertwiningMap g v⟩ hs
  · exact (not_selfDual_absolute_twisted ρ (schurDegree ρ) hpos
      (by rw [←hnt]; exact hcard) rfl hmodel hs).elim
  · exact hlarge
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

/-- The original G.9 degree window excludes every self-dual binary SL₃
central quotient, retaining the original covering homomorphism. -/
theorem not_single_component_linear_three
    (h : ComponentHypothesis C ρ A L L m)
    (hs : Nonempty (Representation.Equiv (ρ.comp L.subtype)
      (Representation.dual (ρ.comp L.subtype))))
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
  have hdeg := selfDual_degree_ge_eight (τ.comp π) hnon (selfDual_comp τ π hs) n hn hcard
  have hdim := h.degree_le
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

/-- Exclude the actual whole marked SL₃ central-cover row. -/
theorem not_whole_linear_three_cover
    (hi : I=⊤) (hHL : componentOrbit L ⊤ = L)
    (π : SL(3,k) →* L) (hπ : Function.Surjective π)
    (hz : π.ker ≤ center SL(3,k))
    (n : ℕ) (hn : 0<n) (hcard : Nat.card k = 2^n) : False := by
  have hf : ActorFaithful (F := F) (g := g) (I := I) := by
    by_contra hnf
    exact s.constituent_ne_top_of_not_actorFaithful hnf hi
  have hc := s.componentHypothesis_of_actorFaithful hf
  have he := congrArg (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
    (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes) hHL
  have hs := MarkedAction.selfDual_image F.terminalRepresentation (componentOrbit L ⊤)
    (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes
    (Recognition.source_terminal_constituent_homogeneous_of_point_mem
      s.simple T s.empty s.maximal s.unique_overgroup s.many_overgroups s.seed_card
      (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
      s.normalizer_not_mem s.nonsolvable s.hypothesis s.component s.moved
      s.selected.isIrrPlus s.point_mem).2.2.1
  dsimp only at hc hs
  rw [he] at hc hs
  let R := invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I s.selected.invariant
  let eL := MarkedAction.subgroupEquiv F.terminalRepresentation (componentOrbit L ⊤)
    (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes
    (s.constituent_faithful R s.irreducible) L (le_componentOrbit L ⊤)
  exact MarkedLinearThree.not_single_component_linear_three hc hs
    (eL.toMonoidHom.comp π) (eL.surjective.comp hπ)
    (by rw [MonoidHom.ker_comp_of_injective _ _ eL.injective]; exact hz) n hn hcard

/-- Both projective and special linear whole-source carriers are impossible. -/
theorem not_whole_linear_three
    (hi : I=⊤) (hHL : componentOrbit L ⊤ = L)
    {n : ℕ} (hn : 0<n)
    (model : ClassicalGroup.IsPSL L 3 (2^n) ∨ Chapter1.Section02.LocalModels.IsSL L 3 (2^n)) : False := by
  rcases model with model | model
  · obtain ⟨k,_,_,hcard,⟨e⟩⟩ := model
    let : CharP k 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
    exact s.not_whole_linear_three_cover hi hHL
      (e.symm.toMonoidHom.comp (Matrix.PSL3.projection k))
      (e.symm.surjective.comp (Matrix.PSL3.projection_surjective k))
      (by rw [MonoidHom.ker_comp_of_injective _ _ e.symm.injective,Matrix.PSL3.projection_ker]) n hn hcard
  · obtain ⟨k,_,_,hcard,⟨e⟩⟩ := model
    let : CharP k 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
    exact s.not_whole_linear_three_cover hi hHL e.symm.toMonoidHom e.symm.surjective
      (by rw [e.symm.toMonoidHom.ker_eq_bot_iff.mpr e.symm.injective]; exact bot_le) n hn hcard

/-- The original local lift in either impossible binary linear-three row. -/
theorem local_lift_of_whole_linear_three
    (hi : I=⊤) (hHL : componentOrbit L ⊤ = L)
    {n : ℕ} (hn : 0<n)
    (model : ClassicalGroup.IsPSL L 3 (2^n) ∨ Chapter1.Section02.LocalModels.IsSL L 3 (2^n)) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K :=
  (s.not_whole_linear_three hi hHL hn model).elim
end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
