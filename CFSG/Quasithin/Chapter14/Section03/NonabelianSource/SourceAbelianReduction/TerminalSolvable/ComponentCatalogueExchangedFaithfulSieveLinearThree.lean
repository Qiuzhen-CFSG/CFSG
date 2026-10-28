module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedFaithfulAction
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedFaithfulSL3Four

/-!
# The binary linear-three exclusion on the exchanged orbit

The outer Sylow-commutator calculation used for SL₃(4) holds for every
positive binary field exponent and every perfect central cover of PSL₃.
Applying it directly to the original component orbit excludes that entire
family, including its central quotients, without a small-module classification.
The exchanging element, dotted Sylow intersection and elementary commutator
are exactly those of the original source. Transport through the faithful
constituent quotient gives the exclusion on the same H used by G.9.3,
independently of which of its components the stabilizer moves.

Source: Aschbacher--Smith G.10.9(2) and G.11.6, printed pp.360,366.
This supplies the linear-three branch of the exchanged-image sieve; the
exhaustive sieve and paired A₅ branch remain with this task's final assembly.
-/

@[expose] public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

private def centerQuotientCongr {D E : Type*} [Group D] [Group E] (e : D ≃* E) :
    D ⧸ center D ≃* E ⧸ center E :=
  QuotientGroup.congr _ _ e (by
    ext z
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact (centerCongr e ⟨y,hy⟩).property
    · intro hz
      refine ⟨((centerCongr e).symm ⟨z,hz⟩ : D),
        ((centerCongr e).symm ⟨z,hz⟩).property, ?_⟩
      exact congrArg Subtype.val ((centerCongr e).apply_symm_apply ⟨z,hz⟩))

namespace ExchangedFaithfulSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : ExchangedFaithfulSource T M Mc F g B v L I)
  {K : Type*} [Field K] [Finite K] [CharP K 2]

include s

/-- The original exchanged orbit has no binary PSL₃ central quotient, at any
positive field exponent. No module recognition or actor-rank bound is needed. -/
theorem not_binary_linear_three_central_quotient {n : ℕ} (hn : 0 < n)
    (hK : Nat.card K = 2 ^ n)
    (e : (componentOrbit L ⊤) ⧸ center (componentOrbit L ⊤) ≃* PSL(3,K)) : False := by
  let := componentOrbit_top_normal L
  let : Group.IsPerfect (componentOrbit L ⊤) := s.component.orbit_isPerfect ⊤
  obtain ⟨x,_,hxouter⟩ := s.exists_exchanging_outer
  obtain ⟨_,hXS,_⟩ := Recognition.source_terminal_actor_normal_in_point_sylow
    s.simple T s.empty s.maximal s.unique_overgroup s.many_overgroups s.seed_card
    (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
    s.normalizer_not_mem s.hypothesis
  exact Matrix.PSL3Four.OuterSylowCommutator.cyclic_commutator_frattini_ne_bot
    K hn hK (componentOrbit L ⊤) e (sylow (F := F)) x (hXS x.property)
    (elemPow_eq_one_of_isElementaryAbelian (x : F.TerminalHdot) x.property)
    hxouter (s.cyclic_sylow_commutator_frattini x)

/-- The literal constituent quotient has the same excluded central quotient.
This applies to H itself even when the moved component is not the original L. -/
theorem image_not_binary_linear_three_central_quotient {n : ℕ} (hn : 0 < n)
    (hK : Nat.card K = 2 ^ n)
    (e : (s.image (componentOrbit L ⊤)) ⧸ center (s.image (componentOrbit L ⊤)) ≃*
      PSL(3,K)) : False :=
  s.not_binary_linear_three_central_quotient hn hK
    ((centerQuotientCongr s.orbitEquiv).trans e)

/-- In particular no natural special-linear model survives on the actual H
image. The group isomorphism alone suffices, so there is no module callback. -/
theorem image_not_binary_special_linear_three {n : ℕ} (hn : 0 < n)
    (hK : Nat.card K = 2 ^ n)
    (e : s.image (componentOrbit L ⊤) ≃* SL(3,K)) : False :=
  s.image_not_binary_linear_three_central_quotient hn hK (centerQuotientCongr e)

end ExchangedFaithfulSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
