module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogue
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.SourceNonsolvable.ExchangedCompletion
public import Theory.ElementaryAbelian.GeneratorRank
public import Theory.ElementaryAbelian.Injective

/-!
# Rank of the exchanged constituent stabilizer

For the original terminal action, the subgroup `Y = N_X(I)` has index two
in the elementary abelian actor. The exchanged summands have equal dimension
and zero intersection, so G.10.2 bounds the degree of `I` by `m(Y) + 2`.
This argument does not use the non-GL assertion G.10.15(3).

In the small-actor case the bound is an equality once G.10.15(3) supplies
spanning through the existing exchanged-completion theorem. That assertion
is an explicit premise of the equality result, not a conclusion of this module.
Both statements are applied to the original flag and literal dotted actor.

Source: Aschbacher--Smith G.10.15(1)(ii), G.11.6 and 14.3.12, printed
pp.361--362,366,993.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable

private instance binary_subgroup {D : Type*} [Group D] [IsElementaryAbelian 2 D]
    (Y : Subgroup D) : IsElementaryAbelian 2 Y :=
  IsElementaryAbelian.of_injective Y.subtype Y.subtype_injective

private theorem binary_card (A : Type*) [Group A] [Finite A]
    [IsElementaryAbelian 2 A] :
    Nat.card A = 2 ^ finrank (ZMod 2) (Additive A) := by
  rw [Nat.card_congr Additive.ofMul]
  simpa only [Nat.card_zmod] using
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)

private theorem index_two_rank {D : Type*} [Group D] [Finite D]
    [IsElementaryAbelian 2 D] (Y : Subgroup D) (hY : Y.index = 2) :
    finrank (ZMod 2) (Additive Y) + 1 = finrank (ZMod 2) (Additive D) := by
  have hc := Y.card_mul_index
  rw [hY, binary_card Y, binary_card D, ← pow_succ] at hc
  exact (Nat.pow_right_injective (by decide : 2 ≤ 2)) hc

private theorem pair_dimension {D E : Type*} [Group D] [AddCommGroup E]
    [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
    (ρ : Representation (ZMod 2) D E) (I : Submodule (ZMod 2) E) (x : D)
    (hd : Disjoint I (I.map (ρ x))) :
    finrank (ZMod 2) (I ⊔ I.map (ρ x) : Submodule (ZMod 2) E) =
      2 * finrank (ZMod 2) I := by
  have hi : Function.Injective (ρ x) :=
    (LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom x)).injective
  have hm := (Submodule.equivMapOfInjective (ρ x) hi I).finrank_eq
  have hs := Submodule.finrank_sup_add_finrank_inf_eq I (I.map (ρ x))
  rw [hd.eq_bot, finrank_bot, add_zero, ← hm] at hs
  omega

private theorem exchanged_degree {D E : Type*} [Group D] [Finite D]
    [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
    {ρ : Representation (ZMod 2) D E} {B : LinearMap.BilinForm (ZMod 2) E}
    {v : E} {W I : Submodule (ZMod 2) E} {X : Subgroup D}
    [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
    (hyp : ChapterG.Section10.Hypothesis ρ B v W X X₀)
    (hg : ChapterG.Section10.ExchangedConstituentGeometry ρ B v W X I) :
    let Y := (subspaceStabilizer ρ I).subgroupOf X
    finrank (ZMod 2) (Additive Y) + 1 = finrank (ZMod 2) (Additive X) ∧
    finrank (ZMod 2) I ≤ finrank (ZMod 2) (Additive Y) + 2 := by
  obtain ⟨x, _, _, hd, hindex, _⟩ := hg
  have hr := index_two_rank ((subspaceStabilizer ρ I).subgroupOf X) hindex
  have hp := pair_dimension ρ I x hd
  have hle := (I ⊔ I.map (ρ x)).finrank_le
  have hq := (Group.rank_le_of_surjective (QuotientGroup.mk' X₀)
    (QuotientGroup.mk'_surjective X₀)).trans (IsElementaryAbelian.rank_le_finrank (p:=2) X)
  have hb := hyp.dimension_bound.1
  exact ⟨hr, by omega⟩

open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The source exchanged stabilizer has codimension one in X and its rank
bounds the degree of the original constituent. This needs no non-GL premise. -/
theorem source_exchanged_stabilizer_degree
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G)
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hn : ¬ Group.IsSolvable F.TerminalHdot)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    {L : Subgroup F.TerminalHdot} (hL : IsComponent F.TerminalHdot L)
    (hm : ⁅L,F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation
      (componentOrbit L ⊤) (F.terminalDot (F.X g)) I)
    (hv : v ∉ I)
    : let Y := (subspaceStabilizer F.terminalRepresentation I).subgroupOf
        (F.terminalDot (F.X g))
      letI : IsElementaryAbelian 2 Y :=
        IsElementaryAbelian.of_injective Y.subtype Y.subtype_injective
      finrank (ZMod 2) (Additive Y) + 1 =
        finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ∧
      finrank (ZMod 2) I ≤ finrank (ZMod 2) (Additive Y) + 2 := by
  let S : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  obtain ⟨_,hXP,hN⟩ := Recognition.source_terminal_actor_normal_in_point_sylow
    hG T hempty hM hu hmany hcard e F hne g hgP hgH hyp
  exact exchanged_degree hyp (hyp.exchanged_constituent_geometry hn hL hm S
    ((normal_subgroupOf_iff_le_normalizer hXP).mp hN)
    (Recognition.terminal_component_normalizer_index_le_two hG F (by decide) L hL) hI hv)

/-- In the small-actor source branch, the degree is exactly two more than
the stabilizer rank once the actual non-GL assertion supplies orbit spanning. -/
theorem source_exchanged_stabilizer_degree_eq
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G)
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hn : ¬ Group.IsSolvable F.TerminalHdot)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    {L : Subgroup F.TerminalHdot} (hL : IsComponent F.TerminalHdot L)
    (hm : ⁅L,F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation
      (componentOrbit L ⊤) (F.terminalDot (F.X g)) I)
    (hv : v ∉ I)
    (hproper : ¬ Function.Surjective
      (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
        hI.invariant).toRepresentation.asGroupHom)
    (hsmall : finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤
      finrank (ZMod 2) (Additive F.Uhat) / 2 - 1) :
    let Y := (subspaceStabilizer F.terminalRepresentation I).subgroupOf
      (F.terminalDot (F.X g))
    letI : IsElementaryAbelian 2 Y :=
      IsElementaryAbelian.of_injective Y.subtype Y.subtype_injective
    finrank (ZMod 2) I = finrank (ZMod 2) (Additive Y) + 2 := by
  obtain ⟨hgeo,hspan,_,_⟩ := Recognition.source_terminal_exchanged_constituent_completion
    hG T hempty hM hu hmany hcard e F hne g hgP hgH hn hyp hL hm hI hv hproper
  obtain ⟨x,_,hpair,hdis,hidx,_⟩ := hgeo
  have hdim := pair_dimension F.terminalRepresentation I x hdis
  rw [← hpair,hspan,finrank_top] at hdim
  have hr := index_two_rank
    ((subspaceStabilizer F.terminalRepresentation I).subgroupOf (F.terminalDot (F.X g))) hidx
  have he := (hyp.numerical_equality_of_actor_dimension_le hsmall).2.1
  let : Group.IsPerfect (componentOrbit L ⊤) := hL.orbit_isPerfect ⊤
  have hd := hI.isIrrPlus.finrank_gt_two F.terminalRepresentation (componentOrbit L ⊤)
  dsimp only
  omega

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
