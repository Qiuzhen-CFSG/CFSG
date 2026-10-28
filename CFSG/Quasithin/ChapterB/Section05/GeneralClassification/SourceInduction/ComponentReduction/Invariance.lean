module

public import CFSG.Quasithin.ChapterB.Section01.IrreducibleInvariance
public import Theory.GroupTheory.CentralPChiefFactorsOddQuotient
public import Theory.Representation.BinaryOffender.Replacement

/-!
# Genuine irreducible-section invariance for the selected component

A quasisimple component is two-perfect and has central two-chief factors.
These facts, the equality L=[L,A], and the quadratic action of a minimal
best offender supply every hypothesis of the proved B.7.2(1) theorem.
Consequently A stabilizes each member of Irr⁺(L,V) setwise. This is not
pointwise fixation of its vectors.

This is the invariance input in the doubled-natural branch of B.5.9.
Source: Aschbacher–Smith, combined 1 March 2004 manuscript, printed p.108
and B.7.2(1), p.119.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)
private theorem perfect_two_residual (L : Subgroup G) [Group.IsPerfect L] :
    pResidual 2 L = ⊤ := by
  apply (pResidual_eq_top_iff 2 L).mpr
  intro N hN hq
  let : N.Normal := hN
  by_contra hne
  let : Nontrivial (L ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect (L ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let : Group.IsNilpotent (L ⧸ N) := hq.isNilpotent
  exact Group.IsPerfect.not_isSolvable (L ⧸ N) inferInstance

private theorem quasisimple_two_chief (L : Subgroup G) [IsQuasisimple L] :
    HasCentralPChiefFactors 2 L := by
  apply hasCentralTwoChiefFactors_of_odd_normal_quasisimple_quotient (⊥ : Subgroup L)
  · simp
  · exact IsQuasisimple.of_mulEquiv (QuotientGroup.quotientBot).symm

/-- B.1.5(3) on the actual moved component, using the genuine B.7.2 theorem. -/
theorem minimalOffender_stabilizes_irrPlus [Module.Finite (ZMod 2) V]
    (hf : Function.Injective ρ) {A L : Subgroup G}
    (hA : IsMinimalBestOffender ρ A) (hL : IsComponent G L)
    (hLA : ⁅L,A⁆ = L) {I : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ L I) :
    A ≤ subspaceStabilizer ρ I := by
  let : IsQuasisimple L := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  have hLne : L ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot L).mp inferInstance
  intro a ha
  apply ChapterB.source_lemma_B_7_2_1 ρ hf hA.1 hLne
    (perfect_two_residual L) hLA (quasisimple_two_chief L) ha
  · intro b hb v
    exact hA.isQuadratic ρ b hb a ha v
  · exact hI

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction
