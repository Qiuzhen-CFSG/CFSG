module
public import Theory.Representation.BinaryOffender.MinimalPlane
public import Theory.Representation.BinaryOffender.CommutatorDisplacement
public import CFSG.Quasithin.ChapterB.Section01.IrreducibleSections

/-!
# A component moved by a minimal plane offender has one irreducible central section

Choose an Irr⁺ section for the faithful perfect component. B.1.5(3) makes it
invariant under the actual minimal offender. Its noncentral action and the
plane bound put every offender displacement inside the section. The identity
[K,A]=K then kills K on the quotient, so the section is all of [V,K]. This
proves the original13.7.15(2) without a classification or model premise.

Source: Aschbacher–Smith B.1.5(3), B.1.11 and13.7.15(2), pp.69,72,943–944.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Every actual Irr⁺ section is the whole component moved space in the plane case. -/
theorem irrPlus_eq_moved_of_minimal_plane (hf : Function.Injective ρ)
    {K A : Subgroup G} [IsQuasisimple K] (hA : IsMinimalBestOffender ρ A)
    (hKA : ⁅K,A⁆ = K)
    (hd : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) ≤ 2)
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ K I) :
    I = subspaceCommutator ρ ⊤ K := by
  have hr : pResidual 2 K = ⊤ := by
    apply (pResidual_eq_top_iff 2 K).mpr
    intro N hN hp
    let := hN
    have hsub : Subsingleton (K ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent (K ⧸ N) hp.isNilpotent
    apply top_unique
    intro k _
    exact (QuotientGroup.eq_one_iff k).mp (Subsingleton.elim _ _)
  have hc : HasCentralPChiefFactors 2 K :=
    hasCentralTwoChiefFactors_of_odd_normal_quasisimple_quotient
      (⊥ : Subgroup K) (by simp) (IsQuasisimple.of_mulEquiv QuotientGroup.quotientBot.symm)
  have hs := source_lemma_B_1_5_3 ρ hf hA hr hKA hc hI
  have hn : ¬ I ≤ fixedSpace ρ A := by
    intro hi
    have hh := le_fixedSpace_commutator_of_invariant ρ hI.choose hi
    rw [hKA] at hh
    exact hI.not_le_fixedSpace ρ hh
  have hm := hA.moved_le_of_plane ρ hd I hs hn
  exact le_antisymm
    (hI.choose_spec.1.ge.trans (subspaceCommutator_mono_left ρ le_top K))
    (subspaceCommutator_le_of_commutator_displacement ρ hKA hI.choose hs hm)

/-- Original13.7.15(2): the full component moved module belongs to Irr⁺. -/
theorem component_irrPlus_of_minimal_plane (hf : Function.Injective ρ)
    {K A : Subgroup G} [IsQuasisimple K] (hA : IsMinimalBestOffender ρ A)
    (hKA : ⁅K,A⁆ = K)
    (hd : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) ≤ 2) :
    IsIrrPlus ρ K (subspaceCommutator ρ ⊤ K) := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  obtain ⟨I,hI⟩ := exists_isIrrPlus_of_faithful ρ hf K
    ((Subgroup.nontrivial_iff_ne_bot K).mp inferInstance)
  rwa [irrPlus_eq_moved_of_minimal_plane ρ hf hA hKA hd hI] at hI
end CFSG.Quasithin.ChapterB
