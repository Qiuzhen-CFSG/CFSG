module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Statement
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairModule
public import Theory.Representation.GoldschmidtONan.Basic
public import Theory.Representation.BinaryOffender.MovedSpaceTransport

/-!
# Lifting a source quotient decomposition with an odd actor

The B.5.6 two-factor split is initially modulo the global fixed space.
An odd actor has disjoint fixed and moved spaces by averaging, so its
moved space is disjoint in the original module from the opposite factor's
moved space. This supplies the literal disjointness needed at 12.3.1, p.812,
without assuming that the whole module splits off its fixed space.
Source: Aschbacher--Smith, B.5.6(3), printed p.105.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceInduction
open QuasisimpleSource
variable {Q W : Type*} [Group Q] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) Q W}

/-- An odd actor removes the fixed-space ambiguity in the source quotient split. -/
theorem SourceTwoFactorCase.disjoint_moved_of_odd (d : SourceTwoFactorCase ρ)
    (A B : Subgroup Q) (ha : A ≤ d.first) (hb : B ≤ d.second)
    [Finite B] (ho : Odd (Nat.card B)) : Disjoint (moved ρ A) (moved ρ B) := by
  have hfirst : moved ρ A ≤ d.firstSpace.toSubmodule :=
    (show moved ρ A ≤ moved ρ d.first from Submodule.span_mono
      (by rintro _ ⟨a,ha',v,hv,rfl⟩; exact ⟨a,ha ha',v,hv,rfl⟩)).trans d.firstCase.moved_le_space
  have hsecond : moved ρ B ≤ d.secondSpace.toSubmodule :=
    (show moved ρ B ≤ moved ρ d.second from Submodule.span_mono
      (by rintro _ ⟨b,hb',v,hv,rfl⟩; exact ⟨b,hb hb',v,hv,rfl⟩)).trans d.secondCase.moved_le_space
  have hodd : Disjoint (fixedSpace ρ B) (moved ρ B) := by
    simpa only [RegularCyclicNormalClosure.displacementSpan, subspaceCommutator,
      moved, eq_comm] using
      (GoldschmidtONan.isCompl_fixed_moved_of_odd (ρ := ρ) ho).disjoint
  apply Submodule.disjoint_def.mpr
  intro v hvA hvB
  have hz : ρ.invariants.mkQ v = 0 := Submodule.disjoint_def.mp d.decomposition.disjoint _
    ⟨v,hfirst hvA,rfl⟩ ⟨v,hsecond hvB,rfl⟩
  have hfixed : v ∈ ρ.invariants := (Submodule.Quotient.mk_eq_zero _).mp hz
  exact Submodule.disjoint_def.mp hodd v (fun b => hfixed b) hvB
end CFSG.Quasithin.ChapterB.SourceInduction
