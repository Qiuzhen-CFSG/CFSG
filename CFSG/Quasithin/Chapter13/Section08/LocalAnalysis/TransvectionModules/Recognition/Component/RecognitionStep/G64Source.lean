module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.RecognitionStep.G64Specialization

/-!
# The complete universal G.6.4 interface used by 13.8.5

The reduced specialization interface does not record the commutator identity
for each factor module, the module sum, or the 2-central refinement. Here we
retain all four source clauses and the extra transvection hypothesis, and
quantify over arbitrary finite actors, modules and SQTK covers. The adapter
supplies the reduced interface only at an actual transvection.

This module defines the allowed earlier-theorem premise; it does not assert
G.6.4. The component recognition proof constructs all its application inputs.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, G.6.1 and
G.6.4, printed pp.345–346.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.RecognitionStep
universe u
variable {A E : Type u} [Group A] [AddCommGroup E] [Module (ZMod 2) E]

/-- G.6.4(1)–(3) in the single-factor case, with the actual commutator module
and equality of the whole actor with the generated group. -/
structure G64SourceOne (ρ : Representation (ZMod 2) A E) (t : A)
    extends G64OneFactorData ρ t where
  whole_actor : K = ⊤
  commutator_module : W = subspaceCommutator ρ ⊤ K

/-- G.6.4(1)–(3) in the two-factor case. The inherited fields give the
internal direct product, the marked first factor and the involutory extension.
These fields retain the literal factor modules, their sum and cross actions,
and the permutation of the factors by every element of the whole actor. -/
structure G64SourceTwo (ρ : Representation (ZMod 2) A E) (t : A)
    extends G64TwoFactorData ρ t where
  module_sum : subspaceCommutator ρ ⊤ K1 ⊔ subspaceCommutator ρ ⊤ K2 = ⊤
  first_module : G64FactorAlternativeAt ρ K1 (subspaceCommutator ρ ⊤ K1)
  second_module : G64FactorAlternativeAt ρ K2 (subspaceCommutator ρ ⊤ K2)
  first_centralizes_second : subspaceCommutator ρ (subspaceCommutator ρ ⊤ K2) K1 = ⊥
  second_centralizes_first : subspaceCommutator ρ (subspaceCommutator ρ ⊤ K1) K2 = ⊥
  permutes_factors : ∀ a : A,
    (K1.map (MulAut.conj a).toMonoidHom = K1 ∧
      K2.map (MulAut.conj a).toMonoidHom = K2) ∨
    (K1.map (MulAut.conj a).toMonoidHom = K2 ∧
      K2.map (MulAut.conj a).toMonoidHom = K1)

/-- The 2-central restriction in G.6.4(4), including both modules for S₆. -/
def G64CentralAlternative (ρ : Representation (ZMod 2) A E) : Prop :=
  (∃ n, 2 ≤ n ∧ n ≤ 5 ∧ HasActionModel ρ (linearRepresentation n)) ∨
  HasActionModel ρ (BinaryPermutation.naturalRepresentation (Fin 6)) ∨
  HasActionModel ρ (BinaryPermutation.naturalRepresentation (Fin 7)) ∨
  HasActionModel ρ (BinaryPermutation.coreRepresentation (Fin 6))

/-- All four source clauses, with no recognized-component premise. -/
def G64SourceConclusion (ρ : Representation (ZMod 2) A E) (t : A) : Prop :=
  (Nonempty (G64SourceOne ρ t) ∨ Nonempty (G64SourceTwo ρ t)) ∧
  (∀ T : Sylow 2 A, t ∈ (center T).map (T : Subgroup A).subtype →
    normalClosure ({t} : Set A) = ⊤ ∧ G64CentralAlternative ρ)

/-- The earlier universal theorem G.6.4, on finite binary modules. Every
G.6.1 hypothesis is explicit, as is the additional transvection hypothesis.
This is an input proposition, not an axiom or a proof of that earlier theorem. -/
def G64SourceTheorem (κ : GroupClass.{u}) : Prop :=
  ∀ {A E Cover : Type u} [Group A] [Finite A]
    [AddCommGroup E] [Module (ZMod 2) E] [Finite E]
    [Group Cover] [Finite Cover],
    (ρ : Representation (ZMod 2) A E) → (t : A) →
    (q : Cover →* A) → IsSQTK κ Cover → Function.Surjective q →
    pCore 2 A = ⊥ → Function.Injective ρ → t ^ 2 = 1 → t ≠ 1 →
    Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) ≤ 2 →
    displacementOrbit ρ t = ⊤ → IsTransvection ρ t → G64SourceConclusion ρ t

/-- Feed the exact universal statement to the previously proved specialization.
The marked transvection supplies the extra hypothesis absent from its reduced
application interface; no specialized classification statement is assumed. -/
theorem g64Universal_of_source {κ : GroupClass.{u}} [Finite A] [Finite E]
    (hG64 : G64SourceTheorem κ) (ρ : Representation (ZMod 2) A E)
    (t : A) (ht : IsTransvection ρ t) : G64Universal κ ρ t := by
  intro Cover _ _ q hcover hq hcore hf ht2 ht1 hrank hgen
  have hc := hG64 ρ t q hcover hq hcore hf ht2 ht1 hrank hgen ht
  change G64SourceConclusion ρ t at hc
  rcases hc with ⟨hd, _⟩
  rcases hd with hd | hd
  · obtain ⟨d⟩ := hd
    exact Or.inl ⟨d.toG64OneFactorData⟩
  · obtain ⟨d⟩ := hd
    exact Or.inr ⟨d.toG64TwoFactorData⟩
end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.RecognitionStep

end
