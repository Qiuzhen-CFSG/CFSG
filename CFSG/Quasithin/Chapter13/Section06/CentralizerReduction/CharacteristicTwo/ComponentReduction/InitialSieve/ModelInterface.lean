module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.LocalStructure
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.ComponentStructure.Models

/-!
# Actual model and action interfaces for the initial component sieve

The earlier 1.1.5(3) contract keeps all six alternatives and their actions.
Its specialization identifies the automorphism with the actual conjugation
map on K. The field-indexed model predicate below ties every alternative
to its concrete carrier, and the proposed sieve output uses K* inside
N(K)/C(K), with the quotient comparison supplied by NormalizerAction.

These output predicates do not assert the model exclusions. They are shared
interfaces for the model sieve and residual analysis. The source application
proved here constructs only the full 1.1.5(3) alternatives and their literal
action, using that universal earlier theorem as an explicit parameter.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
1.1.5(3), printed pp.501–503; proof of 13.6.6, printed pp.926–927.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve
open Subgroup Theory.GroupTheory A5Module
open Chapter15.Section03.Candidates.ComponentStructure
open Chapter1.Section02.LocalModels ClassificationModels
universe u

/-- The full ordinary-component clause, universally quantified over its
genuine Chapter 1 local inputs, rather than over the desired sieve. -/
def Earlier115Three (κ : GroupClass.{u}) (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (_ : IsSimpleQTKE κ G) (H : Subgroup G) (P : Sylow 2 H) (M : Subgroup G) (z : G),
    Chapter1.Lemma115Hypotheses H P M z → ∀ K : Subgroup H, IsComponent H K →
      K.map H.subtype = ⁅K.map H.subtype, zpowers z⁆ ∧
        ¬ K.map H.subtype ≤ M ∧ HasModelAction115 K z

/-- The characteristic-two list, indexed by its actual defining field
exponent. Small derived groups retain exponent one; Suzuki and Ree
parameters retain the conversion to the odd field exponent. -/
inductive BinaryModelAt (Q : Type u) [Group Q] : ℕ → Prop
  | linear_two (m : ℕ) (hm : 2 ≤ m) (iso : ClassicalGroup.IsPSL Q 2 (2 ^ m)) :
      BinaryModelAt Q m
  | unitary_three (m : ℕ) (hm : 2 ≤ m) (iso : ClassicalGroup.IsPSU Q 3 (2 ^ m)) :
      BinaryModelAt Q m
  | suzuki (n : ℕ) (hn : 1 ≤ n)
      (iso : Nonempty (Q ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup n)) :
      BinaryModelAt Q (2 * n + 1)
  | linear_three (m : ℕ) (hm : 1 ≤ m) (iso : ClassicalGroup.IsPSL Q 3 (2 ^ m)) :
      BinaryModelAt Q m
  | symplectic (m : ℕ) (hm : 2 ≤ m) (iso : ClassicalGroup.IsPSp Q 2 (2 ^ m)) :
      BinaryModelAt Q m
  | g2 (m : ℕ) (hm : 2 ≤ m) (iso : IsG2At Q (2 ^ m)) : BinaryModelAt Q m
  | triality (m : ℕ) (hm : 1 ≤ m)
      (iso : Triality.Standard.IsTrialityGroupAt (2 ^ m) Q) : BinaryModelAt Q m
  | ree (n : ℕ) (hn : 1 ≤ n) (iso : IsReeF4At Q n) : BinaryModelAt Q (2 * n + 1)
  | symplectic_derived (iso : Nonempty (Q ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2)))) :
      BinaryModelAt Q 1
  | g2_derived (iso : Nonempty (Q ≃* commutator (Atlas.G2.Model (ZMod 2)))) :
      BinaryModelAt Q 1
  | tits (iso : Nonempty (Q ≃* Tits.ParrottGroup)) : BinaryModelAt Q 1
  | binary_linear (n : ℕ) (hn : n = 4 ∨ n = 5) (iso : ClassicalGroup.IsPSL Q n 2) :
      BinaryModelAt Q 1

variable {G : Type u} [Group G] [Finite G] {L V : Subgroup G}
  {κ : GroupClass.{u}} {T : Sylow 2 G} {s : Marking L V}

/-- The desired field branch is expressed on the actual component image. -/
def LargeField (K : Subgroup (Gv (markedV s)))
    (a : ActionData s (T : Subgroup G) K) : Prop :=
  ∃ m : ℕ, 1 < m ∧ BinaryModelAt (NormalizerAction.componentImage K) m ∧
    EStar s K a.a_normalizes a.z_normalizes ≤ NormalizerAction.componentImage K

/-- The source dichotomy before the block argument eliminates S₆. -/
def ModelSieveAlternatives (K : Subgroup (Gv (markedV s)))
    (a : ActionData s (T : Subgroup G) K) : Prop :=
  LargeField K a ∨ Nonempty (XStar K ≃* Equiv.Perm (Fin 6))

/-- The model automorphism is exactly the prescribed conjugation action
on K, so its inner/outer clauses concern the same quotient as E*. -/
theorem source_model_action (d : Setup κ T s) (earlier : Earlier115Three κ G)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (a : ActionData s (T : Subgroup G) K) :
    ModelAction115 K (K.normalizerMonoidHom ⟨zLocal s, a.z_normalizes⟩) := by
  obtain ⟨_, _, α, hα, hm⟩ := earlier d.ambient _ d.sylow _ _ d.local115 K hK
  have he : α = K.normalizerMonoidHom ⟨zLocal s, a.z_normalizes⟩ := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    exact hα x
  exact he ▸ hm

/-- Construct the action data and its complete earlier model alternative
together. This does not assert the later model exclusions. -/
theorem source_action_and_model (d : Setup κ T s) (hconj : EarlierConjugates κ)
    (earlier : Earlier115Three κ G) (hodd : pPrimeCore 2 (Gv (markedV s)) = ⊥)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K) :
    ∃ a : ActionData s (T : Subgroup G) K,
      ModelAction115 K (K.normalizerMonoidHom ⟨zLocal s, a.z_normalizes⟩) := by
  let a := source_action_data d hconj hodd K hK
  exact ⟨a, source_model_action d earlier K hK a⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve
