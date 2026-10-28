module
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CharacterCalculation.ExtensionRigidity.Injectivity.RealizationInputs
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors.Data
/-!
# Soundness of simultaneous group and module product certificates

A finite program uses only the identity, two actors and products of earlier
nodes. Induction proves that any monoid homomorphism evaluates each node to
its checked value. Thus the same program may be checked both on the genuine
three-dimensional SU matrices and on the twenty-dimensional quotient matrices.
No presentation or faithfulness hypothesis is needed.

Source application: the literal Bruhat actors of Huppert II.10.12.
-/

@[expose] public section
namespace Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.ExtensionRigidity.Injectivity.TableRealization
namespace ProductCertificate
inductive Operation where
  | one
  | actor (j : Fin 2)
  | mul (i j : Nat)
  deriving Inhabited, DecidableEq

def eval {M : Type*} [Monoid M] (a : Fin 2 → M) (ops : Array Operation) (n : Nat) : M :=
  match ops[n]! with
  | .one => 1
  | .actor j => a j
  | .mul i j => if _hi : i < n then if _hj : j < n then
      eval a ops i * eval a ops j else 1 else 1
termination_by n

def Step {M : Type*} [Monoid M] (a : Fin 2 → M) (value : Nat → M)
    (ops : Array Operation) (n : Nat) : Prop :=
  match ops[n]! with
  | .one => value n = 1
  | .actor j => value n = a j
  | .mul i j => i < n ∧ j < n ∧ value i * value j = value n

instance {M : Type*} [Monoid M] [DecidableEq M] (a : Fin 2 → M)
    (value : Nat → M) (ops : Array Operation) (n : Nat) : Decidable (Step a value ops n) := by
  unfold Step
  split <;> infer_instance

theorem map_eval {G M : Type*} [Monoid G] [Monoid M] (a : Fin 2 → G)
    (f : G →* M) (value : Nat → M) (ops : Array Operation) (N : Nat)
    (h : ∀ n : Fin N, Step (fun j => f (a j)) value ops n.val)
    (n : Nat) (hn : n < N) : f (eval a ops n) = value n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hs := h ⟨n, hn⟩
    unfold Step at hs
    rw [eval]
    split at hs <;> rename_i he
    · rw [he, map_one]; exact hs.symm
    · rw [he]; exact hs.symm
    · obtain ⟨hi, hj, hv⟩ := hs
      simp only [he]
      rw [dif_pos hi, dif_pos hj, map_mul,
        ih _ hi (hi.trans hn), ih _ hj (hj.trans hn)]
      exact hv

theorem Step.map {M N : Type*} [Monoid M] [Monoid N] (f : M →* N)
    (a : Fin 2 → M) (value : Nat → M) (ops : Array Operation) (n : Nat)
    (h : Step a value ops n) : Step (fun j => f (a j)) (fun k => f (value k)) ops n := by
  unfold Step at h ⊢
  split at h
  · exact (congrArg f h).trans (map_one f)
  · exact congrArg f h
  · exact ⟨h.1, h.2.1, by rw [← map_mul, h.2.2]⟩
end ProductCertificate
end Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.ExtensionRigidity.Injectivity.TableRealization
