module
public import Theory.Representation.BinaryOffender.InternalGenerators

/-!
# A prescribed first generator in a finite filtration

Prepend any chosen member to a finite generating family. The resulting
sequence still spans the module, so equality in the filtration bound can
be tested on that member. This gives the every-conjugate equality in
Aschbacher–Smith D.1.3(3), printed pp.174–175.
-/

public section
open Representation Representation.BinaryOffender
namespace Representation.BinaryOffender
variable {H V : Type*} [Group H] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) H V)

theorem generatingSpan_cons (W : ℕ → Subrepresentation ρ) (W₀ : Subrepresentation ρ) (n : ℕ) :
    generatingSpan ρ (fun i => match i with | 0 => W₀ | j+1 => W j) (n+1) =
      W₀ ⊔ generatingSpan ρ W n := by
  induction n with
  | zero => simp [generatingSpan]
  | succ n ih =>
    change (generatingSpan ρ (fun i => match i with | 0 => W₀ | j+1 => W j) (n+1)) ⊔ W n =
      W₀ ⊔ (generatingSpan ρ W n ⊔ W n)
    rw [ih, sup_assoc]

theorem exists_generatingSequence_start {ι : Type*} [Finite ι] [Nonempty ι]
    (W : ι → Subrepresentation ρ) (hw : ⨆ i, W i = ⊤) (i₀ : ι) :
    ∃ (n : ℕ) (a : ℕ → ι), 0 < n ∧ a 0 = i₀ ∧
      generatingSpan ρ (fun i => W (a i)) n = ⊤ := by
  obtain ⟨n,a,ha⟩ := exists_generatingSequence ρ W hw
  let b : ℕ → ι := fun i => match i with | 0 => i₀ | j+1 => a j
  refine ⟨n+1,b,Nat.succ_pos _,rfl,?_⟩
  have hb : (fun i => W (b i)) =
      (fun i => match i with | 0 => W i₀ | j+1 => W (a j)) := by
    funext i
    cases i <;> rfl
  rw [hb,generatingSpan_cons,ha,sup_top_eq]
end Representation.BinaryOffender
