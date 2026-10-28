module

public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.E8.Operators.Coordinates.Membership

/-!
# Explicit E8 completeness witnesses

Finite integer certificates for the native E8 root catalogue (GLS3 §2.6).
-/

@[expose] public section
open Theory.AlgebraicGroup.StandardRootSystem
namespace Theory.SpecificGroups.LieType.SourceLevi.E8.Operators.Coordinates.Certificates

private instance (ε : Fin 8 → Bool) : Decidable (evenNegative ε) :=
  inferInstanceAs (Decidable (Even ((Finset.univ.filter fun i => !(ε i)).card)))

private def pairNumber (i j : Fin 8) (a b : Bool) : ℕ :=
  4 * (i.val * (15 - i.val) / 2 + j.val - i.val - 1) +
    (if a then 2 else 0) + (if b then 1 else 0)
private def pairIndex (i j : Fin 8) (a b : Bool) : Fin 240 :=
  ⟨(if i < j then pairNumber i j a b else pairNumber j i b a) % 240, Nat.mod_lt _ (by decide)⟩
theorem pair_complete : ∀ (i j : Fin 8) (a b : Bool),
    i ≠ j → ∃ r, coord r = pair i j a b := by
  have h : ∀ (i j : Fin 8) (a b : Bool), i ≠ j →
      coord (pairIndex i j a b) = pair i j a b := by decide +kernel
  intro i j a b hij
  exact ⟨_, h i j a b hij⟩

private def halfIndex (ε : Fin 8 → Bool) : Fin 240 :=
  ⟨(112 + ∑ q : Fin 7, if ε q.castSucc then 2 ^ (6 - q.val) else 0) % 240,
    Nat.mod_lt _ (by decide)⟩
theorem half_complete : ∀ ε : Fin 8 → Bool,
    evenNegative ε → ∃ r, coord r = half ε := by
  have h : ∀ ε : Fin 8 → Bool, evenNegative ε →
      coord (halfIndex ε) = half ε := by decide +kernel
  intro ε hε
  exact ⟨_, h ε hε⟩


end Theory.SpecificGroups.LieType.SourceLevi.E8.Operators.Coordinates.Certificates
