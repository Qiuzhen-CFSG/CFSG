module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.Data.Fintype.CardEmbedding

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

/-!
# Sharp multiple transitivity of group actions

The reusable sharp-`n`-transitivity predicate used by the Mathieu group
models.  Moved here from
`KGroup.Sporadic.Mathieu.SharpTransitivity` so that other projects can
reuse the same group-action infrastructure without depending on the
sporadic-group directory.
-/

namespace Theory.GroupTheory

namespace MulAction

variable {G α : Type*} [Group G] [MulAction G α]

/-- An action is sharply `n`-transitive when every pair of ordered `n`-tuples
of distinct points is related by a unique group element. -/
public def IsSharplyMultiplyPretransitive (G α : Type*)
    [Group G] [MulAction G α] (n : ℕ) : Prop :=
  ∀ x y : Fin n ↪ α, ∃! g : G, g • x = y

/-- The defining unique transporter supplied by a sharply multiply transitive action. -/
public theorem IsSharplyMultiplyPretransitive.existsUnique_smul_eq
    {n : ℕ} (h : IsSharplyMultiplyPretransitive G α n)
    (x y : Fin n ↪ α) : ∃! g : G, g • x = y := by
  exact h x y
/-- Sharp multiple transitivity implies ordinary multiple transitivity. -/
public theorem IsSharplyMultiplyPretransitive.isMultiplyPretransitive
    {n : ℕ} (h : IsSharplyMultiplyPretransitive G α n) :
    _root_.MulAction.IsMultiplyPretransitive G α n where
  exists_smul_eq x y := (h x y).exists

/-- Every ordered tuple in a sharply transitive action gives a bijective orbit map. -/
public theorem IsSharplyMultiplyPretransitive.bijective_orbitMap
    {n : ℕ} (h : IsSharplyMultiplyPretransitive G α n) (x : Fin n ↪ α) :
    Function.Bijective (fun g : G => g • x) := by
  constructor
  · intro a b hab
    obtain ⟨g, _, hg⟩ := h x (a • x)
    exact (hg a rfl).trans (hg b hab.symm).symm
  · intro y
    exact (h x y).exists

/-- The order of a sharply multiply transitive group is the number of ordered
tuples of distinct points. The tuple hypothesis excludes the vacuous case. -/
public theorem IsSharplyMultiplyPretransitive.natCard_eq_descFactorial
    [Fintype α] {n : ℕ} (h : IsSharplyMultiplyPretransitive G α n)
    (x : Fin n ↪ α) : Nat.card G = (Fintype.card α).descFactorial n := by
  classical
  calc
    Nat.card G = Nat.card (Fin n ↪ α) :=
      Nat.card_congr (Equiv.ofBijective _ (h.bijective_orbitMap x))
    _ = (Fintype.card α).descFactorial n := by
      rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Fintype.card_fin]

/-- It suffices to prove that the orbit map at one ordered tuple is bijective. -/
public theorem isSharplyMultiplyPretransitive_of_bijective_orbitMap
    {n : ℕ} (base : Fin n ↪ α)
    (h : Function.Bijective (fun g : G => g • base)) :
    IsSharplyMultiplyPretransitive G α n := by
  intro x y
  obtain ⟨a, ha⟩ := h.surjective x
  obtain ⟨b, hb⟩ := h.surjective y
  change a • base = x at ha
  change b • base = y at hb
  refine ⟨b * a⁻¹, ?_, ?_⟩
  · rw [← ha]
    change (b * a⁻¹) • (a • base) = y
    rw [mul_smul, inv_smul_smul, hb]
  · intro g hg
    have hga : (g * a) • base = b • base := by
      rw [mul_smul, ha, hg, hb]
    have heq : g * a = b := h.injective hga
    calc
      g = (g * a) * a⁻¹ := by simp
      _ = b * a⁻¹ := by rw [heq]

end MulAction

end Theory.GroupTheory
