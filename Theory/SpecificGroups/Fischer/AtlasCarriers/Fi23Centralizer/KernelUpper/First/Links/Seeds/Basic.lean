module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Links.Data
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Representatives

/-!
# Soundness of shared seed programs for the first Fi23 stabilizer

Each node describes a generator, inverse, or product. A table is certified
locally, using only tables at earlier nodes. Strong induction then realizes
every table by an element of the unchanged first auxiliary subgroup. Inverse
nodes need only one inverse equation against the already realized permutation.
No expanded word, group order, or subgroup normality is used.

The concrete program comes from `Links/source/seed-nodes.json`, with left-action
composition. Its local equations and its eleven output comparisons are separate
finite proof obligations. Source: ATLAS F23G1-p31671B0, GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Links.Seeds

inductive Instruction where
  | generator (i : Fin 2)
  | inverse (i : Nat)
  | product (i j : Nat)

/-- The dependency order that makes induction on the shared program sound. -/
def Earlier (k : Nat) : Instruction → Prop
  | .generator _ => True
  | .inverse i => i < k
  | .product i j => i < k ∧ j < k

instance (k : Nat) (s : Instruction) : Decidable (Earlier k s) := by
  cases s <;> unfold Earlier <;> infer_instance

/-- One local table equation. Products use Lean's left-action order. -/
def Equation (table : Nat → Fin 31671 → Fin 31671) (k : Nat) : Instruction → Prop
  | .generator i => ∀ x, table k x = KernelUpperData.firstGenerator i x
  | .inverse i => ∀ x, table i (table k x) = x
  | .product i j => ∀ x, table k x = table i (table j x)

/-- A table is the actual action of an element in the specified subgroup. -/
def Realized (f : Fin 31671 → Fin 31671) : Prop :=
  ∃ g : Equiv.Perm (Fin 31671), g ∈ KernelUpperData.first ∧ ∀ x, g x = f x

theorem realized_step (table : Nat → Fin 31671 → Fin 31671)
    (k : Nat) (s : Instruction) (he : Earlier k s) (hs : Equation table k s)
    (ih : ∀ j, j < k → Realized (table j)) : Realized (table k) := by
  cases s with
  | generator i =>
    exact ⟨KernelUpperData.firstGenerator i, Subgroup.subset_closure ⟨i, rfl⟩,
      fun x => (hs x).symm⟩
  | inverse i =>
    obtain ⟨g, hg, hgf⟩ := ih i he
    refine ⟨g⁻¹, KernelUpperData.first.inv_mem hg, ?_⟩
    intro x
    apply g.injective
    change g (g.symm x) = g (table k x)
    rw [g.apply_symm_apply, hgf, hs x]
  | product i j =>
    obtain ⟨g, hg, hgf⟩ := ih i he.1
    obtain ⟨h, hh, hhf⟩ := ih j he.2
    refine ⟨g * h, KernelUpperData.first.mul_mem hg hh, ?_⟩
    intro x
    change g (h x) = table k x
    rw [hhf, hgf, hs x]

/-- Local equations, not a computation oracle, certify every shared node. -/
theorem realized_of_equations (n : Nat) (program : Nat → Instruction)
    (table : Nat → Fin 31671 → Fin 31671)
    (horder : ∀ k, k < n → Earlier k (program k))
    (hsteps : ∀ k, k < n → Equation table k (program k))
    (k : Nat) (hk : k < n) : Realized (table k) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    apply realized_step table k (program k) (horder k hk) (hsteps k hk)
    intro j hj
    exact ih j hj (Nat.lt_trans hj hk)

theorem mem_of_realized {f : Fin 31671 → Fin 31671}
    (hf : Realized f) (g : Equiv.Perm (Fin 31671)) (hg : ∀ x, f x = g x) :
    g ∈ KernelUpperData.first := by
  obtain ⟨p, hp, hpf⟩ := hf
  have he : p = g := Equiv.ext (fun x => (hpf x).trans (hg x))
  exact he ▸ hp

end Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Links.Seeds
