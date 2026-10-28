module
public import Theory.Representation.PSL3Two.ParabolicCyclic.ChiefCounts.Refinement
public import Theory.Representation.BinaryOffender.EquivariantOffender
import all Theory.Representation.ChiefCountCubic

/-!
# Cubic chief counts for binary Mathieu shadows

An order-three actor has nontrivial irreducible binary constituents of
dimension two. Fixed-space exactness makes their displacements add along a
complete invariant chief flag. Thus displacement six gives exactly three
noncentral chief factors, rather than merely an order or dimension bound.

The actual marked M22-code application supplies that displacement in
original 8.2.2(1), printed p.715 of Aschbacher--Smith. This native extension
reuses the general cubic constituent and fixed-space calculations.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open BinaryLinearThree.ParabolicCyclic.ChiefCounts
namespace MathieuCode.NormalizedShadowRows

/-- A binary action of an order-three group has one noncentral chief factor
for each two dimensions of displacement. -/
theorem cubic_count_of_fixedCodim
    {X W : Type*} [Group X] [Finite X] [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) X W) (hX : Nat.card X = 3) (n : ℕ)
    (hd : fixedCodim ρ ⊤ = 2 * n) : HasCount ρ n := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : IsCyclic X := isCyclic_of_prime_card hX
  obtain ⟨a,ha⟩ := IsCyclic.exists_generator (α := X)
  have hgen : zpowers a = ⊤ := top_unique (fun x _ => ha x)
  have ha3 : a ^ 3 = 1 := by simpa only [hX] using pow_card_eq_one' (x := a)
  obtain ⟨s,h0,h1⟩ := exists_interval_series (⊥ : Subrepresentation ρ) ⊤ bot_le
  have hc : HasCount ρ s.count := ⟨s,h0,h1,rfl⟩
  have he := Representation.ChiefCountCubic.fixed_codim_count
    (MonoidHom.id X) Function.surjective_id
    (IsPGroup.of_card (n := 0) (by simp))
    (⊤ : Subgroup X) (by simpa using hX)
    (IsPGroup.of_card (n := 0) (by simp)) ⊤ (by simp) a ha3 hgen ρ hc
  have hn : s.count = n := by omega
  exact hn ▸ hc

end MathieuCode.NormalizedShadowRows
