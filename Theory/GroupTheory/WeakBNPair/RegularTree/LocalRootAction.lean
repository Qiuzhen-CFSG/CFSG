module
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Tactic.Group

/-!
# Local root transitivity supplies the rank-one algebra

At a vertex `a`, fix a neighbor `b` and a second apartment neighbor `c`.
The chosen reflection fixes `a` and exchanges `b,c`. A root subgroup of
`G_a ∩ G_b` transitive on the other neighbors gives the two Borel cells in
`G_a` and the factorization `B = (B ∩ G_c) R`. The reflection normalizes
the triple stabilizer. A third neighbor gives the required thickness.

These are the local-action arguments used in DGS (3.7), pp.79–80. They do
not assume exchange or a Tits system. The group and graph may be infinite.
-/

@[expose] public section
namespace Theory.GroupTheory.WeakBNPair.RegularTree
variable {X V : Type*} [Group X] [MulAction X V]

/-- The actual root orbit and reflection at a vertex of the apartment. -/
structure LocalRootAction (Γ : SimpleGraph V) where
  a : V
  b : V
  c : V
  adj_b : Γ.Adj a b
  adj_c : Γ.Adj a c
  distinct : b ≠ c
  reflection : X
  fixes_a : reflection • a = a
  sends_b : reflection • b = c
  sends_c : reflection • c = b
  root : Subgroup X
  root_fixes : root ≤ MulAction.stabilizer X a ⊓ MulAction.stabilizer X b
  transitive : ∀ z, Γ.Adj a z → z ≠ b → ∃ r ∈ root, r • c = z
  thick : ∃ z, Γ.Adj a z ∧ z ≠ b ∧ z ≠ c

namespace LocalRootAction
variable {Γ : SimpleGraph V} (d : LocalRootAction (X := X) Γ)

abbrev endpoint : Subgroup X := MulAction.stabilizer X d.a
abbrev borel : Subgroup X := d.endpoint ⊓ MulAction.stabilizer X d.b
abbrev fixed : Subgroup X := d.borel ⊓ MulAction.stabilizer X d.c

theorem reflection_mem : d.reflection ∈ d.endpoint := d.fixes_a

theorem reflection_not_mem : d.reflection ∉ d.borel := by
  intro h
  exact d.distinct (h.2.symm.trans d.sends_b)

theorem reflection_square : d.reflection * d.reflection ∈ d.borel := by
  constructor
  · change (d.reflection * d.reflection) • d.a = d.a
    rw [mul_smul, d.fixes_a, d.fixes_a]
  · change (d.reflection * d.reflection) • d.b = d.b
    rw [mul_smul, d.sends_b, d.sends_c]

/-- The reflection interchanges the two outside vertices of the triple. -/
theorem conjugate_fixed (x : X) (hx : x ∈ d.fixed) :
    d.reflection * x * d.reflection⁻¹ ∈ d.fixed := by
  have ha : d.reflection⁻¹ • d.a = d.a := by
    simpa only [inv_smul_smul] using congrArg (d.reflection⁻¹ • ·) d.fixes_a.symm
  have hb : d.reflection⁻¹ • d.b = d.c := by
    simpa only [inv_smul_smul] using congrArg (d.reflection⁻¹ • ·) d.sends_c.symm
  have hc : d.reflection⁻¹ • d.c = d.b := by
    simpa only [inv_smul_smul] using congrArg (d.reflection⁻¹ • ·) d.sends_b.symm
  have hxa : x • d.a = d.a := hx.1.1
  have hxb : x • d.b = d.b := hx.1.2
  have hxc : x • d.c = d.c := hx.2
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · change (d.reflection * x * d.reflection⁻¹) • d.a = d.a
    rw [mul_smul, mul_smul, ha, hxa, d.fixes_a]
  · change (d.reflection * x * d.reflection⁻¹) • d.b = d.b
    rw [mul_smul, mul_smul, hb, hxc, d.sends_c]
  · change (d.reflection * x * d.reflection⁻¹) • d.c = d.c
    rw [mul_smul, mul_smul, hc, hxb, d.sends_b]

/-- Root transitivity gives the literal factorization `B = B₀ R`. -/
theorem factor
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b)) (x : X) (hx : x ∈ d.borel) :
    ∃ b₀ ∈ d.fixed, ∃ r ∈ d.root, x = b₀ * r := by
  have hxa : x⁻¹ • d.a = d.a := (d.endpoint.inv_mem hx.1)
  have hxb : x⁻¹ • d.b = d.b := (MulAction.stabilizer X d.b).inv_mem hx.2
  have hadj : Γ.Adj d.a (x⁻¹ • d.c) := by
    simpa only [hxa] using hact x⁻¹ d.adj_c
  have hne : x⁻¹ • d.c ≠ d.b := by
    intro he
    have h := (MulAction.toPerm x⁻¹).injective (he.trans hxb.symm)
    exact d.distinct h.symm
  obtain ⟨r, hr, he⟩ := d.transitive _ hadj hne
  refine ⟨x * r, ⟨d.borel.mul_mem hx (d.root_fixes hr), ?_⟩,
    r⁻¹, d.root.inv_mem hr, ?_⟩
  · change (x * r) • d.c = d.c
    rw [mul_smul, he, smul_inv_smul]
  · group

/-- The same root orbit gives the full rank-one two-cell decomposition. -/
theorem cells
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b)) (x : X) (hx : x ∈ d.endpoint) :
    x ∈ d.borel ∨ ∃ a c, a ∈ d.borel ∧ c ∈ d.borel ∧ x = a * d.reflection * c := by
  by_cases hxb : x • d.b = d.b
  · exact Or.inl ⟨hx, hxb⟩
  have hadj : Γ.Adj d.a (x • d.b) := by
    simpa only [show x • d.a = d.a from hx] using hact x d.adj_b
  obtain ⟨r, hr, he⟩ := d.transitive _ hadj hxb
  let c := (r * d.reflection)⁻¹ * x
  have hcP : c ∈ d.endpoint := d.endpoint.mul_mem
    (d.endpoint.inv_mem (d.endpoint.mul_mem (d.root_fixes hr).1 d.reflection_mem)) hx
  have hc : c ∈ d.borel := by
    refine ⟨hcP, ?_⟩
    change ((r * d.reflection)⁻¹ * x) • d.b = d.b
    have hmove : (r * d.reflection) • d.b = x • d.b := by
      rw [mul_smul, d.sends_b, he]
    rw [mul_smul, ← hmove, inv_smul_smul]
  exact Or.inr ⟨r, c, d.root_fixes hr, hc, by dsimp [c]; group⟩

/-- A third neighbor gives a coset different from `B` and `B t`.
The inverse is essential for these right-coset conventions. -/
theorem third_coset : ∃ x ∈ d.endpoint,
    x ∉ d.borel ∧ x * d.reflection⁻¹ ∉ d.borel := by
  obtain ⟨z, hz, hzb, hzc⟩ := d.thick
  obtain ⟨r, hr, he⟩ := d.transitive z hz hzb
  let x := (r * d.reflection)⁻¹
  have hx : x ∈ d.endpoint :=
    d.endpoint.inv_mem (d.endpoint.mul_mem (d.root_fixes hr).1 d.reflection_mem)
  have hmove : x⁻¹ • d.b = z := by
    dsimp [x]
    rw [inv_inv, mul_smul, d.sends_b, he]
  refine ⟨x, hx, ?_, ?_⟩
  · intro hxB
    have hfix : x⁻¹ • d.b = d.b := (MulAction.stabilizer X d.b).inv_mem hxB.2
    exact hzb (hmove.symm.trans hfix)
  · intro hxtB
    have hfix : (x * d.reflection⁻¹)⁻¹ • d.b = d.b :=
      (MulAction.stabilizer X d.b).inv_mem hxtB.2
    rw [mul_inv_rev, inv_inv, mul_smul, hmove] at hfix
    exact hzc ((MulAction.toPerm d.reflection).injective (hfix.trans d.sends_c.symm))

end LocalRootAction
end Theory.GroupTheory.WeakBNPair.RegularTree
