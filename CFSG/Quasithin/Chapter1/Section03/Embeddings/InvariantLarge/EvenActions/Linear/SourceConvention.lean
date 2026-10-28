module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.Linear

/-!
# The linear Cartan action with the source field convention

GLS3 Definition 2.5.13 permits a field automorphism to be an arbitrary
Aut(D)-conjugate of a coefficient action. The source input below retains
that elementwise convention and every raw A.3.15(5) clause, without choosing
common field coordinates or assuming the power-orbit conclusion.

Standard automorphism coverage and the matrix field/graph compatibility
identities show that every automorphism normalizes the inner-diagonal group.
Field/inner-diagonal separation consequently applies to these conjugate field
actions. Since B lies in D, the literal equality FBD = HBD places F in the
inner-diagonal part, forcing F = 1. This proves the coordinate premise of
the earlier raw configuration with exactly the same model and factors.
The existing alignment, inner kernel and Weyl-adjusted graph argument then
constructs the involution on the actual B/Φ(B).

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, A.3.15(5), printed
pp.50–51, and Proposition 1.3.4, printed p.511 (`refs/quasithin.pdf`);
GLS3 Definition 2.5.13(b)(1), `refs/KGroup/GLS3/chapter2.tex`.
-/

public section

open scoped MatrixGroups Pointwise
open Subgroup Matrix.PSL3.OuterSolvable
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.Linear.SourceAlignment
variable {D : Type*} [Group D] (E : Type*) [Field E] [Finite E]
/-- The full raw linear configuration, with each field element allowed its
own conjugating automorphism as in the source. The Cartan is relative to I. -/
structure SourceConfiguration (n : ℕ) (U B : Subgroup D) where
  model : D ≃* PSL(3,E)
  field_card : Nat.card E = 2 ^ n
  degree : 1 < n
  F : Subgroup (MulAut D)
  H : Subgroup (MulAut D)
  I : Subgroup (MulAut D)
  f : ℕ
  field_cyclic : IsCyclic F
  field_order : Nat.card F = f
  field_degree : f ∣ n
  field_type : ∀ a ∈ F, ∃ (c : MulAut PSL(3,E)) (σ : E ≃+* E),
    MulAut.congr model a = c * fieldAction E σ * c⁻¹
  cartan : SplitCartan I U H
  invariant : F ≤ normalizer H
  product : ∀ b ∈ B.map (MulAut.conj : D →* MulAut D),
    ∃ a ∈ F, ∃ h ∈ H, b = a * h
  product_eq : ((F : Set (MulAut D)) * (B.map (MulAut.conj : D →* MulAut D)) : Set (MulAut D)) *
      (MulAut.innerSubgroup D : Set (MulAut D)) =
    ((H : Set (MulAut D)) * (B.map (MulAut.conj : D →* MulAut D)) : Set (MulAut D)) *
      (MulAut.innerSubgroup D : Set (MulAut D))
  inner_part : I = (F ⊔ B.map (MulAut.conj : D →* MulAut D) ⊔ MulAut.innerSubgroup D) ⊓
    (innerDiagonal E).comap (MulAut.congr model).toMonoidHom
variable {E}
/-- The set-product equality and separation of conjugate field actions from
inner-diagonal actions force the source field factor to vanish when B ≤ D. -/
theorem SourceConfiguration.field_eq_bot {n : ℕ} {U B : Subgroup D}
    (c : SourceConfiguration E n U B) : c.F = ⊥ := by
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using c.field_card)
  have hcover := standard_eq_top_of_two_power_card E (by have := c.degree; omega) c.field_card
  have hi : MulAut.innerSubgroup D ≤
      (innerDiagonal E).comap (MulAut.congr c.model).toMonoidHom := by
    rintro _ ⟨x, rfl⟩
    change MulAut.congr c.model (MulAut.conj x) ∈ innerDiagonal E
    rw [MulAut.congr_conj]
    exact inner_le_innerDiagonal E ⟨_, rfl⟩
  apply le_antisymm _ bot_le
  intro a ha
  have hprod : a ∈ ((c.F : Set (MulAut D)) * B.map (MulAut.conj : D →* MulAut D)) *
      (MulAut.innerSubgroup D : Set (MulAut D)) :=
    ⟨a, ⟨a, ha, 1, one_mem _, mul_one a⟩, 1, one_mem _, mul_one a⟩
  rw [c.product_eq] at hprod
  obtain ⟨hb, ⟨h, hh, b, hb, rfl⟩, d, hd, he⟩ := hprod
  have hdiag : MulAut.congr c.model a ∈ innerDiagonal E := by
    change a ∈ (innerDiagonal E).comap (MulAut.congr c.model).toMonoidHom
    rw [← he]
    have hhI := c.cartan.inside hh
    rw [c.inner_part] at hhI
    have hbD : b ∈ MulAut.innerSubgroup D := by
      obtain ⟨x, _, rfl⟩ := hb
      exact ⟨x, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hhI.2 (hi hbD)) (hi hd)
  obtain ⟨z, σ, hz⟩ := c.field_type a ha
  have hzN : z ∈ normalizer (innerDiagonal E) :=
    standard_le_normalizer_innerDiagonal (hcover ▸ mem_top z)
  have hσ : fieldAction E σ ∈ innerDiagonal E := by
    apply (mem_normalizer_iff.mp hzN _).mpr
    rwa [hz] at hdiag
  have hσ1 : fieldAction E σ = 1 := (field_inner_disjoint E).le_bot ⟨⟨σ, rfl⟩, hσ⟩
  apply mem_bot.mpr
  apply (MulAut.congr c.model).injective
  rw [map_one, hz, hσ1, mul_one, mul_inv_cancel]
/-- The coordinate-based interface follows from the source configuration;
the model, F, H, I and every original algebraic clause are retained. -/
noncomputable def SourceConfiguration.toRawConfiguration {n : ℕ} {U B : Subgroup D}
    (c : SourceConfiguration E n U B) : RawConfiguration E n U B where
  model := c.model
  field_card := c.field_card
  degree := c.degree
  F := c.F
  H := c.H
  I := c.I
  f := c.f
  field_cyclic := c.field_cyclic
  field_order := c.field_order
  field_degree := c.field_degree
  field_action := by rw [c.field_eq_bot, Subgroup.map_bot]; exact bot_le
  cartan := c.cartan
  invariant := c.invariant
  product := c.product
  product_eq := c.product_eq
  inner_part := c.inner_part
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.Linear.SourceAlignment
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.Linear
variable (E : Type*) [Field E] [Finite E]
/-- The linear action step in Proposition 1.3.4, allowing the full source
field-automorphism convention. One actual square-one automorphism controls
all N_S(B) actions on B/Φ(B), without coverage or alignment premises. -/
theorem frattini_of_source_configuration {J : Type*} [Group J] [Finite J]
    {κ : GroupClass} {D B : Subgroup J} {S : Sylow 2 J} {p n : ℕ}
    (h : SourceAlignment.AmbientInput κ D B S p)
    (c : SourceAlignment.SourceConfiguration E n
      ((S : Subgroup J).subgroupOf D) (B.subgroupOf D)) :
    ∃ g : MulAut (B ⧸ frattini B), g ^ 2 = 1 ∧
      ∀ (s : ((S : Subgroup J) ⊓ normalizer B : Subgroup J)) (v : B ⧸ frattini B),
        frattiniConjugationAction ((S : Subgroup J) ⊓ normalizer B) B inf_le_right s v ∈
          zpowers v ∨
        frattiniConjugationAction ((S : Subgroup J) ⊓ normalizer B) B inf_le_right s v ∈
          zpowers (g v) := by
  exact frattini_of_raw_configuration E h c.toRawConfiguration
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.Linear
