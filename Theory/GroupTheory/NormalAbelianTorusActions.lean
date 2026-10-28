module
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group
/-!
# Normal abelian torus factors and an actual quotient action

Two normal abelian subgroups make each actor in the second factor quadratic
on the first: its commutators lie in the abelian second factor. If a faithful
image of the first factor is a rigid torus for the given quotient action,
that action fixes the first factor, so their join is abelian. Inner
implementers in the same torus express the join as the product of the first
factor and the actual action kernel; a centerless quotient makes them disjoint.

This preserves the literal embeddings and conjugation action in the last
paragraph of Aschbacher--Smith 2.4.8(5), printed p.530. The rigidity hypothesis
is discharged for the source's binary PSL₂ quotients in QuadraticTorusSource.
-/
public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.NormalAbelianTorus
variable {G K : Type*} [Group G] [Group K] [Finite K]

private theorem quadratic_conjugation (D E : Subgroup G) [IsMulCommutative E]
    (hDE : D ≤ normalizer (E : Set G)) {x y : G} (hx : x ∈ D) (hy : y ∈ E) :
    y * (y * x * y⁻¹ * x⁻¹) * y⁻¹ = y * x * y⁻¹ * x⁻¹ := by
  have hz : y * x * y⁻¹ * x⁻¹ ∈ E := by
    have hi := (hDE hx y⁻¹).mp (E.inv_mem hy)
    simpa only [mul_assoc] using E.mul_mem hy hi
  have hc : y * (y * x * y⁻¹ * x⁻¹) = (y * x * y⁻¹ * x⁻¹) * y :=
    congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : E) ⟨_, hz⟩)
  rw [hc, mul_inv_cancel_right]

/-- Normal abelian factors provide the quadratic action; a faithful torus
embedding and the model's rigidity then make their actual product abelian.
Inner implementers in that same torus give the product with the action kernel. -/
theorem abelian_and_kernel_product
    (B D E : Subgroup G) (hB : D ⊔ E = B)
    (hDB : D ≤ B) (hEB : E ≤ B)
    (hBD : B ≤ normalizer (D : Set G)) (hBE : B ≤ normalizer (E : Set G))
    [IsMulCommutative D] [IsMulCommutative E]
    (ι : D →* K) (hi : Function.Injective ι) (hK : center K = ⊥) (ρ : B →* MulAut K)
    (hcompat : ∀ (b : B) (d : D),
      ρ b (ι d) = ι (D.normalizerMonoidHom ⟨b, hBD b.property⟩ d))
    (hinner : ∀ d : D, ρ ⟨d, hDB d.property⟩ = MulAut.conj (ι d))
    (hrigidity : ∀ b : B, (b : G) ∈ E →
      (ι.range.map (ρ b).toMonoidHom = ι.range) →
      (∀ x ∈ ι.range, ρ b (ρ b x * x⁻¹) = ρ b x * x⁻¹) →
      (∀ x ∈ ι.range, ρ b x = x) ∧ ∃ d ∈ ι.range, ρ b = MulAut.conj d) :
    IsMulCommutative B ∧ B = D ⊔ ρ.ker.map B.subtype ∧
      Disjoint D (ρ.ker.map B.subtype) ∧ (B : Set G) = (D : Set G) * (ρ.ker.map B.subtype : Set G) := by
  have hactor (b : B) (hb : (b : G) ∈ E) :
      (∀ x ∈ ι.range, ρ b x = x) ∧ ∃ d : D, ρ b = MulAut.conj (ι d) := by
    let a := D.normalizerMonoidHom ⟨b, hBD b.property⟩
    have hmap : ι.range.map (ρ b).toMonoidHom = ι.range := by
      apply eq_of_le_of_card_ge
      · rintro _ ⟨_, ⟨d, rfl⟩, rfl⟩
        exact ⟨a d, (hcompat b d).symm⟩
      · rw [card_map_of_injective (ρ b).injective]
    have hquad : ∀ x ∈ ι.range, ρ b (ρ b x * x⁻¹) = ρ b x * x⁻¹ := by
      rintro _ ⟨d, rfl⟩
      rw [hcompat b, ← map_inv, ← map_mul, hcompat b]
      apply congrArg ι
      apply Subtype.ext
      exact quadratic_conjugation D E (hDB.trans hBE) d.property hb
    obtain ⟨hf, d, ⟨d, rfl⟩, ha⟩ := hrigidity b hb hmap hquad
    exact ⟨hf, d, ha⟩
  have hDE : D ≤ centralizer (E : Set G) := by
    intro d hd e he
    let b : B := ⟨e, hEB he⟩
    have hh := (hactor b he).1 (ι ⟨d, hd⟩) ⟨_, rfl⟩
    rw [hcompat] at hh
    have heq : e * d * e⁻¹ = d := congrArg Subtype.val (hi hh)
    exact mul_inv_eq_iff_eq_mul.mp heq
  have hab : IsMulCommutative B := by
    rw [← hB]
    apply le_centralizer_iff_isMulCommutative.mp
    have hDD : D ≤ centralizer (D : Set G) := le_centralizer_iff_isMulCommutative.mpr inferInstance
    have hEE : E ≤ centralizer (E : Set G) := le_centralizer_iff_isMulCommutative.mpr inferInstance
    have hED : E ≤ centralizer (D : Set G) := le_centralizer_iff.mp hDE
    apply sup_le
    · intro d hd
      rw [sup_eq_closure, centralizer_closure]
      intro x hx
      exact hx.elim (hDD hd x) (hDE hd x)
    · intro e he
      rw [sup_eq_closure, centralizer_closure]
      intro x hx
      exact hx.elim (hED he x) (hEE he x)
  have hsplit : B = D ⊔ ρ.ker.map B.subtype := by
    apply le_antisymm
    · apply hB.ge.trans
      apply sup_le le_sup_left
      intro e he
      let b : B := ⟨e, hEB he⟩
      obtain ⟨d, hd⟩ := (hactor b he).2
      let dB : B := ⟨d, hDB d.property⟩
      have hk : dB⁻¹ * b ∈ ρ.ker := by
        change ρ (dB⁻¹ * b) = 1
        rw [map_mul, map_inv, hinner, hd, inv_mul_cancel]
      have hh := mul_mem_sup d.property (mem_map_of_mem B.subtype hk)
      change (d : G) * ((d : G)⁻¹ * e) ∈ D ⊔ ρ.ker.map B.subtype at hh
      simpa only [mul_inv_cancel_left] using hh
    · exact sup_le hDB (map_subtype_le _)
  have hdis : Disjoint D (ρ.ker.map B.subtype) := by
    apply disjoint_def.mpr
    intro x hx
    rintro ⟨b, hb, rfl⟩
    let d : D := ⟨b, hx⟩
    have he : MulAut.conj (ι d) = 1 := (hinner d).symm.trans hb
    have hc : ι d ∈ center K := by
      apply mem_center_iff.mpr
      intro k
      have hh := DFunLike.congr_fun he k
      change ι d * k * (ι d)⁻¹ = k at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    have hd : d = 1 := hi (by simpa only [map_one, hK, mem_bot] using hc)
    exact congrArg Subtype.val hd
  refine ⟨hab, hsplit, hdis, ?_⟩
  exact (congrArg (fun V : Subgroup G => (V : Set G)) hsplit).trans
    (coe_mul_of_right_le_normalizer_left _ _ ((map_subtype_le _).trans hBD))

end Theory.GroupTheory.NormalAbelianTorus
