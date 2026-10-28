module

public import Theory.Representation.SymplecticConjugatePair.Ambient.Basic
public import Theory.Representation.SymplecticConjugatePair.OddOrder.Binary.Automorphisms
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.OuterQuotient.ParabolicClasses
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Binary transport of a diagram-conjugate symplectic pair

Every diagram-moving automorphism is inner-field times the constructed graph
map. On the second natural summand the corresponding semilinear map is binary
linear; together with the identity on the first summand it gives an actual
intertwiner. The same map intertwines the genuine derived-group actions,
including over the two-element field. Both marked summands are preserved.

Source: Aschbacher–Smith, H.7, printed pp.388–389 of `refs/quasithin.pdf`,
combined manuscript of 1 March 2004; the automorphism input is F.1.12.
-/

@[expose] public section

open Representation Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
open Representation.OneCohomology.SymplecticFour
open Representation.BinaryOffender
namespace SymplecticConjugatePair.Ambient
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem eq_of_nonidentity_card_le_two {G : Type*} [Group G] [Finite G]
    (hc : Nat.card G ≤ 2) {a b : G} (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
  classical
  let f : Bool → G := fun x => cond x a 1
  have hf : Function.Injective f := by
    intro x y h
    cases x <;> cases y <;> simp_all [f]
  have hs := (hf.bijective_of_nat_card_le (by simpa using hc)).2
  obtain ⟨x, hx⟩ := hs b
  cases x
  · exact False.elim (hb hx.symm)
  · exact hx

theorem moving_eq_inner_field_graph (τ : MulAut (Sp F))
    (hτ : ¬ PreservesDiagram τ) :
    ∃ (g : Sp F) (σ : F ≃+* F), τ = MulAut.conj g * fieldAutomorphism σ * graphAut := by
  by_cases hF : Nat.card F = 2
  · obtain ⟨g, hg⟩ := OddOrder.Binary.binary_moving_eq_inner_graph hF τ hτ
    refine ⟨g, RingEquiv.refl F, ?_⟩
    have hi : fieldAutomorphism (RingEquiv.refl F) = 1 := by ext x i j; rfl
    simpa only [hi, mul_one] using hg
  · have hF' : 2 < Nat.card F := by
      have hc : 1 < Nat.card F := Finite.one_lt_card
      omega
    let π := parabolicClassAction hF'
    have ht : π τ ≠ 1 := fun h => hτ ((mem_parabolicClassAction_ker_iff hF' τ).mp h)
    have hg : π (graphAut (F := F)) ≠ 1 := fun h =>
      graphAut_not_preservesDiagram ((mem_parabolicClassAction_ker_iff hF' _).mp h)
    have hc : Nat.card (Equiv.Perm (parabolicClasses hF')) ≤ 2 := by
      let := Fintype.ofFinite (parabolicClasses hF')
      rw [Nat.card_eq_fintype_card, Fintype.card_perm]
      exact (Nat.factorial_le (show Fintype.card (parabolicClasses hF') ≤ 2 by
        simpa only [Nat.card_eq_fintype_card] using card_parabolicClasses_le_two hF')).trans
          (by decide)
    have he := eq_of_nonidentity_card_le_two hc ht hg
    have hp : PreservesDiagram (τ * graphAut⁻¹) := by
      apply (mem_parabolicClassAction_ker_iff hF' _).mp
      change π (τ * graphAut⁻¹) = 1
      rw [map_mul, map_inv, he, mul_inv_cancel]
    obtain ⟨g, σ, h⟩ := SemilinearClassification.inner_field_of_preservesDiagram _ hp
    exact ⟨g, σ, (mul_inv_eq_iff_eq_mul.mp h)⟩

variable [Algebra (ZMod 2) F]

noncomputable def fieldVector (σ : F ≃+* F) : Vector F ≃ₗ[ZMod 2] Vector F where
  toFun v i := σ (v i)
  invFun v i := σ.symm (v i)
  left_inv v := by ext i; exact σ.symm_apply_apply _
  right_inv v := by ext i; exact σ.apply_symm_apply _
  map_add' v w := by ext i; exact σ.map_add _ _
  map_smul' c v := by ext i; exact ZMod.map_smul σ c (v i)

noncomputable def innerFieldVector (g : Sp F) (σ : F ≃+* F) :
    Vector F ≃ₗ[ZMod 2] Vector F :=
  (fieldVector σ).trans ((LinearMap.GeneralLinearGroup.toLinearEquiv ((symplecticNatural 2).asGroupHom g)).restrictScalars (ZMod 2))

omit [Finite F] [CharP F 2] in
lemma fieldVector_intertwines (σ : F ≃+* F) (x : Sp F) (v : Vector F) :
    fieldVector σ (symplecticNatural 2 x v) =
      symplecticNatural 2 (fieldAutomorphism σ x) (fieldVector σ v) := by
  ext i
  change σ (∑ j, x.val i j * v j) = ∑ j, σ (x.val i j) * σ (v j)
  simp only [map_sum, map_mul]

omit [Finite F] [CharP F 2] in
lemma innerFieldVector_intertwines (g : Sp F) (σ : F ≃+* F)
    (x : Sp F) (v : Vector F) :
    innerFieldVector g σ (symplecticNatural 2 x v) =
      symplecticNatural 2 ((MulAut.conj g * fieldAutomorphism σ) x)
        (innerFieldVector g σ v) := by
  change symplecticNatural 2 g (fieldVector σ (symplecticNatural 2 x v)) =
    symplecticNatural 2 (g * fieldAutomorphism σ x * g⁻¹)
      (symplecticNatural 2 g (fieldVector σ v))
  rw [fieldVector_intertwines]
  simp only [← Module.End.mul_apply,
    ← map_mul, inv_mul_cancel_right]

noncomputable def pairTransport (g : Sp F) (σ : F ≃+* F) :
    Space F ≃ₗ[ZMod 2] Space F :=
  (LinearEquiv.refl (ZMod 2) (Vector F)).prodCongr (innerFieldVector g σ)

lemma pairTransport_intertwines (g : Sp F) (σ : F ≃+* F)
    (x : Sp F) (v : Space F) :
    pairTransport g σ (graphPair x v) =
      binaryPair (MulAut.conj g * fieldAutomorphism σ * graphAut) x
        (pairTransport g σ v) := by
  apply Prod.ext
  · rfl
  · exact innerFieldVector_intertwines g σ (graphAut x) v.2

theorem exists_graphPair_equiv (τ : MulAut (Sp F)) (hτ : ¬ PreservesDiagram τ) :
    ∃ E : Space F ≃ₗ[ZMod 2] Space F,
      (∀ x v, E (graphPair x v) = binaryPair τ x (E v)) ∧
      (∀ v, E v ∈ firstSummand ↔ v ∈ firstSummand) ∧
      (∀ v, E v ∈ secondSummand ↔ v ∈ secondSummand) := by
  obtain ⟨g, σ, rfl⟩ := moving_eq_inner_field_graph τ hτ
  refine ⟨pairTransport g σ, pairTransport_intertwines g σ, ?_, ?_⟩
  · intro v
    have hm (w : Space F) : w ∈ firstSummand ↔ w.2 = 0 := by
      constructor
      · rintro ⟨u, rfl⟩; rfl
      · intro h; exact ⟨w.1, Prod.ext rfl h.symm⟩
    rw [hm, hm]
    change innerFieldVector g σ v.2 = 0 ↔ v.2 = 0
    exact (innerFieldVector g σ).map_eq_zero_iff
  · intro v
    have hm (w : Space F) : w ∈ secondSummand ↔ w.1 = 0 := by
      constructor
      · rintro ⟨u, rfl⟩; rfl
      · intro h; exact ⟨w.2, Prod.ext h.symm rfl⟩
    rw [hm, hm]
    rfl

theorem exists_derivedPair_equiv (τ : MulAut (Sp F)) (hτ : ¬ PreservesDiagram τ) :
    ∃ E : Space F ≃ₗ[ZMod 2] Space F,
      (∀ x v, E (derivedPair graphAut x v) = derivedPair τ x (E v)) ∧
      (∀ v, E v ∈ firstSummand ↔ v ∈ firstSummand) ∧
      (∀ v, E v ∈ secondSummand ↔ v ∈ secondSummand) := by
  obtain ⟨E, hE, hU, hW⟩ := exists_graphPair_equiv τ hτ
  exact ⟨E, fun x v => hE x.val v, hU, hW⟩
/-- Fixed codimensions transport on every subgroup of the full matrix group. -/
theorem binaryPair_fixedCodim_eq_graphPair (τ : MulAut (Sp F))
    (hτ : ¬ PreservesDiagram τ) (A : Subgroup (Sp F)) :
    fixedCodim (binaryPair τ) A = fixedCodim (graphPair (F := F)) A := by
  obtain ⟨E, hE, _, _⟩ := exists_graphPair_equiv τ hτ
  have h := fixedCodim_map_equivariant graphPair (binaryPair τ)
    (MonoidHom.id _) E hE A
  simpa only [Subgroup.map_id] using h.symm

/-- The same transport on the genuine derived carrier, including n = 1. -/
theorem derivedPair_fixedCodim_eq_graphPair (τ : MulAut (Sp F))
    (hτ : ¬ PreservesDiagram τ) (A : Subgroup (commutator (Sp F))) :
    fixedCodim (derivedPair τ) A = fixedCodim (derivedPair graphAut) A := by
  obtain ⟨E, hE, _, _⟩ := exists_derivedPair_equiv τ hτ
  have h := fixedCodim_map_equivariant (derivedPair graphAut) (derivedPair τ)
    (MonoidHom.id _) E hE A
  simpa only [Subgroup.map_id] using h.symm

end SymplecticConjugatePair.Ambient
