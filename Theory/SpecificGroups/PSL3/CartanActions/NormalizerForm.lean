module

public import Theory.SpecificGroups.PSL3.CartanActions.NormalizerForm.BorelKernel

/-!
# Factoring standard PSL₃ automorphisms

The field subgroup normalizes the inner-diagonal subgroup. Inverse transpose
normalizes their product, so every element of the generated standard subgroup
has a single linear–field–graph factorization. Coordinate reversal replaces
inverse transpose by the graph representative preserving the upper unipotent
subgroup. The imported matrix kernel will remove the remaining linear factor
on any torus subgroup preserved by the actor.

The three matrix compatibility identities are explicit inputs, to be supplied
by the standard outer automorphism development. No coverage of all
automorphisms, Borel kernel, or stability of a chosen torus subgroup is assumed.
Source: GLS3, §2.7, `refs/KGroup/GLS3/chapter2.tex`, and Aschbacher–Smith,
`refs/quasithin.pdf`, printed p.511 and A.3.15(5), printed pp.50–51.
-/

public section

open scoped MatrixGroups
open Matrix Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.OuterSolvable.OddPrimeCoverage
namespace Matrix.PSL3.CartanActions.NormalizerForm
variable (F : Type*) [Field F]

private theorem mem_normalizer_of_conjugates {G : Type*} [Group G]
    (H : Subgroup G) (a : G)
    (hf : ∀ x ∈ H, a * x * a⁻¹ ∈ H)
    (hb : ∀ x ∈ H, a⁻¹ * x * a ∈ H) : a ∈ Subgroup.normalizer H := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hf x, fun hx => ?_⟩
  simpa [mul_assoc] using hb _ hx

private theorem one_or_generator_of_sq {G : Type*} [Group G]
    (g : G) (hg : g ^ 2 = 1) {x : G} (hx : x ∈ Subgroup.zpowers g) :
    x = 1 ∨ x = g := by
  have hg' : g * g = 1 := by simpa only [pow_two] using hg
  have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_left hg'
  let H : Subgroup G :=
    { carrier := {x | x = 1 ∨ x = g}
      one_mem' := Or.inl rfl
      mul_mem' := by
        rintro a b (rfl | rfl) (rfl | rfl) <;> simp [hg']
      inv_mem' := by
        rintro a (rfl | rfl) <;> simp [hgi] }
  exact (Subgroup.zpowers_le.mpr (show g ∈ H from Or.inr rfl)) hx

/-- Standard elements have a single linear–field–graph factorization. The
three displayed matrix compatibility laws are the only external inputs. -/
theorem standard_factorization
    (hfield : ∀ (σ : F ≃+* F) (m : GL (Fin 3) F),
      fieldAction F σ * linearConj F m =
        linearConj F (GeneralLinearGroup.map σ.toRingHom m) * fieldAction F σ)
    (hgraph : ∀ m : GL (Fin 3) F, ∃ m' : GL (Fin 3) F,
      graph F * linearConj F m = linearConj F m' * graph F)
    (hcomm : ∀ σ : F ≃+* F, Commute (fieldAction F σ) (graph F))
    (α : MulAut PSL(3,F)) (hα : α ∈ standard F) :
    ∃ (m : GL (Fin 3) F) (σ : F ≃+* F),
      α = linearConj F m * fieldAction F σ ∨
      α = linearConj F m * fieldAction F σ * graph F := by
  have hfn : (fieldAction F).range ≤ Subgroup.normalizer (innerDiagonal F) := by
    rintro _ ⟨σ,rfl⟩
    apply mem_normalizer_of_conjugates
    · rintro _ ⟨m,rfl⟩
      refine ⟨GeneralLinearGroup.map σ.toRingHom m, ?_⟩
      rw [hfield, mul_inv_cancel_right]
    · rintro _ ⟨m,rfl⟩
      refine ⟨GeneralLinearGroup.map σ⁻¹.toRingHom m, ?_⟩
      rw [← map_inv, hfield, map_inv, inv_mul_cancel_right]
  let K := innerDiagonal F ⊔ (fieldAction F).range
  have hgi : (graph F)⁻¹ = graph F :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using graph_sq F)
  have hgK : ∀ x ∈ K, graph F * x * (graph F)⁻¹ ∈ K := by
    have hh : K ≤ K.comap (MulAut.conj (graph F)).toMonoidHom := by
      apply sup_le
      · rintro _ ⟨m,rfl⟩
        obtain ⟨m',hm'⟩ := hgraph m
        change graph F * linearConj F m * (graph F)⁻¹ ∈ K
        rw [hm', mul_inv_cancel_right]
        exact (le_sup_left : innerDiagonal F ≤ K) ⟨m',rfl⟩
      · rintro _ ⟨σ,rfl⟩
        change graph F * fieldAction F σ * (graph F)⁻¹ ∈ K
        rw [← (hcomm σ).eq, mul_inv_cancel_right]
        exact (le_sup_right : (fieldAction F).range ≤ K) ⟨σ,rfl⟩
    exact hh
  have hgn : Subgroup.zpowers (graph F) ≤ Subgroup.normalizer K := by
    apply Subgroup.zpowers_le.mpr
    apply mem_normalizer_of_conjugates K (graph F) hgK
    intro x hx
    simpa only [hgi] using hgK x hx
  change α ∈ (↑(K ⊔ Subgroup.zpowers (graph F)) : Set _) at hα
  rw [Subgroup.coe_mul_of_right_le_normalizer_left K _ hgn] at hα
  obtain ⟨a,ha,g,hg,rfl⟩ := hα
  change a ∈ (↑(innerDiagonal F ⊔ (fieldAction F).range) : Set _) at ha
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hfn] at ha
  obtain ⟨_,⟨m,rfl⟩,_,⟨σ,rfl⟩,rfl⟩ := ha
  refine ⟨m,σ,?_⟩
  rcases one_or_generator_of_sq (graph F) (graph_sq F) hg with rfl | rfl
  · exact Or.inl (mul_one _)
  · exact Or.inr rfl

/-- Use coordinate reversal to express the graph case with the representative
that preserves the upper unipotent subgroup. -/
theorem standard_opposition_factorization
    (hfield : ∀ (σ : F ≃+* F) (m : GL (Fin 3) F),
      fieldAction F σ * linearConj F m =
        linearConj F (GeneralLinearGroup.map σ.toRingHom m) * fieldAction F σ)
    (hgraph : ∀ m : GL (Fin 3) F, ∃ m' : GL (Fin 3) F,
      graph F * linearConj F m = linearConj F m' * graph F)
    (hcomm : ∀ σ : F ≃+* F, Commute (fieldAction F σ) (graph F))
    (α : MulAut PSL(3,F)) (hα : α ∈ standard F) :
    ∃ (m : GL (Fin 3) F) (σ : F ≃+* F),
      α = linearConj F m * fieldAction F σ ∨
      α = linearConj F m * fieldAction F σ * oppositionGraph F := by
  obtain ⟨m,σ,h | h⟩ := standard_factorization F hfield hgraph hcomm α hα
  · exact ⟨m,σ,Or.inl h⟩
  · refine ⟨m * (GeneralLinearGroup.map σ.toRingHom (reversalGL F))⁻¹, σ, Or.inr ?_⟩
    rw [h, map_mul, map_inv, oppositionGraph]
    calc
      _ = linearConj F m *
          (linearConj F (GeneralLinearGroup.map σ.toRingHom (reversalGL F)))⁻¹ *
          (linearConj F (GeneralLinearGroup.map σ.toRingHom (reversalGL F)) * fieldAction F σ) *
          graph F := by group
      _ = _ := by rw [← hfield]; simp only [mul_assoc]

end Matrix.PSL3.CartanActions.NormalizerForm
