module

public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.Configurations.FourDimensionalMarking.Core
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.Configurations.FourDimensionalMarking.Diagonal
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.Configurations.FourDimensionalMarking.Splitting
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.Configurations.FourDimensionalMarking.Transitivity

/-!
# Assembly of the marked four-dimensional branch

The faithful four-space forces core rank two. Coprime splitting constructs
the two literal support factors, and the fixed-space dimension budget forces
the original actor to exchange them. The actual semidirect product supplies
an isomorphism to S₃ × S₃; transitivity then forces the factors' diagonal
marking under that isomorphism.
The starred-offender dimension budget gives fixed codimension three and
global cubic ratio three halves. The application uses the original
subgroups inside their generated local group and obtains the strict ratio
bound from its noncentralized hyperplane fixed space.

`Reduced.fullSupport_marking` discharges both geometric inputs from the
reduced hypotheses and the full-support branch assumption. The resulting
configuration supplies the first alternative of the common configuration
interface. The reduction to this branch remains with the source assembly.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
D.2.14(3),(6),(7)(i), the first branch on printed p.187.
-/

public section
namespace CFSG.Quasithin.ChapterD.FittingConfigurations
open Representation.BinaryOffender
open scoped ENNReal

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The remaining geometric inputs give the original marked group and ratio. -/
theorem Reduced.fullSupport_marking_of_transitive_factors
    {P A : Subgroup G} {s : ℕ} (h : Reduced ρ P A s)
    (hlow : 1 < cubicRatio ρ) (hfull : FullSupport ρ P A)
    (d : SupportFactors ρ P s) (ht : d.IsTransitive A) :
    s = 2 ∧
      (∃ e : G ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)),
        d.IsDiagonal e ∧ d.IsTransitive A) ∧
      fixedCodim ρ A = 3 ∧ cubicRatio ρ = 3 / 2 := by
  obtain ⟨Z, hZ, hmove, hdim⟩ := hfull
  have hs := h.core_rank_eq_two_of_finrank_four ρ hdim
  have hP : Nat.card P = 9 := by rw [h.card_core, hs]; rfl
  obtain ⟨e⟩ := h.nonempty_symmetricThree_product_of_rank_two ρ hs
  exact ⟨hs, ⟨e, d.isDiagonal_of_isTransitive hP ht e, ht⟩,
    h.small_dimension_ratio ρ hlow (by omega)⟩

/-- The literal local-generated-group application discharges the strict lower
ratio bound using the original moved hyperplane fixed space. -/
theorem local_generated_fullSupport_marking_of_transitive_factors
    (P A B : Subgroup G)
    (σ : Representation (ZMod 2) (P ⊔ A : Subgroup G) V) {s : ℕ}
    (h : Reduced σ (P.subgroupOf (P ⊔ A)) (A.subgroupOf (P ⊔ A)) s)
    (hBA : B ≤ A) (hrB : rank (B.subgroupOf (P ⊔ A)) = 1)
    (hn : subspaceCommutator σ (fixedSpace σ (B.subgroupOf (P ⊔ A)))
      (A.subgroupOf (P ⊔ A)) ≠ ⊥)
    (hfull : FullSupport σ (P.subgroupOf (P ⊔ A)) (A.subgroupOf (P ⊔ A)))
    (d : SupportFactors σ (P.subgroupOf (P ⊔ A)) s)
    (ht : d.IsTransitive (A.subgroupOf (P ⊔ A))) :
    s = 2 ∧
      (∃ e : (P ⊔ A : Subgroup G) ≃*
          (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)),
        d.IsDiagonal e ∧ d.IsTransitive (A.subgroupOf (P ⊔ A))) ∧
      fixedCodim σ (A.subgroupOf (P ⊔ A)) = 3 ∧ cubicRatio σ = 3 / 2 := by
  apply h.fullSupport_marking_of_transitive_factors σ _ hfull d ht
  exact h.one_lt_ratio_of_moved_hyperplane σ (fun _ hb => hBA hb) hrB hn

/-- The full-support branch constructs the literal factors, their diagonal
marking in the original group, and their conjugation transitivity, with no
additional geometric premises. -/
theorem Reduced.fullSupport_marking
    {P A : Subgroup G} {s : ℕ} (h : Reduced ρ P A s)
    (hlow : 1 < cubicRatio ρ) (hfull : FullSupport ρ P A) :
    ∃ d : SupportFactors ρ P s, s = 2 ∧
      (∃ e : G ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)),
        d.IsDiagonal e ∧ d.IsTransitive A) ∧
      fixedCodim ρ A = 3 ∧ cubicRatio ρ = 3 / 2 := by
  obtain ⟨d⟩ := h.fullSupport_supportFactors ρ hfull
  exact ⟨d, h.fullSupport_marking_of_transitive_factors ρ hlow hfull d
    (h.fullSupport_transitivity ρ hlow hfull d)⟩

/-- The marked four-space supplies the first source configuration alternative
and its ratio on the same module. -/
theorem Reduced.fullSupport_configuration
    {P A : Subgroup G} {s : ℕ} (h : Reduced ρ P A s)
    (hlow : 1 < cubicRatio ρ) (hfull : FullSupport ρ P A) :
    ∃ d : SupportFactors ρ P s, d.Alternatives A ∧
      fixedCodim ρ A = 3 ∧ cubicRatio ρ = 3 / 2 := by
  obtain ⟨d, hs, he, hratio⟩ := h.fullSupport_marking ρ hlow hfull
  exact ⟨d, Or.inl ⟨hs, he⟩, hratio⟩

/-- On the literal generated local group, the noncentralized hyperplane fixed
space supplies the strict ratio bound. Both support factors and their markings
are constructed from the reduced full-support hypotheses. -/
theorem local_generated_fullSupport_marking
    (P A B : Subgroup G)
    (σ : Representation (ZMod 2) (P ⊔ A : Subgroup G) V) {s : ℕ}
    (h : Reduced σ (P.subgroupOf (P ⊔ A)) (A.subgroupOf (P ⊔ A)) s)
    (hBA : B ≤ A) (hrB : rank (B.subgroupOf (P ⊔ A)) = 1)
    (hn : subspaceCommutator σ (fixedSpace σ (B.subgroupOf (P ⊔ A)))
      (A.subgroupOf (P ⊔ A)) ≠ ⊥)
    (hfull : FullSupport σ (P.subgroupOf (P ⊔ A)) (A.subgroupOf (P ⊔ A))) :
    ∃ d : SupportFactors σ (P.subgroupOf (P ⊔ A)) s, s = 2 ∧
      (∃ e : (P ⊔ A : Subgroup G) ≃*
          (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)),
        d.IsDiagonal e ∧ d.IsTransitive (A.subgroupOf (P ⊔ A))) ∧
      fixedCodim σ (A.subgroupOf (P ⊔ A)) = 3 ∧ cubicRatio σ = 3 / 2 := by
  apply h.fullSupport_marking σ _ hfull
  exact h.one_lt_ratio_of_moved_hyperplane σ (fun _ hb => hBA hb) hrB hn

end CFSG.Quasithin.ChapterD.FittingConfigurations
