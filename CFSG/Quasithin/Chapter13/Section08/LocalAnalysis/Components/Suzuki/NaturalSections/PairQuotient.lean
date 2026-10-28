module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.Natural
public import Theory.Representation.BinaryOffender.IrreducibleSection
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.PairQuotient.Linear

/-!
# The paired Suzuki central quotient

A product equivalence K₀ ≃ K₁ × K₂ is marked by its compatibility with
both literal subgroup inclusions. Composing its two coordinates with the
surjective Suzuki actor maps gives a surjection onto the whole Suzuki
product, with the same component markings.

For W = W₁ + W₂, where each stable Wᵢ is fixed by the other factor,
addition identifies the product of the individual central quotients with
the literal W/C_W(K₀). Composing its inverse with the two given natural
module equivalences constructs the paired equivalence. Its representative
formula proves equivariance for centralQuotientRepresentation. No splitting
of W is required, and the individual natural module identifications remain
explicit hypotheses of this conditional construction.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
F.9.18(5iii), printed pp.325–326, and the swapped Suzuki case of 13.8.16,
pp.952–953. This helper does not assert the classification of the individual
factor sections or the final source theorem.
-/

@[expose] public section

open Representation Representation.BinaryOffender
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.PairQuotient
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {K₀ K₁ K₂ : Subgroup G}

/-- A product marking of the actual subgroups, compatible with both literal inclusions. -/
structure ProductActors (K₀ K₁ K₂ : Subgroup G) where
  le₁ : K₁ ≤ K₀
  le₂ : K₂ ≤ K₀
  equiv : K₀ ≃* K₁ × K₂
  inclusion₁ : ∀ k, equiv (Subgroup.inclusion le₁ k) = (k, 1)
  inclusion₂ : ∀ k, equiv (Subgroup.inclusion le₂ k) = (1, k)

namespace ProductActors
variable (d : ProductActors K₀ K₁ K₂)

/-- Every actor is the product of its two actual component coordinates. -/
theorem factorization (k : K₀) :
    Subgroup.inclusion d.le₁ (d.equiv k).1 *
      Subgroup.inclusion d.le₂ (d.equiv k).2 = k := by
  apply d.equiv.injective
  rw [map_mul, d.inclusion₁, d.inclusion₂]
  simp

/-- The factors may also be multiplied in reverse order. -/
theorem factorization_rev (k : K₀) :
    Subgroup.inclusion d.le₂ (d.equiv k).2 *
      Subgroup.inclusion d.le₁ (d.equiv k).1 = k := by
  apply d.equiv.injective
  rw [map_mul, d.inclusion₁, d.inclusion₂]
  simp

include d in
/-- The compatible product marking implies the required subgroup generation. -/
theorem sup_eq : K₀ = K₁ ⊔ K₂ := by
  apply le_antisymm _ (sup_le d.le₁ d.le₂)
  intro k hk
  have he := congrArg (fun a : K₀ => (a : G)) (d.factorization ⟨k, hk⟩)
  change ((d.equiv ⟨k, hk⟩).1 : G) * (d.equiv ⟨k, hk⟩).2 = k at he
  rw [← he]
  exact Subgroup.mul_mem_sup (d.equiv ⟨k, hk⟩).1.property
    (d.equiv ⟨k, hk⟩).2.property

/-- The quotient actors are independent because the marking uses the whole product. -/
noncomputable def pairedActor {m : ℕ} (φ₁ : K₁ →* SuzukiMatrixGroup m) (φ₂ : K₂ →* SuzukiMatrixGroup m) :
    K₀ →* SuzukiMatrixGroup m × SuzukiMatrixGroup m :=
  (φ₁.prodMap φ₂).comp d.equiv.toMonoidHom

theorem pairedActor_apply {m : ℕ} (φ₁ : K₁ →* SuzukiMatrixGroup m)
    (φ₂ : K₂ →* SuzukiMatrixGroup m) (k : K₀) :
    d.pairedActor φ₁ φ₂ k = (φ₁ (d.equiv k).1, φ₂ (d.equiv k).2) := rfl

theorem pairedActor_inclusion₁ {m : ℕ} (φ₁ : K₁ →* SuzukiMatrixGroup m)
    (φ₂ : K₂ →* SuzukiMatrixGroup m) (k : K₁) :
    d.pairedActor φ₁ φ₂ (Subgroup.inclusion d.le₁ k) = (φ₁ k, 1) := by
  simp [pairedActor_apply, d.inclusion₁]

theorem pairedActor_inclusion₂ {m : ℕ} (φ₁ : K₁ →* SuzukiMatrixGroup m)
    (φ₂ : K₂ →* SuzukiMatrixGroup m) (k : K₂) :
    d.pairedActor φ₁ φ₂ (Subgroup.inclusion d.le₂ k) = (1, φ₂ k) := by
  simp [pairedActor_apply, d.inclusion₂]

theorem pairedActor_surjective {m : ℕ} (φ₁ : K₁ →* SuzukiMatrixGroup m)
    (φ₂ : K₂ →* SuzukiMatrixGroup m)
    (hφ₁ : Function.Surjective φ₁) (hφ₂ : Function.Surjective φ₂) :
    Function.Surjective (d.pairedActor φ₁ φ₂) := by
  rintro ⟨g₁, g₂⟩
  obtain ⟨k₁, rfl⟩ := hφ₁ g₁
  obtain ⟨k₂, rfl⟩ := hφ₂ g₂
  exact ⟨d.equiv.symm (k₁, k₂), by simp [pairedActor_apply]⟩

variable (ρ : Representation (ZMod 2) G V)
  {W₁ W₂ : Submodule (ZMod 2) V}

theorem action_fst (h₁₂ : W₁ ≤ fixedSpace ρ K₂) (k : K₀) (x : W₁) :
    ρ k x = ρ (d.equiv k).1 x := by
  have he := congrArg (fun a : K₀ => ρ (a : G) (x : V)) (d.factorization k)
  change ρ ((d.equiv k).1 * (d.equiv k).2 : G) x = ρ k x at he
  have hx : ρ (d.equiv k).2 x = x := h₁₂ x.property (d.equiv k).2
  rw [map_mul, Module.End.mul_apply, hx] at he
  exact he.symm

theorem action_snd (h₂₁ : W₂ ≤ fixedSpace ρ K₁) (k : K₀) (y : W₂) :
    ρ k y = ρ (d.equiv k).2 y := by
  have he := congrArg (fun a : K₀ => ρ (a : G) (y : V)) (d.factorization_rev k)
  change ρ ((d.equiv k).2 * (d.equiv k).1 : G) y = ρ k y at he
  have hy : ρ (d.equiv k).1 y = y := h₂₁ y.property (d.equiv k).1
  rw [map_mul, Module.End.mul_apply, hy] at he
  exact he.symm

end ProductActors
end CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.PairQuotient

namespace CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.PairQuotient
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)
  {K₀ K₁ K₂ : Subgroup G} (d : ProductActors K₀ K₁ K₂)
  {W W₁ W₂ : Submodule (ZMod 2) V}
  (hW : W = W₁ ⊔ W₂)
  (h₁₂ : W₁ ≤ fixedSpace ρ K₂) (h₂₁ : W₂ ≤ fixedSpace ρ K₁)

include hW in
/-- Stability of the summands gives stability of their actual sum. -/
theorem sum_stable (s₁ : K₀ ≤ subspaceStabilizer ρ W₁)
    (s₂ : K₀ ≤ subspaceStabilizer ρ W₂) : K₀ ≤ subspaceStabilizer ρ W := by
  apply le_subspaceStabilizer
  intro k hk w hw
  rw [hW] at hw ⊢
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hw
  rw [map_add]
  exact Submodule.add_mem_sup ((s₁ hk x).2 hx) ((s₂ hk y).2 hy)

/-- Addition intertwines the actual quotient action and the two component actions. -/
theorem centralSumEquiv_intertwines
    (s₀ : K₀ ≤ subspaceStabilizer ρ W)
    (s₁ : K₀ ≤ subspaceStabilizer ρ W₁)
    (s₂ : K₀ ≤ subspaceStabilizer ρ W₂)
    (k : K₀) (a : centralQuotient ρ K₁ W₁) (b : centralQuotient ρ K₂ W₂) :
    centralSumEquiv ρ d.sup_eq hW h₁₂ h₂₁
      (centralQuotientRepresentation ρ K₁ W₁ (d.le₁.trans s₁) (d.equiv k).1 a,
       centralQuotientRepresentation ρ K₂ W₂ (d.le₂.trans s₂) (d.equiv k).2 b) =
    centralQuotientRepresentation ρ K₀ W s₀ k
      (centralSumEquiv ρ d.sup_eq hW h₁₂ h₂₁ (a, b)) := by
  induction a using Submodule.Quotient.induction_on with | _ x =>
  induction b using Submodule.Quotient.induction_on with | _ y =>
  let x' : W₁ := ⟨ρ (d.equiv k).1 x, ((s₁ (d.le₁ (d.equiv k).1.property)) x).2 x.property⟩
  let y' : W₂ := ⟨ρ (d.equiv k).2 y, ((s₂ (d.le₂ (d.equiv k).2.property)) y).2 y.property⟩
  change centralSumEquiv ρ d.sup_eq hW h₁₂ h₂₁
    (Submodule.Quotient.mk x', Submodule.Quotient.mk y') = _
  rw [centralSumEquiv_mk, centralSumEquiv_mk]
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  change ρ (d.equiv k).1 x + ρ (d.equiv k).2 y = ρ k ((x : V) + y)
  rw [map_add, d.action_fst ρ h₁₂ k x, d.action_snd ρ h₂₁ k y]

variable {m : ℕ}
  (e₁ : centralQuotient ρ K₁ W₁ ≃ₗ[ZMod 2] (Fin 4 → BinaryGaloisField (2 * m + 1)))
  (e₂ : centralQuotient ρ K₂ W₂ ≃ₗ[ZMod 2] (Fin 4 → BinaryGaloisField (2 * m + 1)))

/-- The paired natural module is constructed from the two individual factor equivalences. -/
noncomputable def pairedEquiv :
    centralQuotient ρ K₀ W ≃ₗ[ZMod 2]
      ((Fin 4 → BinaryGaloisField (2 * m + 1)) ×
       (Fin 4 → BinaryGaloisField (2 * m + 1))) :=
  (centralSumEquiv ρ d.sup_eq hW h₁₂ h₂₁).symm.trans (e₁.prodCongr e₂)

/-- Any decomposition into the actual subspaces computes the same paired coordinates. -/
theorem pairedEquiv_mk (x : W₁) (y : W₂) :
    pairedEquiv ρ d hW h₁₂ h₂₁ e₁ e₂
      (Submodule.Quotient.mk (⟨(x : V) + y,
        hW ▸ Submodule.add_mem_sup x.property y.property⟩ : W)) =
    (e₁ (Submodule.Quotient.mk x), e₂ (Submodule.Quotient.mk y)) := by
  change (e₁.prodCongr e₂) ((centralSumEquiv ρ d.sup_eq hW h₁₂ h₂₁).symm _) = _
  rw [centralSumEquiv_symm_mk]
  rfl

/-- The constructed equivalence intertwines centralQuotientRepresentation with naturalPair. -/
theorem pairedEquiv_intertwines
    (s₀ : K₀ ≤ subspaceStabilizer ρ W)
    (s₁ : K₀ ≤ subspaceStabilizer ρ W₁)
    (s₂ : K₀ ≤ subspaceStabilizer ρ W₂)
    (φ₁ : K₁ →* SuzukiMatrixGroup m) (φ₂ : K₂ →* SuzukiMatrixGroup m)
    (he₁ : ∀ k v, e₁ (centralQuotientRepresentation ρ K₁ W₁ (d.le₁.trans s₁) k v) =
      natural m (φ₁ k) (e₁ v))
    (he₂ : ∀ k v, e₂ (centralQuotientRepresentation ρ K₂ W₂ (d.le₂.trans s₂) k v) =
      natural m (φ₂ k) (e₂ v))
    (k : K₀) (v : centralQuotient ρ K₀ W) :
    pairedEquiv ρ d hW h₁₂ h₂₁ e₁ e₂ (centralQuotientRepresentation ρ K₀ W s₀ k v) =
      naturalPair m (d.pairedActor φ₁ φ₂ k) (pairedEquiv ρ d hW h₁₂ h₂₁ e₁ e₂ v) := by
  obtain ⟨⟨a, b⟩, rfl⟩ := (centralSumEquiv ρ d.sup_eq hW h₁₂ h₂₁).surjective v
  rw [← centralSumEquiv_intertwines ρ d hW h₁₂ h₂₁ s₀ s₁ s₂]
  simp only [pairedEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  exact Prod.ext (he₁ (d.equiv k).1 a) (he₂ (d.equiv k).2 b)

include h₁₂ h₂₁ in
/-- Conditional paired-section assembly, including surjectivity, compatibility with
both literal subgroup inclusions, representative coordinates, and equivariance.
Only the two individual factor equivalences are assumed. -/
theorem exists_pairedCentralSection
    (s₁ : K₀ ≤ subspaceStabilizer ρ W₁)
    (s₂ : K₀ ≤ subspaceStabilizer ρ W₂)
    (φ₁ : K₁ →* SuzukiMatrixGroup m) (φ₂ : K₂ →* SuzukiMatrixGroup m)
    (hφ₁ : Function.Surjective φ₁) (hφ₂ : Function.Surjective φ₂)
    (he₁ : ∀ k v, e₁ (centralQuotientRepresentation ρ K₁ W₁ (d.le₁.trans s₁) k v) =
      natural m (φ₁ k) (e₁ v))
    (he₂ : ∀ k v, e₂ (centralQuotientRepresentation ρ K₂ W₂ (d.le₂.trans s₂) k v) =
      natural m (φ₂ k) (e₂ v)) :
    ∃ φ : K₀ →* SuzukiMatrixGroup m × SuzukiMatrixGroup m,
      Function.Surjective φ ∧
      (∀ k : K₁, φ (Subgroup.inclusion d.le₁ k) = (φ₁ k, 1)) ∧
      (∀ k : K₂, φ (Subgroup.inclusion d.le₂ k) = (1, φ₂ k)) ∧
      ∃ e : centralQuotient ρ K₀ W ≃ₗ[ZMod 2]
        ((Fin 4 → BinaryGaloisField (2 * m + 1)) ×
         (Fin 4 → BinaryGaloisField (2 * m + 1))),
        (∀ (x : W₁) (y : W₂), e
          (Submodule.Quotient.mk (⟨(x : V) + y,
            hW ▸ Submodule.add_mem_sup x.property y.property⟩ : W)) =
          (e₁ (Submodule.Quotient.mk x), e₂ (Submodule.Quotient.mk y))) ∧
        ∀ k v, e (centralQuotientRepresentation ρ K₀ W (sum_stable ρ hW s₁ s₂) k v) =
          naturalPair m (φ k) (e v) := by
  refine ⟨d.pairedActor φ₁ φ₂, d.pairedActor_surjective φ₁ φ₂ hφ₁ hφ₂,
    d.pairedActor_inclusion₁ φ₁ φ₂, d.pairedActor_inclusion₂ φ₁ φ₂,
    pairedEquiv ρ d hW h₁₂ h₂₁ e₁ e₂, pairedEquiv_mk ρ d hW h₁₂ h₂₁ e₁ e₂, ?_⟩
  exact pairedEquiv_intertwines ρ d hW h₁₂ h₂₁ e₁ e₂
    (sum_stable ρ hW s₁ s₂) s₁ s₂ φ₁ φ₂ he₁ he₂

end CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.PairQuotient
