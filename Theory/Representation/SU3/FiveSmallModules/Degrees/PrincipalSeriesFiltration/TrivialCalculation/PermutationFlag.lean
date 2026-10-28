module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.CosetCoordinates
public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.CoordinateFiltrations.FlagTools
public import Mathlib.RingTheory.SimpleModule.Rank

/-!
# The end factors of a finite permutation flag

Over any field, the constant line is one dimensional, and augmentation has
one-dimensional quotient. Thus an invariant subspace between constants and
augmentation, with simple quotients of degrees 20 and 104, supplies all
four factors of the required filtration. The subspaces and quotient actions
are literal ones; the middle-subspace existence is an explicit premise.

This is the elementary assembly for the trivial SU₃(5) principal series
in the approach to Guralnick–Malle, *Classification of 2F-modules I*,
Proposition 4.3, p.10; Aschbacher–Smith K.2, printed p.453.
-/

@[expose] public section

open scoped MonoidAlgebra
open BenderSuzuki.MatrixGroups
namespace Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation
open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations
section Permutation
variable {K G Ω : Type*} [Field K] [Group G] [MulAction G Ω]

def constants : Subrepresentation (functionAction (K := K) (G := G) (Ω := Ω)) where
  toSubmodule := Submodule.span K {fun _ => (1 : K)}
  apply_mem_toSubmodule g v hv := by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    have he : functionAction (K := K) (Ω := Ω) g (fun _ => 1) = (fun _ => 1) := rfl
    rw [map_smul, he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

noncomputable def augmentation [Fintype Ω] : (Ω → K) →ₗ[K] K where
  toFun v := ∑ i, v i
  map_add' := by intros; exact Finset.sum_add_distrib
  map_smul' := by intros; simp [Finset.mul_sum]

noncomputable def augmentationKernel [Fintype Ω] :
    Subrepresentation (functionAction (K := K) (G := G) (Ω := Ω)) where
  toSubmodule := (augmentation (K := K) (Ω := Ω)).ker
  apply_mem_toSubmodule g v hv := by
    change (∑ x, v (g⁻¹ • x)) = 0
    exact (Equiv.sum_comp (MulAction.toPerm g⁻¹) v).trans hv

theorem finrank_constants [Nonempty Ω] :
    Module.finrank K (constants (K := K) (G := G) (Ω := Ω)).toSubmodule = 1 := by
  apply finrank_span_singleton
  intro h
  exact one_ne_zero (congrFun h (Classical.choice ‹Nonempty Ω›))

theorem augmentation_surjective [Fintype Ω] [Nonempty Ω] :
    Function.Surjective (augmentation (K := K) (Ω := Ω)) := by
  classical
  intro c
  exact ⟨Pi.single (Classical.choice ‹Nonempty Ω›) c, by simp [augmentation]⟩

theorem finrank_augmentation_quotient [Fintype Ω] [Nonempty Ω] :
    Module.finrank K ((Ω → K) ⧸ (augmentationKernel (K := K) (G := G) (Ω := Ω)).toSubmodule) = 1 := by
  let e := (augmentation (K := K) (Ω := Ω)).quotKerEquivOfSurjective augmentation_surjective
  exact e.finrank_eq.trans (Module.finrank_self K)

theorem irreducible_of_finrank_one {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (h : Module.finrank K V = 1) : IsIrreducible ρ := by
  let : IsSimpleModule K V := isSimpleModule_iff_finrank_eq_one.mpr h
  let : Nontrivial V := IsSimpleModule.nontrivial K V
  rw [IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, fun S => ?_⟩
  rcases eq_bot_or_eq_top S.toSubmodule with hs | hs
  · exact Or.inl (Subrepresentation.toSubmodule_injective hs)
  · exact Or.inr (Subrepresentation.toSubmodule_injective hs)

theorem filtration_of_finrank_one {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (h : Module.finrank K V = 1) {D : Set ℕ} (hD : 1 ∈ D) :
    FactorDegreeFiltration D ρ := by
  have hq : Module.finrank K (V ⧸ (⊥ : Subrepresentation ρ).toSubmodule) = 1 := by
    change Module.finrank K (V ⧸ (⊥ : Submodule K V)) = 1
    rw [(Submodule.quotEquivOfEqBot _ rfl).finrank_eq]
    exact h
  let : Subsingleton (⊥ : Subrepresentation ρ).toSubmodule :=
    inferInstanceAs (Subsingleton (⊥ : Submodule K V))
  exact .step ⊥ (.zero _) (irreducible_of_finrank_one _ hq) (hq.symm ▸ hD)

/-- A single interior subspace supplies precisely the two nontrivial factors.
The constant line and augmentation quotient are handled independently. -/
def MiddleFlag [Fintype Ω] : Prop :=
  ∃ U : Subrepresentation (functionAction (K := K) (G := G) (Ω := Ω)),
    constants ≤ U ∧ U ≤ augmentationKernel ∧
    IsIrreducible (within constants U).quotientRepresentation ∧
    IsIrreducible (within U augmentationKernel).quotientRepresentation ∧
    Module.finrank K (U.toSubmodule ⧸ (within constants U).toSubmodule) ∈ ({20, 104} : Set ℕ) ∧
    Module.finrank K (augmentationKernel.toSubmodule ⧸ (within U augmentationKernel).toSubmodule)
      ∈ ({20, 104} : Set ℕ)

set_option backward.isDefEq.respectTransparency false in
theorem filtration_of_middleFlag [Fintype Ω] [Nonempty Ω]
    (h : MiddleFlag (K := K) (G := G) (Ω := Ω)) :
    FactorDegreeFiltration {1, 20, 104} (functionAction (K := K) (G := G) (Ω := Ω)) := by
  obtain ⟨U, hCU, hUA, hs₁, hs₂, hd₁, hd₂⟩ := h
  have hC : FactorDegreeFiltration {1, 20, 104}
      (constants (K := K) (G := G) (Ω := Ω)).toRepresentation :=
    filtration_of_finrank_one _ finrank_constants (by simp)
  let CU : Subrepresentation U.toRepresentation := within constants U
  have hCUf : FactorDegreeFiltration (V := CU.toSubmodule) (k := K) (G := G) {1, 20, 104} CU.toRepresentation := by
    apply hC.transport (MonoidHom.id G) (fun x => ⟨x, rfl⟩) _ (withinEquiv constants U hCU)
    intro g v
    rfl
  have hU : FactorDegreeFiltration {1, 20, 104} U.toRepresentation :=
    .step CU hCUf hs₁ (Set.mem_insert_of_mem 1 hd₁)
  let UA : Subrepresentation (augmentationKernel (K := K) (G := G) (Ω := Ω)).toRepresentation :=
    within U augmentationKernel
  have hUAf : FactorDegreeFiltration (V := UA.toSubmodule) (k := K) (G := G) {1, 20, 104} UA.toRepresentation := by
    apply hU.transport (MonoidHom.id G) (fun x => ⟨x, rfl⟩) _ (withinEquiv U augmentationKernel hUA)
    intro g v
    rfl
  have hA : FactorDegreeFiltration {1, 20, 104}
      (augmentationKernel (K := K) (G := G) (Ω := Ω)).toRepresentation :=
    .step UA hUAf hs₂ (Set.mem_insert_of_mem 1 hd₂)
  exact .step augmentationKernel hA
    (irreducible_of_finrank_one _ finrank_augmentation_quotient)
    (by rw [finrank_augmentation_quotient]; simp)
end Permutation
end Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation
