module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.Projection
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.Representation.GeneratedSubgroupInvariants
public import Theory.Representation.SubspaceQuotient

/-!
# Actual quotient projections for the two-factor sum

The quotient by U₂ kills K₂ when U = U₁ + U₂ and K₂ fixes U₁.
Equal marked subgroup images modulo K₂, fixation by L₀, and commutator
generation by L₁,+ then put the seed in U₂. Its invariance under the
factor exchange puts it in U₁ as well. The intersection is fixed by
both factors, contradicting the nonzero commutator-generated seed.

This proves that the quotient seed image is nonzero and handles an
overlapping sum in case (b1), as well as the direct sum in case (a).
All quotient maps and their equivariance are the literal maps induced
by the supplied representation. No directness is inferred from a sum.
The source application must construct the marked projected group images,
component submodules, factor exchange, and the seed inside the source action.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 13.8.16(1), cases (a) and (b1), printed p.952 (PDF p.969).
-/

@[expose] public section

open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo
variable {G U : Type*} [Group G] [AddCommGroup U] [Module (ZMod 2) U]

/-- The quotient projection identifies the actions of marked subgroups with the
same image modulo a factor acting trivially on that quotient. -/
theorem seed_le_of_factor_cosets (ρ : Representation (ZMod 2) G U)
    (W : Subrepresentation ρ) (X : Submodule (ZMod 2) U)
    (L₀ Lplus K₂ : Subgroup G)
    (hcoset : Lplus ≤ L₀ ⊔ K₂)
    (hfix : X ≤ fixedSpace ρ L₀)
    (hfactor : ∀ g ∈ K₂, ∀ u, ρ g u - u ∈ W)
    (hgen : subspaceCommutator ρ X Lplus = X) : X ≤ W.toSubmodule := by
  have hfixed : X.map W.toSubmodule.mkQ ≤ fixedSpace W.quotientRepresentation Lplus := by
    apply le_trans _ (Representation.invariants_comp_subtype_antitone
      W.quotientRepresentation hcoset)
    rw [Representation.invariants_comp_sup]
    refine le_inf ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩ g
      change W.toSubmodule.mkQ (ρ (g : G) x) = W.toSubmodule.mkQ x
      exact congrArg W.toSubmodule.mkQ (hfix hx g)
    · rintro _ ⟨x, hx, rfl⟩ g
      change W.toSubmodule.mkQ (ρ (g : G) x) = W.toSubmodule.mkQ x
      exact (Submodule.Quotient.eq W.toSubmodule).mpr (hfactor g g.property x)
  rw [← hgen]
  apply Submodule.span_le.mpr
  rintro _ ⟨g, hg, x, hx, rfl⟩
  apply (Submodule.Quotient.eq W.toSubmodule).mp
  exact (W.quotientRepresentation_mk g x).symm.trans
    (hfixed (Submodule.mem_map.mpr ⟨x, hx, rfl⟩) ⟨g, hg⟩)

/-- A quotient by one summand really kills the other factor, even when the
sum is not direct. -/
theorem factor_trivial_on_quotient_of_sum (ρ : Representation (ZMod 2) G U)
    (U₁ U₂ : Subrepresentation ρ) (K₂ : Subgroup G)
    (hsum : U₁.toSubmodule ⊔ U₂.toSubmodule = ⊤)
    (hcross : U₁.toSubmodule ≤ fixedSpace ρ K₂) :
    ∀ g ∈ K₂, ∀ u, ρ g u - u ∈ U₂ := by
  intro g hg u
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp
    (hsum ▸ (show u ∈ (⊤ : Submodule (ZMod 2) U) from trivial))
  have hf : ρ g u₁ = u₁ := hcross hu₁ ⟨g, hg⟩
  rw [map_add, hf, add_sub_add_left_eq_sub]
  exact U₂.toSubmodule.sub_mem (U₂.apply_mem_toSubmodule g hu₂) hu₂

/-- The overlap of the two factor modules is fixed by their join. -/
theorem overlap_fixed (ρ : Representation (ZMod 2) G U)
    (U₁ U₂ : Submodule (ZMod 2) U) (K₁ K₂ : Subgroup G)
    (h₁ : U₂ ≤ fixedSpace ρ K₁) (h₂ : U₁ ≤ fixedSpace ρ K₂) :
    U₁ ⊓ U₂ ≤ fixedSpace ρ (K₁ ⊔ K₂) := by
  rw [fixedSpace, Representation.invariants_comp_sup]
  exact le_inf (inf_le_right.trans h₁) (inf_le_left.trans h₂)

/-- The first quotient image of a nonzero, exchanged, commutator-generated
seed is nonzero. The summands need not be disjoint. -/
theorem seed_quotient_ne_bot (ρ : Representation (ZMod 2) G U)
    (U₁ U₂ X : Submodule (ZMod 2) U) (K₁ K₂ Lplus : Subgroup G)
    (s : U ≃ₗ[ZMod 2] U)
    (hseed : X ≠ ⊥) (hgen : subspaceCommutator ρ X Lplus = X)
    (hL : Lplus ≤ K₁ ⊔ K₂)
    (h₁ : U₂ ≤ fixedSpace ρ K₁) (h₂ : U₁ ≤ fixedSpace ρ K₂)
    (hseed_swap : X.map s.toLinearMap = X)
    (hswap : U₂.map s.toLinearMap ≤ U₁) :
    X.map U₂.mkQ ≠ ⊥ := by
  intro hz
  have hX₂ : X ≤ U₂ := by
    intro x hx
    apply (Submodule.Quotient.mk_eq_zero U₂).mp
    have hm : U₂.mkQ x ∈ X.map U₂.mkQ := ⟨x, hx, rfl⟩
    rwa [hz] at hm
  have hX₁ : X ≤ U₁ := by
    rw [← hseed_swap]
    exact (Submodule.map_mono hX₂).trans hswap
  have hf : X ≤ fixedSpace ρ Lplus :=
    (le_inf hX₁ hX₂).trans ((overlap_fixed ρ U₁ U₂ K₁ K₂ h₁ h₂).trans
      (Representation.invariants_comp_subtype_antitone ρ hL))
  exact hseed (hgen.symm.trans ((subspaceCommutator_eq_bot_iff ρ X Lplus).mpr hf))

/-- Exclude both a direct sum and the possibly overlapping sum in case (b1),
using the actual quotient action rather than an assumed coordinate projection. -/
theorem not_sum_of_diagonal_seed (ρ : Representation (ZMod 2) G U)
    (U₁ U₂ : Subrepresentation ρ) (X : Submodule (ZMod 2) U)
    (K₁ K₂ L₀ Lplus : Subgroup G) (s : U ≃ₗ[ZMod 2] U)
    (hsum : U₁.toSubmodule ⊔ U₂.toSubmodule = ⊤)
    (hseed : X ≠ ⊥) (hgen : subspaceCommutator ρ X Lplus = X)
    (hL : Lplus ≤ K₁ ⊔ K₂)
    (h₁ : U₂.toSubmodule ≤ fixedSpace ρ K₁)
    (h₂ : U₁.toSubmodule ≤ fixedSpace ρ K₂)
    (hseed_swap : X.map s.toLinearMap = X)
    (hswap : U₂.toSubmodule.map s.toLinearMap ≤ U₁.toSubmodule)
    (hcoset : Lplus ≤ L₀ ⊔ K₂) (hfix : X ≤ fixedSpace ρ L₀) : False := by
  have hne := seed_quotient_ne_bot ρ U₁.toSubmodule U₂.toSubmodule X K₁ K₂ Lplus s
    hseed hgen hL h₁ h₂ hseed_swap hswap
  apply hne
  have hle := seed_le_of_factor_cosets ρ U₂ X L₀ Lplus K₂ hcoset hfix
    (factor_trivial_on_quotient_of_sum ρ U₁ U₂ K₂ hsum h₂) hgen
  apply le_antisymm _ bot_le
  rintro _ ⟨x, hx, rfl⟩
  exact (Submodule.Quotient.mk_eq_zero U₂.toSubmodule).mpr (hle hx)
/-- Equality of actual projected subgroup images gives the equality of
cosets used for the marked diagonal subgroups. The kernel is the other factor. -/
theorem join_kernel_eq_of_projected_images {P : Type*} [Group P]
    (f : G →* P) (L₀ Lplus : Subgroup G)
    (himage : L₀.map f = Lplus.map f) : L₀ ⊔ f.ker = Lplus ⊔ f.ker := by
  have he := congrArg (fun A : Subgroup P => A.comap f) himage
  simpa only [Subgroup.comap_map_eq] using he

/-- Apply the sum obstruction to actual factor projections and marked subgroup
images. This constructs the coset compatibility from group homomorphisms. -/
theorem not_sum_of_projected_markings {P : Type*} [Group P]
    (ρ : Representation (ZMod 2) G U)
    (U₁ U₂ : Subrepresentation ρ) (X : Submodule (ZMod 2) U)
    (K₁ K₂ L₀ Lplus : Subgroup G) (s : U ≃ₗ[ZMod 2] U)
    (hsum : U₁.toSubmodule ⊔ U₂.toSubmodule = ⊤)
    (hseed : X ≠ ⊥) (hgen : subspaceCommutator ρ X Lplus = X)
    (hL : Lplus ≤ K₁ ⊔ K₂)
    (h₁ : U₂.toSubmodule ≤ fixedSpace ρ K₁)
    (h₂ : U₁.toSubmodule ≤ fixedSpace ρ K₂)
    (hseed_swap : X.map s.toLinearMap = X)
    (hswap : U₂.toSubmodule.map s.toLinearMap ≤ U₁.toSubmodule)
    (f : G →* P) (hker : f.ker = K₂) (himage : L₀.map f = Lplus.map f)
    (hfix : X ≤ fixedSpace ρ L₀) : False := by
  have he := join_kernel_eq_of_projected_images f L₀ Lplus himage
  rw [hker] at he
  apply not_sum_of_diagonal_seed ρ U₁ U₂ X K₁ K₂ L₀ Lplus s
    hsum hseed hgen hL h₁ h₂ hseed_swap hswap _ hfix
  rw [he]
  exact le_sup_left
end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo

end
