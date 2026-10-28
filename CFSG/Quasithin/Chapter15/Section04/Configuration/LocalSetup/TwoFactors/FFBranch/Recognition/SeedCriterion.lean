module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ActionGroup
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.ActionGeometry

/-!
# The Sylow fixed-space test for the remaining module alternatives

If the pointwise stabilizer of a seed subspace is `P`, the pointwise
stabilizer of the entire `P`-fixed space is also `P`. Apply this first to
the genuine quotient action and then to its offender-generated subgroup;
normality ensures that the prescribed Sylow intersection is Sylow there.
Consequently a concrete model is excluded by an element outside that Sylow
subgroup fixing its entire fixed space. The final lemma transports this
obstruction through both an actual group isomorphism and an intertwining
linear equivalence. No module model calculation is assumed or asserted.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, the B.5.6 comparison in Lemma 15.4.18, printed p.1163.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch
variable {H : Type*} [Group H] [Finite H]
variable (P : Sylow 2 H) (Z : Subgroup H)
  [IsElementaryAbelian 2 (moduleClosure Z)]
  (hC : centralizer (Z : Set H) = (P : Subgroup H))

private theorem fixedSpace_kernel_of_seed {D V : Type*} [Group D]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (A : Subgroup D)
    (W : Submodule (ZMod 2) V) (hW : subspaceKernel ρ W ⊤ = A) :
    subspaceKernel ρ (fixedSpace ρ A) ⊤ = A := by
  have hWA : W ≤ fixedSpace ρ A := by
    rw [← hW]
    exact le_fixedSpace_subspaceKernel ρ W ⊤
  apply le_antisymm
  · intro g hg
    rw [← hW]
    exact ⟨mem_top _, fun w hw => hg.2 w (hWA hw)⟩
  · intro g hg
    exact ⟨mem_top _, fun w hw => hw ⟨g, hg⟩⟩

omit [Finite H] in
theorem quotientAction_sylow_fixedSpace_kernel :
    subspaceKernel (quotientAction P Z hC)
      (fixedSpace (quotientAction P Z hC) ((P : Subgroup H).map coreProjection)) ⊤ =
        (P : Subgroup H).map coreProjection :=
  fixedSpace_kernel_of_seed _ _ (seedSubspace Z) (seedSubspace_kernel Z P hC)

omit [Finite H] in
theorem offenderAction_seed_kernel :
    subspaceKernel (offenderAction P Z hC) (seedSubspace Z) ⊤ =
      ((P : Subgroup H).map coreProjection).subgroupOf (offenderGroup P Z hC) := by
  rw [← seedSubspace_kernel Z P hC]
  ext g
  rfl

omit [Finite H] in
theorem offenderAction_sylow_fixedSpace_kernel (S : Subgroup (offenderGroup P Z hC))
    (hS : S = ((P : Subgroup H).map coreProjection).subgroupOf (offenderGroup P Z hC)) :
    subspaceKernel (offenderAction P Z hC) (fixedSpace (offenderAction P Z hC) S) ⊤ = S := by
  apply fixedSpace_kernel_of_seed _ _ (seedSubspace Z)
  exact (offenderAction_seed_kernel P Z hC).trans hS.symm

omit [Finite H] in
theorem offenderAction_no_fixedSpace_enlargement (S : Subgroup (offenderGroup P Z hC))
    (hS : S = ((P : Subgroup H).map coreProjection).subgroupOf (offenderGroup P Z hC))
    (g : offenderGroup P Z hC) (hg : g ∉ S)
    (hfix : ∀ v ∈ fixedSpace (offenderAction P Z hC) S, offenderAction P Z hC g v = v) : False := by
  apply hg
  rw [← offenderAction_sylow_fixedSpace_kernel P Z hC S hS]
  exact ⟨mem_top _, hfix⟩

omit [Finite H] in
theorem offenderAction_no_equivariant_fixedSpace_enlargement
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) D W)
    (S : Subgroup (offenderGroup P Z hC))
    (hS : S = ((P : Subgroup H).map coreProjection).subgroupOf (offenderGroup P Z hC))
    (e : offenderGroup P Z hC ≃* D) (E : Additive (moduleClosure Z) ≃ₗ[ZMod 2] W)
    (hE : ∀ g v, E (offenderAction P Z hC g v) = σ (e g) (E v))
    (d : D) (hd : d ∉ S.map e.toMonoidHom)
    (hfix : ∀ w ∈ fixedSpace σ (S.map e.toMonoidHom), σ d w = w) : False := by
  apply offenderAction_no_fixedSpace_enlargement P Z hC S hS (e.symm d)
  · intro hg
    exact hd (mem_map.mpr ⟨e.symm d, hg, e.apply_symm_apply d⟩)
  · intro v hv
    apply E.injective
    rw [hE, e.apply_symm_apply]
    apply hfix
    rw [← fixedSpace_map_equivariant (offenderAction P Z hC) σ e.toMonoidHom E hE S]
    exact ⟨v, hv, rfl⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch
