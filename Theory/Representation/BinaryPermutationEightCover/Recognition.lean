module
public import Theory.Representation.BinaryPermutationEightCover

/-!
# Recognizing the nontrivial central cover of the natural A₈ module

The universal augmentation cover maps onto every perfect central cover of
A₈'s six-dimensional natural module. If the latter projection has nonzero
kernel, dimension bounds force that map to be an isomorphism. The resulting
coordinates preserve both the supplied actor marking and the original
projection, including the constant line.

Source: Aschbacher–Smith I.1.5–6, printed p.408, and the augmentation-core
step in Lemma 12.3.3, printed p.808.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace BinaryPermutation.EightCover
variable {G U : Type*} [Group G] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]

theorem core_equiv_of_marked_cover
    (ρ : Representation (ZMod 2) G U) (B : Subgroup G)
    (e : B ≃* alternatingGroup (Fin 8))
    (p : U →ₗ[ZMod 2] natural (Fin 8))
    (hp : ∀ b : B, ∀ u, p (ρ b.val u) =
      alternatingNaturalRepresentation (Fin 8) (e b) (p u))
    (hsur : Function.Surjective p)
    (hker : p.ker ≤ fixedSpace ρ B)
    (hgen : subspaceCommutator ρ ⊤ B = ⊤)
    (hn : ¬ Function.Injective p) :
    ∃ E : U ≃ₗ[ZMod 2] core (Fin 8),
      (∀ b : B, ∀ u, E (ρ b.val u) =
        alternatingCoreRepresentation (Fin 8) (e b) (E u)) ∧
      ∀ u, coreToNatural (Fin 8) (E u) = p u := by
  obtain ⟨f,hf,ha,hq⟩ := core_quotient_of_marked_cover ρ B e p hp hsur hker hgen
  have hlo := LinearMap.finrank_le_finrank_of_surjective hsur
  have hhi := LinearMap.finrank_le_finrank_of_surjective hf
  have hnat : Module.finrank (ZMod 2) (natural (Fin 8)) = 6 := by
    simpa using finrank_natural_even (Fin 8) (by decide)
  have hcore : Module.finrank (ZMod 2) (core (Fin 8)) = 7 := by
    simpa using finrank_core (Fin 8)
  have hne : Module.finrank (ZMod 2) U ≠ 6 := by
    intro hd
    exact hn ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (hd.trans hnat.symm)).mpr hsur)
  have hd : Module.finrank (ZMod 2) (core (Fin 8)) = Module.finrank (ZMod 2) U := by
    rw [hnat] at hlo
    rw [hcore] at hhi ⊢
    omega
  let F := LinearEquiv.ofBijective f
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr hf,hf⟩
  refine ⟨F.symm,?_,?_⟩
  · intro b u
    apply F.injective
    rw [F.apply_symm_apply]
    exact ((ha b (F.symm u)).trans (congrArg (ρ b.val) (F.apply_symm_apply u))).symm
  · intro u
    exact (hq (F.symm u)).symm.trans (congrArg p (F.apply_symm_apply u))

end BinaryPermutation.EightCover
