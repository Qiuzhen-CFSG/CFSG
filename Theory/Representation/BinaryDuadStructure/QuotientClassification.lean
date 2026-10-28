module

public import Theory.Representation.BinaryDuadStructure.NaturalCover
public import Theory.Representation.FirstCohomologyDuality.SimpleCover

/-!
# Nonzero quotients of the five-dimensional duad cover

The natural module is irreducible. An invariant subspace of its perfect
central cover either maps onto the natural module and is the whole cover,
or lies in the one-dimensional kernel. Thus all nonzero equivariant quotients
are genuinely isomorphic to the marked natural module or its cover.
The target representation need not be faithful, irreducible, or given
finite-dimensionality.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), G.5.3,
printed pp.343–345 (PDF pp.354–356).
-/

@[expose] public section

open Theory.SpecificGroups.SymmetricSix BinaryPermutation BinaryDuadModule
namespace BinaryDuadStructure

/-- The five-dimensional line quotient has exactly its central line as a
proper nonzero invariant subspace. -/
theorem lineQuotient_subrepresentation_cases (S : Subrepresentation lineQuotientAction) :
    S = ⊥ ∨ S = naturalProjectionHom.ker ∨ S = ⊤ := by
  let N : Subrepresentation alternatingNaturalAction := {
    toSubmodule := S.toSubmodule.map naturalProjection
    apply_mem_toSubmodule g := by
      rintro _ ⟨q, hq, rfl⟩
      exact ⟨lineQuotientAction g q, S.apply_mem_toSubmodule g hq,
        naturalProjection_equivariant g q⟩ }
  let := alternatingNaturalAction_irreducible
  rcases eq_bot_or_eq_top N with hN | hN
  · have hle : S.toSubmodule ≤ naturalProjection.ker := by
      intro q hq
      have hp : naturalProjection q ∈ N := ⟨q, hq, rfl⟩
      rw [hN] at hp
      exact hp
    by_cases hS : S = ⊥
    · exact Or.inl hS
    right; left
    apply Subrepresentation.toSubmodule_injective
    have hpos : 0 < Module.finrank (ZMod 2) S.toSubmodule := by
      by_contra hh
      apply hS
      apply Subrepresentation.toSubmodule_injective
      exact Submodule.finrank_eq_zero.mp (by omega)
    have hmono := Submodule.finrank_mono hle
    rw [naturalProjection_ker_finrank] at hmono
    apply Submodule.eq_of_le_of_finrank_eq hle
    rw [naturalProjection_ker_finrank]
    omega
  · right; right
    apply Subrepresentation.toSubmodule_injective
    apply Representation.OneCohomology.invariant_eq_top_of_cover_image_eq_top
      naturalProjectionHom naturalProjection_isCover S.toSubmodule
      (fun g _ hq => S.apply_mem_toSubmodule g hq)
    exact congrArg Subrepresentation.toSubmodule hN

/-- Every nonzero equivariant quotient is the marked natural module or this cover.
There is no faithfulness or irreducibility premise on the target. -/
theorem nonzero_quotient_alternatives {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [Nontrivial W] (ρ : Representation (ZMod 2) A6 W)
    (f : lineQuotientAction.IntertwiningMap ρ) (hf : Function.Surjective f) :
    Nonempty (Representation.Equiv alternatingNaturalAction ρ) ∨ Nonempty (lineQuotientAction.Equiv ρ) := by
  rcases lineQuotient_subrepresentation_cases f.ker with hk | hk | hk
  · right
    exact ⟨f.ofBijective ⟨LinearMap.ker_eq_bot.mp (congrArg Subrepresentation.toSubmodule hk), hf⟩⟩
  · left
    have hker : f.toLinearMap.ker = naturalProjection.ker :=
      congrArg Subrepresentation.toSubmodule hk
    let E : NaturalModule ≃ₗ[ZMod 2] W :=
      (naturalProjection.quotKerEquivOfSurjective naturalProjection_surjective).symm.trans
        ((Submodule.quotEquivOfEq _ _ hker.symm).trans
          (f.toLinearMap.quotKerEquivOfSurjective hf))
    have he (q : LineQuotient) : E (naturalProjection q) = f q := by
      simp only [E, LinearEquiv.trans_apply, LinearMap.quotKerEquivOfSurjective_symm_apply,
        Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]
      rfl
    refine ⟨Representation.Equiv.mk E (fun g => LinearMap.ext (fun v => ?_))⟩
    obtain ⟨q, rfl⟩ := naturalProjection_surjective v
    change E (alternatingNaturalAction g (naturalProjection q)) = ρ g (E (naturalProjection q))
    rw [← naturalProjection_equivariant, he, he, f.isIntertwining]
  · exfalso
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    obtain ⟨q, rfl⟩ := hf w
    apply hw
    exact (show q ∈ f.ker from hk ▸ (show q ∈ (⊤ : Subrepresentation lineQuotientAction) from
      Submodule.mem_top))

end BinaryDuadStructure
