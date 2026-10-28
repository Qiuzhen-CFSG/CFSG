module
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.Quotient
public import Theory.Representation.BinaryOffender.QuadraticImageBound
public import Theory.GroupTheory.PResidual.Quotient

/-!
# Two-cores and residuals of actual irreducible binary actions

The faithful image of an irreducible binary action has trivial two-core.
If the two-residual acts trivially, that image is a two-group, hence trivial.
Thus every nontrivial irreducible binary action detects the two-residual.
The proof uses the literal image and kernel, without a constituent model.
Source application: Aschbacher–Smith D.1.3, printed p.173.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative ENNReal
namespace Representation.BinaryOffender
variable {H W : Type*} [Group H] [Finite H]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
theorem irreducible_image_twoCore_eq_bot
    (ρ : Representation (ZMod 2) H W) [IsIrreducible ρ] :
    pCore 2 (actionImage ρ) = ⊥ := by
  let : IsIrreducible (imageRepresentation ρ) :=
    (irreducible_comp_surjective_iff (actionHom ρ)
      ρ.asGroupHom.rangeRestrict_surjective (imageRepresentation ρ)).mp (by
        have he : (imageRepresentation ρ).comp (actionHom ρ) = ρ := by ext g w; rfl
        rw [he]
        infer_instance)
  exact bot_unique ((normal_p_subgroup_le_ker (imageRepresentation ρ) _ pCore_isPGroup).trans
    ((MonoidHom.ker_eq_bot_iff _).mpr (imageRepresentation_injective ρ)).le)

theorem irreducible_residual_not_le_ker
    (ρ : Representation (ZMod 2) H W) [IsIrreducible ρ]
    (hn : ∃ h w, ρ h w ≠ w) : ¬ pResidual 2 H ≤ ρ.ker := by
  intro hk
  have hp : IsPGroup 2 (H ⧸ ρ.ker) := (pResidual_le_iff_isPGroup_quotient 2 _).mp hk
  let f := actionHom ρ
  have hkf : f.ker = ρ.ker := actionHom_ker_eq ρ
  have hi : IsPGroup 2 (actionImage ρ) := by
    have hp' : IsPGroup 2 (H ⧸ f.ker) := hp.of_equiv (QuotientGroup.quotientMulEquivOfEq hkf.symm)
    exact hp'.of_equiv (QuotientGroup.quotientKerEquivOfSurjective f ρ.asGroupHom.rangeRestrict_surjective)
  have ht : (⊤ : Subgroup (actionImage ρ)) ≤ pCore 2 (actionImage ρ) :=
    le_sSup ⟨inferInstance,hi.to_subgroup ⊤⟩
  rw [irreducible_image_twoCore_eq_bot ρ] at ht
  obtain ⟨h,w,hn⟩ := hn
  have he : f h = 1 := ht (mem_top _)
  exact hn ((actionHom_eq_one_iff ρ h).mp he w)

end Representation.BinaryOffender
