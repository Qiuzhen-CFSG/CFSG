module

public import Theory.SpecificGroups.ReeTwo.ParabolicConcreteCore
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# The full-Ree core is not contained in the two-residual

The binary core character extends to the entire first parabolic and is
nontrivial on source root v5. Its kernel has two-group quotient, so it
contains the actual two-residual and excludes v5. Thus the full core QH
is not contained in O²(H).

This is a further quotient-convention correction for Aschbacher--Smith,
Lemma 14.2.21, printed p.989: in the full-Ree case K/Q must mean the image
of K in H/Q, not a quotient whose denominator is silently assumed contained
in K. The equality of residual images under surjections is provided by
Subgroup.map_pResidual_of_surjective. This obstruction concerns that local
notation, not the final ambient rigidity theorem.

The character and its compatibility with the actual first parabolic use
the verified Shinoda (1975) root model and marked comparison.
-/

namespace ReeTwo.ParabolicConcrete
open Subgroup

/-- The actual source root v5 lies outside the full-Ree parabolic's two-residual. -/
public theorem ree_root_five_not_mem_twoResidual : reeCoreMap (Core.root 2) ∉
    pResidual 2 Tits.ExceptionalParabolics.FullRee.first := by
  let χ := Centralizer.coreCharacter.comp
    ParabolicMarkedComparison.Verified.firstEquiv.symm.toMonoidHom
  have hC : IsPGroup 2 (FiveFour.Cyclic 2) := by
    apply IsPGroup.of_card (n := 1)
    change Nat.card (ZMod 2) = 2 ^ 1
    simp
  have hk : pResidual 2 Tits.ExceptionalParabolics.FullRee.first ≤ χ.ker :=
    sInf_le ⟨inferInstance, (hC.to_subgroup χ.range).of_equiv
      (QuotientGroup.quotientKerEquivRange χ).symm⟩
  intro hx
  have he := hk hx
  change χ (reeCoreMap (Core.root 2)) = 1 at he
  change Centralizer.coreCharacter (ParabolicMarkedComparison.Verified.firstEquiv.symm
    (ParabolicMarkedComparison.Verified.firstEquiv
      (SemidirectProduct.inl (Core.root 2)))) = 1 at he
  rw [MulEquiv.symm_apply_apply, Centralizer.IndexTwo.coreCharacter_inl] at he
  exact (by decide +kernel : Core.binaryCharacter (Core.root 2) ≠ 1) he

/-- In particular the whole two-core cannot be used as a denominator in O²(H). -/
public theorem ree_core_not_le_twoResidual : ¬ reeQ ≤ pResidual 2 Tits.ExceptionalParabolics.FullRee.first := by
  intro h
  apply ree_root_five_not_mem_twoResidual
  apply h
  rw [← reeCoreMap_range]
  exact ⟨Core.root 2, rfl⟩

end ReeTwo.ParabolicConcrete
