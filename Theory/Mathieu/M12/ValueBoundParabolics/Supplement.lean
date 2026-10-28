module
public import Theory.Mathieu.M12.Properties.SylowAutomorphisms
public import Theory.Mathieu.M12.Properties.SylowAutomorphismGroup
public import Theory.GroupTheory.SylowOuterAutomorphisms
public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup

/-!
# Sylow supplements of a normal M₁₂

The intrinsic automorphism calculations imply that Out(M₁₂) is a two-group.
For a normal copy L of M₁₂ with trivial ambient centralizer, conjugation
embeds G/L in Out(L). The quotient is therefore a two-group, and every
Sylow two-subgroup of G supplements L.

Source: the condition G = LT needed to apply Aschbacher–Smith E.4.2 in
E.4.3(1), printed p.241 (PDF p.252). The actual equivalence L ≃ M₁₂ and
triviality of C_G(L) are hypotheses here, to be discharged by the source
central-cover reduction.
-/

public section
open Subgroup
namespace Sporadic.Mathieu.M12SmallPair.ValueBoundParabolics

theorem outer_isPGroup_two : IsPGroup 2 (MulAut.Outer M12) := by
  apply MulAut.isPGroup_outer_of_sylow_aut commonSylow SylowAutomorphismGroup.isPGroup_two
  intro a ha
  rcases SylowAutomorphisms.eq_one_or_conj_of_fixes_sylow a ha with rfl | rfl
  · exact (MulAut.innerSubgroup M12).one_mem
  · exact ⟨z, rfl⟩

/-- A normal M₁₂ with trivial ambient centralizer supplements every Sylow
two-subgroup. Triviality of that centralizer remains an explicit input. -/
theorem sup_sylow_eq_top_of_equiv {G : Type*} [Group G] [Finite G]
    (L : Subgroup G) [L.Normal] (e : L ≃* M12)
    (hC : centralizer (L : Set G) = ⊥) (T : Sylow 2 G) :
    L ⊔ (T : Subgroup G) = ⊤ := by
  have hO : IsPGroup 2 (MulAut.Outer L) :=
    outer_isPGroup_two.of_injective (MulAut.outerCongr e).toMonoidHom
      (MulAut.outerCongr e).injective
  have hQ : IsPGroup 2 (G ⧸ L) :=
    hO.of_injective (MulAut.outerAction L) (MulAut.outerAction_injective L hC)
  simpa only [sup_comm] using T.sup_eq_top_of_quotient_isPGroup L hQ

end Sporadic.Mathieu.M12SmallPair.ValueBoundParabolics
