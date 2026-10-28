module

public import Theory.Representation.Mathieu.SmallModules.M12Recognition.Completeness
public import Theory.Mathieu.M12.ValueBoundParabolics.CentralCovers
public import Theory.Representation.NormalPSubgroupKernel

/-!
# Recognition through a marked M₁₂ central quotient

A faithful irreducible binary representation kills the two-core. The proved
central-cover theorem for M₁₂ then makes the center trivial. Composing the
inverse of this quotient isomorphism with the supplied marking identifies
the covering group itself with M₁₂. In degree at most ten, small-module
recognition supplies an equivariant equivalence with the permutation heart,
preserving that exact marking.

This is the cover and transport step in Aschbacher--Smith K.4, printed
pp.457--460 (1 March 2004 manuscript). It does not prove the degree bound
deduced there from Guralnick--Malle, Theorem 6.6 and Table 6.7.
-/

public section
namespace Representation.MathieuSmall.M12Recognition.CentralCover
open Subgroup Theory.GroupTheory Sporadic.Mathieu

variable {L V : Type*} [Group L] [Finite L] [IsQuasisimple L]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (σ : Representation (ZMod 2) L V)

/-- Faithful irreducible binary M₁₂ covers have trivial center. -/
theorem center_eq_bot (hf : Function.Injective σ) (hi : σ.IsIrreducible)
    (e : (L ⧸ center L) ≃* M12) : center L = ⊥ := by
  let := hi
  have hcore : pCore 2 L = ⊥ := by
    exact le_bot_iff.mp ((normal_p_subgroup_le_ker σ (pCore 2 L)
      (pCore_isPGroup (p := 2))).trans ((MonoidHom.ker_eq_bot_iff σ).mpr hf).le)
  exact M12SmallPair.ValueBoundParabolics.CentralCovers.center_eq_bot hcore e

/-- The group identification induced by the literal central-quotient marking. -/
noncomputable def groupEquiv (hf : Function.Injective σ) (hi : σ.IsIrreducible)
    (e : (L ⧸ center L) ≃* M12) : L ≃* M12 :=
  ((QuotientGroup.quotientMulEquivOfEq (center_eq_bot σ hf hi e)).trans
    QuotientGroup.quotientBot).symm.trans e

/-- No automorphism or change of marking is inserted in the cover reduction. -/
theorem groupEquiv_apply (hf : Function.Injective σ) (hi : σ.IsIrreducible)
    (e : (L ⧸ center L) ≃* M12) (l : L) :
    groupEquiv σ hf hi e l = e (QuotientGroup.mk' (center L) l) := by
  apply congrArg e
  rfl

/-- Small-module recognition for arbitrary central covers, with the original
central quotient marking. The degree bound remains an explicit hypothesis. -/
theorem equiv_heart_of_finrank_le_ten
    (hf : Function.Injective σ) (hi : σ.IsIrreducible)
    (e : (L ⧸ center L) ≃* M12) (hd : Module.finrank (ZMod 2) V ≤ 10) :
    Nonempty (σ.Equiv (m12HeartRepresentation.comp
      (groupEquiv σ hf hi e).toMonoidHom)) := by
  let f := groupEquiv σ hf hi e
  obtain ⟨E⟩ := equiv_heart_of_faithful_finrank_le_ten
    (σ.comp f.symm.toMonoidHom) (hf.comp f.symm.injective) hd
  refine ⟨{ toLinearEquiv := E.toLinearEquiv, isIntertwining' := ?_ }⟩
  intro l
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply] using E.isIntertwining' (f l)

end Representation.MathieuSmall.M12Recognition.CentralCover
