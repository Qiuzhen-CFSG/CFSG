module

public import Theory.Mathieu.M24.ValueBoundParabolics.CentralCover
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.Quotient
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Faithful irreducible binary actions of central covers of M₂₄

The normal two-core acts trivially on an irreducible binary module. A faithful
action therefore has trivial two-core, and the established perfect central
cover theorem for the actual Witt-design M₂₄ gives trivial center. The original
central quotient map is thus an isomorphism. Pullback along its inverse retains
the original vector space and the literal action of every original element.

This supplies the cover reduction for Guralnick--Malle, Classification of
2F-modules I, Proposition 5.1, M₂₄ paragraph, author manuscript p.17.
-/

public section
namespace Representation.MathieuM24Degree44
open Subgroup Theory.GroupTheory Sporadic.Mathieu BinaryOffender
variable {L V : Type*} [Group L] [Finite L] [IsQuasisimple L]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) L V)

/-- Faithfulness and irreducibility remove the center of an arbitrary M₂₄ cover. -/
theorem center_eq_bot (hf : Function.Injective ρ) (hi : ρ.IsIrreducible)
    (e : L ⧸ center L ≃* M24) : center L = ⊥ := by
  let : ρ.IsIrreducible := hi
  have hcore : pCore 2 L = ⊥ := by
    apply le_bot_iff.mp
    exact (normal_p_subgroup_le_ker ρ (pCore 2 L) pCore_isPGroup).trans
      ((MonoidHom.ker_eq_bot_iff ρ).mpr hf).le
  exact M24ValueBoundParabolics.center_eq_bot_of_twoCore_eq_bot hcore e

/-- The literal specified central quotient map becomes an isomorphism. -/
@[expose] noncomputable def modelEquiv (hf : Function.Injective ρ) (hi : ρ.IsIrreducible)
    (e : L ⧸ center L ≃* M24) : L ≃* M24 :=
  (MulEquiv.ofBijective (QuotientGroup.mk' (center L))
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by
      rw [QuotientGroup.ker_mk', center_eq_bot ρ hf hi e]),
      QuotientGroup.mk'_surjective (center L)⟩).trans e

/-- The isomorphism is the given quotient map, with no change of marking. -/
theorem modelEquiv_apply (hf : Function.Injective ρ) (hi : ρ.IsIrreducible)
    (e : L ⧸ center L ≃* M24) (g : L) :
    modelEquiv ρ hf hi e g = e (QuotientGroup.mk' (center L) g) := rfl

omit [Finite L] [IsQuasisimple L] in
/-- Pullback through any group isomorphism preserves the literal cyclic displacement. -/
theorem fixedCodim_comp_equiv_symm {H : Type*} [Group H] (e : L ≃* H) (t : L) :
    fixedCodim (ρ.comp e.symm.toMonoidHom) (zpowers (e t)) = fixedCodim ρ (zpowers t) := by
  rw [fixedCodim_zpowers_eq_displacement_rank, fixedCodim_zpowers_eq_displacement_rank]
  exact congrArg (fun f : Module.End (ZMod 2) V =>
    Module.finrank (ZMod 2) (LinearMap.range (f - LinearMap.id)))
    (show (ρ.comp e.symm.toMonoidHom) (e t) = ρ t from congrArg ρ (e.symm_apply_apply t))

end Representation.MathieuM24Degree44
