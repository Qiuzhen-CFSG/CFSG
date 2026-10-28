module

public import CFSG.Quasithin.ChapterH.Section10To12.Defs

/-!
# The ambient-action construction needed for H.11

The residual module equivalence identifies only the action of M₁₂. To use
outer involutions, one must extend that action to the actual automorphism
group and identify the given ambient action with a subgroup of this extension.
The record below specifies that construction, including the original residual
marking and the original module equivalence. Its existence is a separate
obligation; it is not included in `M12ModuleInput` or asserted here.

This interface permits the construction and the conditional local calculations
to be developed independently. The final H.11 assembly must construct it.
Source: Aschbacher–Smith H.11.1, printed pp.392–393, combined manuscript
of 1 March 2004.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterH.Section10To12.M12Calculations

/-- An actual extension of the native heart action, with the given ambient
group and its residual marking identified equivariantly. -/
structure AmbientExtension {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (h : M12ModuleInput ρ) where
  automorphismRepresentation : Representation (ZMod 2) (MulAut Sporadic.Mathieu.M12) M12Heart
  automorphismRepresentation_faithful : Function.Injective automorphismRepresentation
  inner_action : automorphismRepresentation.comp MulAut.conj = m12HeartRepresentation
  embedding : G →* MulAut Sporadic.Mathieu.M12
  embedding_injective : Function.Injective embedding
  embedding_residual : ∀ t : Subgroup.solvableResidual G,
    embedding (t : G) = MulAut.conj (h.residualEquiv t)
  equivariant : ∀ (g : G) (v : V),
    h.moduleEquiv.toLinearEquiv (ρ g v) =
      automorphismRepresentation (embedding g) (h.moduleEquiv.toLinearEquiv v)

end CFSG.Quasithin.ChapterH.Section10To12.M12Calculations
