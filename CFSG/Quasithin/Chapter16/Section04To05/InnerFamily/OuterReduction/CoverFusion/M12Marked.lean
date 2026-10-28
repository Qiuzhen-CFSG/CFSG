module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.CoverFusion.Reduction
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.CoverFusion.M12Marked.Separation
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.CoverFusion.M12Marked.Construction

/-!
# Marked M₁₂ quotient fusion for the double-cover argument

The model separations are unconditional. From the exact earlier 16.1.5(4)
table, the construction supplies a two-central involution in the actual
O²(C_M₁₂(b)). The remaining 192-element centralizer calculation then supplies
l with b(l)l⁻¹ = v, retaining both the residual membership and the mark.

The local calculation remains an explicit proof obligation in this module;
this conditional assembly is not a completed M₁₂ case of 16.4.9(2).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.5(4), printed p.1171; proof of 16.4.9(2), pp.1190–1191;
the use of the two-central mark in the cover is I.2.2(5a), p.409.
-/

public section
open Sporadic.Mathieu
namespace CFSG.Quasithin.Chapter16.Intersections.OuterReduction.CoverFusion
open OtherPreliminaries.Mathieu

/-- Assemble the literal marked-fusion witness from the remaining local
calculation and the permitted earlier source table. -/
theorem m12_twoCentralResidualFusion_of_centralizerDisplacement
    (table : ∀ r : MulAut M12, orderOf r = 2 → M12InvolutionAlternative r)
    (hlocal : M12CentralizerDisplacement)
    (b : MulAut M12) (hb : orderOf b = 2) (hout : ¬ ∃ s : M12, b = MulAut.conj s) :
    TwoCentralResidualFusion b := by
  obtain ⟨v, hv, hv2, hvC, ⟨g, hg⟩, hc⟩ := m12_marked_residual_involution table b hb hout
  obtain ⟨l, hl⟩ := m12_conjugator_of_centralizerDisplacement hlocal b
    (by simpa only [hb] using pow_orderOf_eq_one b) v hc g hg
  exact ⟨l, v, hv, hv2, hvC, hl⟩

end CFSG.Quasithin.Chapter16.Intersections.OuterReduction.CoverFusion
