module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Inputs
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Exceptional.G2
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Exceptional.Triality
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Exceptional.Ree
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Exceptional.Tits

/-!
# Exceptional rank-two fixed-component inspection

The four genuine model branches reduce to their precise remaining intrinsic
facts. The G₂ inner case, whole smaller G₂ fixed models, triality order-360
obstruction, full linear Ree parabolic, and both binary Ree/Tits parabolic
obstructions are proved in the descendants. The original simple and perfect
instances transfer through the actual model equivalences, in every universe.

This is a conditional assembly. Outer fixed-group descent and coverage,
triality inner geometry and smaller-carrier simplicity, the full Suzuki Ree
projection, and Tits fixed-parabolic containment still need their existing
owners. Until those inputs are discharged, `ExceptionalInspection` remains
unproved. The parent `RankTwo` assembly and its shared leaves are unchanged.

Source: Aschbacher–Smith Theorem C and A.2.4, printed p.33; E.6.23,
p.254; and 16.1.4, p.1171, `refs/quasithin.pdf`.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo
universe u

/-- Assembly on actual carriers, preserving the original contract's universe.
The displayed model facts are still outstanding obligations of this task. -/
theorem exceptionalInspection_of_model_facts
    (hg2 : Exceptional.G2.OuterFixedModels)
    (htinner : Exceptional.Triality.InnerFixedRank)
    (htouter : Exceptional.Triality.OuterFixedModels)
    (htsmall : ∀ (m : ℕ) (hm : 0 < m),
      IsSimpleGroup (_root_.Triality.Standard.BinaryCarrier m hm))
    (hrinner : ∀ (m : ℕ), 1 ≤ m →
      IsSimpleGroup (ReeF4.Model m) → Group.IsPerfect (ReeF4.Model m) →
      ∀ a : MulAut (ReeF4.Model m), orderOf a = 2 →
        ∃ x : ReeF4.Model m, a = MulAut.conj x)
    (hrprojection : ∀ (m : ℕ), 1 ≤ m →
      IsSimpleGroup (ReeF4.Model m) → Group.IsPerfect (ReeF4.Model m) →
      ∃ π : ReeF4.ConverseParabolics.parabolic m .suzuki →*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m × (ReeF4.CoefficientField m)ˣ,
        IsPGroup 2 π.ker)
    (htits : Exceptional.Tits.FixedParabolics) : ExceptionalInspection.{u} := by
  intro D _ _ _ _ hD
  rcases hD with hg | ht | hr | hi
  · obtain ⟨n, hn, F, _, _, hc, ⟨e⟩⟩ := hg
    exact ExcludesFixedSix.of_equiv e
      (Exceptional.G2.excludesFixedSix_of_outerFixedModels hg2 F hn hc)
  · obtain ⟨n, hn, h⟩ := ht
    obtain ⟨e⟩ := (_root_.Triality.Standard.isTrialityGroupAt_binary_iff D n hn).mp h
    let : IsSimpleGroup (_root_.Triality.Standard.BinaryCarrier n hn) :=
      e.symm.isSimpleGroup
    let : Group.IsPerfect (_root_.Triality.Standard.BinaryCarrier n hn) :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    exact ExcludesFixedSix.of_equiv e
      (Exceptional.Triality.excludesFixedSix_of_involution_data
        htinner htouter htsmall n hn)
  · obtain ⟨m, hm, ⟨e⟩⟩ := hr
    let : IsSimpleGroup (ReeF4.Model m) := e.symm.isSimpleGroup
    let : Group.IsPerfect (ReeF4.Model m) :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    obtain ⟨π, hk⟩ := hrprojection m hm inferInstance inferInstance
    exact ExcludesFixedSix.of_equiv e
      (Exceptional.Ree.excludesFixedSix_of_inner_and_projection hm
        (hrinner m hm inferInstance inferInstance) π hk)
  · obtain ⟨e⟩ := hi
    exact ExcludesFixedSix.of_equiv e
      (Exceptional.Tits.excludesFixedSix_of_fixedParabolics htits)

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo
