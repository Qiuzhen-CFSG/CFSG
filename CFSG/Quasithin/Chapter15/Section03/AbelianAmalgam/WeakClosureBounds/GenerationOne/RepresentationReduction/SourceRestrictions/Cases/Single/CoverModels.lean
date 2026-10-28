module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.LocalSetup
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.CentralComparison
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.CoverModels.Preparation
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.CoverModels.Kernel
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.CoverModels.Models
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.CoverModels.RankOne

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.CoverModels.Source

/-!
# Lifting the single-component source models to the actual actor

Preparation proves relative normality, quasisimplicity, the canonical
K/O₂(K) identification, SQTK of H/O₂(H), the literal Sylow image, and its
two-group quotient above the component. CentralCollapse proves that the
actor center is trivial in every E.2.2 branch, hence J=O₂(H).

The PSL₂ and Suzuki branches use cyclic odd Sylow subgroups and central
transfer, allowing the exceptional Suzuki two-cover before the local two-core
condition excludes it. For PSU₃, the large-prime bound on the literal perfect
cover and the original three-prime overlap kill the full center. The rank-two
branches use SL₃ universality and the proved Sp₄ universal kernel calculation.
No centerlessness, splitting or model-exclusion premise is added to LocalInput.

Source exposes the canonical component and model equivalences with their
quotient equations. source_models gives the marked Bender or rank-two actor,
preserving PSU₃, the actual Borel, standard parabolics and the inducing
T-element. The independent parent retains the final representation case split
and module-coordinate alignment.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), E.2.2,
printed pp.215--216; I.1.1--4, pp.407--408; and 15.3.65, p.1152.
-/
