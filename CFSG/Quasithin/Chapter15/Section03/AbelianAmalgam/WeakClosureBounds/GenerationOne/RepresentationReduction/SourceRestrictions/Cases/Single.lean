module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.LocalSetup
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.OrbitTransport
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.ClassificationInputs

/-!
# Preparation of the single-component module deduction

The generic section theorems apply to the literal local action D=H/O₂(H)
on V=U/Z, U=⟨ZS^H⟩. `LocalInput` records that specialization, the selected
T-homogeneous Irr⁺ section, K=K₀, the genuine E.2.2 reduction, the odd
exponent f>1, and the quadratic bound. It contains no module classification,
FF exclusion, fixation or contradiction premise.

The proved comparison identifies the component modulo its center with
its E.2.2 image in H/J and transports the overlap by the same map.
The proved orbit construction turns a constituent identification and an
actual two-summand quotient-image equality into a central-quotient product
identification, twisted by the automorphism induced by the given T element.
The section-action construction verifies the B.4 hypotheses on the literal
faithful image, subject to the explicitly listed structural inputs.

The deduction of the two final single-component cases remains open.
`ClassificationInputs` retains the existing complete F.9.18(4) output: the preliminary
component list (Bender, L₃, Sp₄′, G₂′, L₄(2), L₅(2), A₇ excluding its
triple cover, M₂₂ and its triple cover) and all three branches: H-invariance,
the invariant FF case, and the inequivalent two-constituent case with every
one of its SL₃/Sp₄/A₆/L₄(2)/L₅(2)/four-dimensional-A₇ alternatives.
No alternative is removed from this input contract.

Complete conditional B.4.2 and B.4.5 interfaces already exist in
`Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.SourceB42`
and `Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource`
in Chapter 13 Section 08. Their input hypotheses are `Cases.Ratios`' genuine
B.4 hypotheses. The source proofs remain with the B.4/F.9 owners.

Remaining assembly obligations include the central-cover and parameter
comparisons, elimination of every incompatible B.4/F.9 model, compatible
Borel markings, actual movement of standard parabolics, and exclusion of the paired
alternative in the Bender case to give I=I_T. The whole-space ratio does not
by itself supply a faithful quadratic actor on each section. F.9.18(2--3)'s
common actor and its faithfulness on the component are still required.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.65,
printed p.1152; F.9.18(4), pp.325--326; B.4.2/B.4.5, pp.86--87;
A.1.40--42, pp.31--32.
-/
