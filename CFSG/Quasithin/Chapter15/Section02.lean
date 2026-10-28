module

public import Theory.GroupTheory.InvolutionGeneratedCommutator
public import CFSG.Quasithin.Chapter15.Section02.CriticalPair
public import CFSG.Quasithin.Chapter15.Section02.InvolutionLayers
public import CFSG.Quasithin.Chapter15.Section02.OffenderNormality
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaUniqueness
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaResidualImage
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaFullStructure
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaFullComplete
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaChosenComplete
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaHStarExclusion
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaWreathExclusion
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.CyclicWreathExclusion
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.DihedralCubicExclusion
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveCharacteristic
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFivePushingUp
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveNonquasisimple
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveRankOne
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveLinearThree
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveLinearExclusion
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveComparison
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveMixedPair
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.MarkedFiveCriticalCommuting
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.MarkedFiveMixedDistanceOne
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.MarkedFiveMixedCriticalData
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveFinalExclusion
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.MarkedFiveQuotientExclusions
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.MarkedFiveFinalQuotient
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaResidualStar
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.DistinguishedPlane
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.ResidualKernelAssembly
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.EqualityRowJanko
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.EqualityRowOrdinary.TerminalSource
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.EqualityRowOrdinary.Selection
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.EqualityRowOrdinary.Source
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Index.ComponentEscape
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Index.SimpleComponentEscape
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Index.LinearFourExclusion
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Index.BinaryG2Exclusion
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SourceSmallParabolicResiduals
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallSourceQuotientAssembly
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallSourceFinalQuotients
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.SmallSourceDirect
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SmallActionDischarged
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.ProperThompsonDischarged

/-!
# Finishing the reduction to the orthogonal four-dimensional quotient

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), §15.2, printed pp. 1104--1120. The final contradiction
on p. 1120 completes Theorem 15.1.3, whose alternatives are the rank-two case
with its six group identifications and the natural `O₄⁺(2)` rank-four case.

The original small-action contradiction is now supplied by
`source_chosen_contradiction` from the actual `ChosenSmallSource` and
`SmallSourcePrior`. The original prior contains the preceding global residual
centralization and the two counterexample exclusions. Every H-star wreath
quotient and the entire distinguished-plane uniqueness argument are constructed
internally. `source_smallChosenExclusion` supplies the literal 15.1.3
small-action input for both the full module and its proper chosen support.
The Omega row also has the independent `source_chosen_omega_contradiction`,
which constructs residual uniqueness and the H-star quotients without the
global residual prior. Its literal proper-support application discharges
`SourceProperThompsonImageTwoInput`. The original 15.1.3 endpoint
`source_lemma_15_1_3_of_full_image_gap_and_large_exclusion` therefore retains
only full-module Thompson normalization, rank-two and large-action source
inputs. This module does not assert the full classification.

The imported involution-generated commutator theorem supplies the argument of
Lemma 15.2.28 from its explicit group-theoretic inputs, inside the local group
`H`. Those inputs are furnished by 15.2.11, 15.2.25, and the module cases of
15.2.25.1. The preliminary reductions, uniqueness theorem 15.2.15, and the
weak-closure/coset-graph contradiction are now connected by
`source_chosen_contradiction_of_preceding_residuals`. That source application
retains the two-maximal-overgroup and wreath-quotient results, and the original
15.2.12 residual identity and structural alternatives. This older conditional
endpoint remains available alongside the direct source theorem above.
The stronger `source_chosen_contradiction_of_one_residual_identity` now needs
one actual residual input and its identity; it supplies the common plane,
inverter and Held exclusion internally. The equal-plane case needs no residual
identity, and `source_chosen_marked_five_or_omega_of_mixed_size` excludes the
marked cubic action from the independent mixed-size and original prior inputs.
The remaining residual row has Sz(2) or Omega action and an index-two plane
centralizer. The direct source route now supplies global wreath recognition
and excludes that remaining row.
The exact embedded action-kernel residual containment now feeds
`source_chosen_contradiction_of_action_kernel_residual`; the equality row is
derived internally, while the ambient containment remains explicit.
The actual J₄ fixed-residual terminal step now also avoids the residual identity:
its triple-Mathieu section is excluded directly in Mc in the equality row.
The component and block escape specializations and the original KI/SL₄(2)
terminal exclusion are also exported without a partner residual identity.
The direct residual-input route now supplies escaping Sylow geometry,
the literal 1.1.5 hypotheses, odd-core vanishing and ordinary component
selection. Its even-model reduction and terminal ordinary consumer exclude
the entire minimal ordinary-component escape, constructing the component
and its marked action internally. The full characteristic-two source sieve
reduces to the literal natural/doubled-natural L₃ parabolic and excludes it.
`ResidualInput.plane_uniqueness_direct` combines these two branches, and
`source_chosen_contradiction_of_wreath_quotients` constructs the residual input
and completes the original contradiction without residual-identity premises.
The literal marked-five S3 pair has only distance-one or nonzero
distance-three commuting critical pairs. In the faithful wreath mixed A5
pair, unequal adjacent omega parameters also exclude distance three,
leaving critical distance one. The faithful mixed A₅ pair is now excluded:
its canonical critical edge starts at A₅, the full core product gives
three-walk transitivity, and the Suzuki short-path contradiction closes
the original H-star wreath-five branch in `ChosenSmallSource.HStar_not_wreath_five`.
The same mixed-pair exclusion removes the single S₅ quotient using its
actual two-residual. The original marked-five/S₃ pair is now excluded as
well: the commuting-one alpha obstructions force distance three, while
transported centerlessness contradicts the actual central involution of H
and forces distance one. `HStar_wreath_of_marked_five` therefore completes
marked-five 15.2.8 without a recognition premise. The complete original
mixed A₅/S₃ source now has Sylow order at most 1024: its commuting branch
has Borel core order 64, and the noncommuting commutator pairing bounds
that core by 512. This contradicts the original two-chief-factor lower
bound 2048 in the single-S₅ branch. `ChosenSmallSource.HStar_wreath`
therefore supplies every original small-source H-star quotient with only
the original prior retained, without a mixed-size or recognition input.
The terminal two applications of E.3.6 are now supplied by
`source_critical_pair_false_of_layer_bounds` on the literal conjugate pair;
the direct source assembly constructs that pair and its corank-one bounds.
The original 15.2.28 local inputs now feed that terminal consumer through
`source_critical_pair_false_of_local_data`, which constructs the orbit span
inside `H` and both elementary conjugate-layer bounds in the ambient group.
The quadratic offender-normality argument from 15.2.11 is re-exported through
`source_offender_normalClosure_involution_bound`; the original source assembly
supplies its generation and selection hypotheses.
The Omega preliminary row now proves the literal residual factorization,
normality and star centralization in 15.2.3(2),(4),(5), its commutator image,
and the order-three or order-nine image dichotomy. The latter retains the
earlier chosen-module core noncentrality; its order-nine branch supplies
15.2.3(3) uniqueness. The source residual image is now proved to equal its
commutator with the core image; in the cubic branch that core image has
order two and acts by inversion. In that cubic branch the literal star image
has order three and C_Y(V)=O₂(Y), by the cyclic-kernel transfer argument.
The cubic branch also proves m₃(C_M(V))≤1 and that every Sylow three-subgroup
of M is C₃ × C₃ⁿ for some n≥1. When the chosen V is the full local module,
the Omega Sylow fixed line supplies central-seed order two and the original
core-growth argument discharges noncentrality. The full-module Omega row is now assembled in
`source_omega_full_residual_complete`: all three genuine residual alternatives,
normality, uniqueness, factorization and star centralization are proved on
the original maps. The order-nine branch includes its elementary or
extraspecial quotient, the precise theta identity and core inversion. The
common centralizer rank bound now proves the Omega branch of15.2.4 directly:
the original H-star intersection has three-rank at most one, while the
S₅ wreath C₂ quotient would force rank at least two. This uses the wreath
action on 25 points and requires no elementary-nine star-image construction.
The dihedral source residual image is the actual marked prime kernel, with
order three or five. Its cubic branch now discharges the action-image premise
of the same wreath exclusion. The remaining wreath case is now reduced to the
literal order-five source configuration, with its seed span, movement and
normalizer bounds proved. This configuration also descends through the literal
two-core quotient when both
image parabolics have characteristic two, preserving the local models and
Borel normality. The complementary quotient-image alternative, order five
or A₅, now gives V≤O₂(W) and characteristic two of W directly. Failure of
the component-image parabolic to have characteristic two gives the same
conclusion without identifying its image. The marked-five residual is normal
in M, and the exact C.2.3 radical/normal-closure setup is now proved for every
nontrivial-core generated configuration. The failed-image configuration now also yields a normal component containing
the original five-residual: C.2.5 and the A₅ action calculation exclude its
Sylow branch, and the prime-index argument supplies containment in the other
branch. C.2.6 and the actual A.3.6 Sylow action then force this component's
two-core quotient to be quasisimple. The original A₅ component and its
full Sylow now bound the field degree of both binary rank-one and linear-three
quotient models by two, excluding their degree-divisible-by-four rows. In the
linear-three case the actual component and Sylow lie in a standard parabolic;
its affine Levi projection reduces the bound to the rank-one calculation.
The normalized original five-residual now excludes both linear quotient
families at every field size. Its solvable join with the full Sylow lies in
a Borel, whose order cannot contain a factor five at either remaining degree.
The complete C.2.7/B.5 star catalogue now excludes the failed-image
configuration, including the literal central covers and their solvable
five-free kernels. Thus a nontrivial two-core forces both quotient
parabolics to have characteristic two. The mixed DGS85 exclusion is now
supplied by the original-pair theorem `small_solvable_a5_exclusion` and
applied to both faithful completion cases. The general
chosen-module assembly now discharges core
noncentrality through original14.1.13–14: `source_omega_chosen_residual_complete`
supplies the same complete conclusions for full and proper chosen modules.
-/
