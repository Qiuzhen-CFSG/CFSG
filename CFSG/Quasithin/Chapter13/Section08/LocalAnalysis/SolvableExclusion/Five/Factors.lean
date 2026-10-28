module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.Action
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.Lift
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.SupportGeneration
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.Exclusion
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.FixedIndex
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.CommonCenter
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.Product
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.SourceAssembly

/-!
# Five-primary factors: quotient actions, products and the equality case

The literal quotient action is faithful by the source kernel identity.
Every subgroup of P* has a specified lift into the supplied five-group P,
with the same order and exact star image. For a `Factorization`, its factors
are cyclic and independent; their actual moved supports are independent and
generate the full P-displacement. The product isomorphisms retain the actual
subgroup inclusions and give orders 5^s and 16^s. Split involution supports
give both the order-sixteen displacement and the fixed index sixteen.

The source kernel identifies Dγ with Uγ ∩ Q_H. The source centralizer and
index equalities from F.9.16 construct `CommonCenterOnDH` on the actual
image of D_H, including faithfulness, invariance and its order-two center.
The common-center argument then excludes `RankTwoFactors`, establishing
both nontrivial involution restrictions from that faithfulness.

`rankOneFactors_of_critical_pair` now constructs the rank-one factors
from the supplied `ReducedFive`, genuine minimal solvable membership in Hz,
ambient quasithinness, the standing source flag and kernel, and the earlier
critical-pair conclusions. The factor construction uses the exact universal
D.2.13(1–2) input through the localized offender reduction; it does not assume
D.2.17's indecomposable hypotheses for H*. The source rank comparison and
binary pairing prove the required F.9.16 equality case and exclude rank two.
`exists_faithful_rankOneFactors_of_source` also constructs the faithful action
from the kernel identity. Both results retain the literal U_H, V₁, P and Uγ.

The independent Chapter D and geometry results remain explicit earlier-source
inputs to this conditional prerequisite. The parent retains their source
instantiation, geometric localization and the final solvable-exclusion proof.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.13,
printed p.951 (PDF p.968), with D.2.16–17 and F.9.13/F.9.16.
-/
