module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Reduction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.RankOne.Contradiction

/-!
# Both three-primary rank-one exclusions in 13.8.13

`RankOne.Geometry.cyclic_false` and `RankOne.Geometry.contained_false`
prove the two branches from ReducedOdd and the actual standing geometry.
`rank_one_false_of_source` combines them, constructs the actual quotient
action, and derives L₁*≠1 from the standing noncentral action on V₃/V₁.
The strict inequality is D_H<U_H.

The proof obtains the order-two bound from faithful parabolic-core actions
on C₃ or the extraspecial group of order 27. Frattini irreducibility and
the actual critical-pair conjugator establish both generation assertions;
13.8.5 and corrected 13.8.10–11 give the contradiction. This direct route
replaces the recognition and module-dimension steps of the printed proof.
No rank contradiction, model isomorphism or generation witness is an input.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
13.8.13, printed p.951. This module is the conditional rank-one helper;
the parent constructs ReducedOdd and handles the noncontained branch.
-/
