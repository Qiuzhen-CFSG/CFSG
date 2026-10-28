module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.OddLinear.Preparation
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.OddLinear.Sections
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.OddLinear.Normalizer.RankOneComponent
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.OddLinear.Normalizer.RankTwoComponent
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.OddLinear.Sieve.SmallOuter
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.OddLinear.Sieve.RankOne
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.OddLinear.Sieve.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.OddLinear.Sieve.Noncentral
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.OddLinear.Sieve.Nilpotent

/-!
# Odd-degree component field detection: preparation and coefficient descent

The original Hall Cartan permutes with T, and the marked source numerics
give the coprime abelian actor needed by A.3.15. For a surviving actual
linear quotient marking, restriction to a constructed odd-degree subfield
preserves the nontrivial coefficient actor. The PSL₂ and graph-compatible
PSL₃ torus consumers then reduce Borel movement to simultaneous normalizer
lifts for that subfield.

For both PSL₂ and PSL₃, the original three-rank bound fixes the component.
The Normalizer modules construct all odd-subfield lifts and prove the actual
component commutator clause, retaining the PSL₃ graph factor. SmallOuter
eliminates the two-group outer rows, including odd-characteristic PSL₂.
The unitary modules construct the odd-subfield torus lifts and literal Borel
movement in PSU₃. RankOne applies these proofs to the complete simple
Bender row, retaining the actual component quotient and original Sylow.
Source applies completed A.3.6 to the actual image in G₁/O₂(G₁), eliminating
these rows, odd PSL₂, the alternating rows and binary degrees four/five,
while preserving all remaining simple and nonsimple alternatives.
Noncentral then excludes the remaining simple rows, triple covers and natural
extensions through their actual quotient actors. Only the nilpotent-Fitting
SL₂(5) extension remains. Nilpotent reduces its moved actual Cartan action
to a scalar on a primary Frattini plane with prime p>5, retaining every
extraspecial and homocyclic factor. The ambient scalar exclusion and final
source assembly stay with
this odd-degree branch, followed by the parent FieldDetection assembly.
Source: Aschbacher--Smith 11.5.6(3), printed p.781, using A.3.15, pp.50--51.
-/
