module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.LocalStructure
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.SimplicityReduction
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2
public import Theory.SpecificGroups.Janko3.Model.Basic

/-!
# Local structure for recognition of J₂ and J₃

Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, I.4.7, printed p. 418, asserts that every group
of type J₂ is isomorphic to J₂, and every group of type J₃ is isomorphic
to J₃. `J2Type` and `J3Type` encode exactly the preceding source definitions.
The target carriers are `Sporadic.LeechRelated.J2.Carrier` and
`Sporadic.Janko3.Model`, the independently constructed ATLAS permutation
groups. No identification with an alternate lattice construction is made.

The proved local consequences include the extraspecial two-core of order
32, the centralizer order 1920, both normalizer equalities, trivial ambient
center, and the Sylow order 128 in the one-class case. The generic
simplicity argument is reduced to irreducibility on the central quotient
and fusion into the centralizer outside its two-core.

The local action and fusion obligations, followed by the two recognition
arguments, remain to be proved. Neither source clause of I.4.7 is asserted
by this module yet. Its final assembly must discharge the local hypotheses
and produce actual multiplicative equivalences to the indicated carriers.

The source routes are Janko, *Some new simple groups of finite order, I*
(1968); Hall–Wales, *The simple group of order 604,800* (1968), or
Aschbacher, *Sporadic Groups* (1994), §47, for J₂; and Higman–McKay,
*On Janko's simple group of order 50,232,960* (1969), or Frohardt,
*A trilinear form for the third Janko group* (1983), for J₃.
-/
