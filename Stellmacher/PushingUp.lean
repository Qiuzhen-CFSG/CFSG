module

public import Stellmacher.PushingUp.CriticalDistanceBound
public import Stellmacher.PushingUp.CriticalDistanceZero
public import Stellmacher.PushingUp.CriticalDistanceTwoStructure
public import Stellmacher.PushingUp.CriticalDistanceFourImpossible
public import Stellmacher.PushingUp.SL2TwoNormalModule
public import Stellmacher.PushingUp.SL2TwoCoreResidualCardFour
public import Stellmacher.PushingUp.SL2TwoStructure
public import Stellmacher.PushingUp.SL2Two
public import Stellmacher.SectionTwo.PushingUpThreeTwo
public import Stellmacher.SectionTwo.PushingUpThreeFour
public import Stellmacher.SectionTwo.PushingUpThreeFive
public import Stellmacher.PushingUp.ShiftSharedSylow
public import Stellmacher.PushingUp.ShiftCoreIntersectionNormal
public import Stellmacher.PushingUp.ShiftCoreIntersectionNormalLeft
public import Stellmacher.PushingUp.ShiftCoreIntersectionObstruction
public import Stellmacher.PushingUp.ShiftClosureNormal
public import Stellmacher.PushingUp.VertexOmegaGeneration
public import Stellmacher.PushingUp.DistanceFourLeftCenter
public import Stellmacher.PushingUp.DistanceFourRightCenter
public import Stellmacher.PushingUp.CriticalClosure
public import Stellmacher.PushingUp.CriticalClosureContainment
public import Stellmacher.PushingUp.NaturalQuotientInvolution
public import Stellmacher.PushingUp.DistanceFourConfiguration
public import Stellmacher.PushingUp.DistanceFourInitialRelations
public import Stellmacher.PushingUp.DistanceFourElementaryQuotient
public import Stellmacher.PushingUp.DistanceFourCoreProduct
public import Stellmacher.PushingUp.DistanceFourNormality
public import Stellmacher.PushingUp.DistanceFourCentralQuotient
public import Stellmacher.PushingUp.DistanceFourCentralTwoElements
public import Stellmacher.PushingUp.DistanceFourUNormal
public import Stellmacher.PushingUp.DistanceFourResidualAction
public import Stellmacher.PushingUp.DistanceFourActionKernel
public import Stellmacher.PushingUp.FaithfulFourNaturalAction
public import Stellmacher.PushingUp.FourElementActionInvolution
public import Stellmacher.PushingUp.LocalCharacteristicObstruction
public import Stellmacher.PushingUp.CriticalPairCoreIntersectionData
public import Stellmacher.PushingUp.CriticalPairCoreIntersectionGeneration
public import Stellmacher.PushingUp.CriticalPairMiddleSylow
public import Stellmacher.PushingUp.ResidualNeighborTransport
public import Theory.GroupTheory.CommutingFactorNormality
public import Theory.GroupTheory.CenterSmallIndex
public import Theory.GroupTheory.CentralTwoFactorQuotient
public import Theory.GroupTheory.CentralProductPSubgroupNormal
public import Theory.GroupTheory.TwoElementaryIndexTwo
public import Theory.Frattini.CentralElementarySupplement
public import Theory.GroupTheory.NormalCoverIntersection
public import Stellmacher.PushingUp.CriticalCommutatorNoncentral
public import Stellmacher.PushingUp.BicentralClosureCommutator
public import Stellmacher.PushingUp.OmegaCenterGeneration
public import Stellmacher.PushingUp.SL2TwoNaturalFixedGeneration

/-!
# The local pushing-up development

This module assembles the finite-module and locally finite amalgam results
used for the pushing-up input to Stellmacher's N-group theorem. The critical
pair theorems identify the natural SL₂(2) action, and the critical-distance
bound restricts the possibilities to zero, two and four. The zero-distance case gives
an elementary Sylow subgroup; the distance-two case gives an elementary,
irreducible residual commutator. The shared Sylow, centralizer, normality and
omega-center generation lemmas support the remaining distance analysis.

The hypotheses retain the exact nested Frattini quotient and the absence of
nontrivial characteristic Sylow subgroups normal in the original group.
Only the vertex stabilizers and their neighborhoods are finite; the free
amalgam and its coset graph are not assumed finite. Source: Stellmacher,
*Pushing up*, Arch. Math. 46 (1986), Sections 1–3, specialized to p=2,n=1,
as invoked in `refs/latex/stellmacher-n-group.tex`, (2.4).
-/
