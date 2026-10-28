module

public import Stellmacher.SectionEight.CriticalOutsideInvolution
public import Stellmacher.SectionEight.LocalQuotientSL2
public import Stellmacher.SectionEight.NoncentralSylowCenterAction
public import Stellmacher.SectionEight.LemmaEightOne
public import Stellmacher.SectionEight.LemmaEightTwo
public import Stellmacher.SectionEight.EightTwoCriticalDistanceLeTwo
public import Stellmacher.SectionEight.LemmaEightThree
public import Stellmacher.SectionEight.LemmaEightFour
public import Stellmacher.SectionEight.GeneratedEightFour
public import Stellmacher.SectionEight.LemmaEightFive
public import Stellmacher.SectionEight.EightFiveCentralizerCore
public import Stellmacher.SectionEight.LemmaEightSix
public import Stellmacher.SectionEight.EightSixHighCostNextCore
public import Stellmacher.SectionEight.EightSixHighCostExtraspecial
public import Stellmacher.SectionEight.EightSixHighCostActorRank
public import Stellmacher.SectionEight.EightSixHighCostResidualElementary
public import Stellmacher.SectionEight.EightSixHighCostCoreOrders
public import Stellmacher.SectionEight.EightSixHighCostCoreActionRank
public import Stellmacher.SectionEight.EightSixHighCostFixedCoreSplitting
public import Stellmacher.SectionEight.EightSixHighCostResidualQuotient
public import Stellmacher.SectionEight.EightSixCostFourRelativeDoubleSL2
public import Stellmacher.SectionEight.GeneratedEightSixCostFourReduction
public import Stellmacher.SectionEight.EightFourLocalContext
public import Stellmacher.SectionEight.EightSixHighCostResidualRankFour
public import Stellmacher.SectionEight.EightSixCostFourNextQuotient
public import Stellmacher.SectionEight.EightSixCostFourModuleQuaternion
public import Stellmacher.SectionEight.EightSixNextCoreFrattini
public import Stellmacher.SectionEight.EightSixCostFourCoreQuotientCard
public import Stellmacher.SectionEight.EightSixHighCostCaseC
public import Stellmacher.SectionEight.EightSixCostFourFixedCoreCard
public import Stellmacher.SectionEight.EightSixCostFourSylowOrders

public import Stellmacher.SectionEight.EightSixCostFourInitialResidualCore

public import Stellmacher.SectionEight.EightSixCostFourInitialResidualSpecial

public import Stellmacher.SectionEight.EightSixCostFourInitialQuotientBound

public import Stellmacher.SectionEight.EightSixCostFourInitialResidualModule

public import Stellmacher.SectionEight.EightSixCostFourModuleLNormal

/-!
# Stellmacher Section 8 assembly

This module re-exports the numbered Section 8 results together with the proved
local leaves used by (8.2): noncentrality of both Sylow omega-center actions,
recognition of the faithful local quotient as `SL₂(2)` from its dihedral core
quotient, critical distance one in the noncentral case, and
the critical-pair involution used by the terminal finite-group classification.
The distance reduction uses backward critical pairs, their central
commutators, and the distance-two V0 Frattini contradiction. The complete
(8.2) assembly combines that reduction with the whole-stabilizer
classification at distance one, exporting both local and legacy statements.
The conditional ambient-centralizer core
control used by the long-path argument of (8.5) is also re-exported.
For the high-cost branch of (8.6), the residual fixed decomposition
identifies the next two-core with its neighbor module. Its center and
Frattini subgroup give the extraspecial structure of order 512, and the
elementary core intersection yields the actual rank-three actor quotient.
The fixed groups of this actor make the residual action image elementary
abelian of exponent three. Exact action-kernel identification transfers this
to the native residual quotient. The core orders and cubic fixed-core splitting
are also re-exported. The generated-group reduction uses the high-cost
normalizer obstruction and isolates the actual cost-four case; its numerical
profile supports the corrected relative double-SL2 action theorem.
The actual residual quotient has rank four. The cost-four quotient is the
regular wreath product, its next module is a quaternion central product,
and the next core has Frattini subgroup equal to the central line. The
initial core quotient and pair intersection give the subsequent normalizer
support calculation. Its fixed core has order at most eight, yielding the
exact cost-four Sylow interval. The complete high-cost alternative assembles
its Sylow interval, residual rank, core structure, both quotient-action clauses
and neighbor normalizer. The proved local and generated (8.4) interfaces retain the two
ambient inputs on the actual graph and supply the generated (8.5) chain.
The complete cost-four alternative has its special initial core, quotient
bound and canonical elementary group of order sixteen normalized by L.
Its native A4 action and moved fixed plane prove that its ambient normalizer
is nonsolvable. The principal (8.6) theorem combines all three alternatives
while preserving the originally prescribed defining subgroups.
-/
