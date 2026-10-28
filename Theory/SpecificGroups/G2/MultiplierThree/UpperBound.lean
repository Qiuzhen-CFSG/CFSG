module

public import Theory.SpecificGroups.G2.MultiplierThree.PrimeSupport
public import Theory.SpecificGroups.G2.MultiplierThree.UpperBound.LocalReduction
public import Theory.SpecificGroups.G2.MultiplierThree.UpperBound.OrthogonalDefect
public import Theory.SpecificGroups.G2.MultiplierThree.UpperBound.InvolutionLift
public import Theory.SpecificGroups.G2.MultiplierThree.UpperBound.CubicRelations

/-!
# Assembly of the remaining G₂(3) primary bounds

The local reductions detect the two-primary kernel in a lift of the actual
involution centralizer, and the three-primary kernel in a lift of the actual
unipotent subgroup. An odd kernel in the first and a single cubic root
multiplication defect in the second give the upper bound of three.

The imported local constructions discharge both inputs for the literal
canonical universal cover. Together with prime support, they prove that
its kernel has order at most three. The original conditional local-lift
interface is retained below. Identifying the kernel as cyclic of order
three still requires the independent lower-bound construction.

Source: Aschbacher–Smith I.1.4(2), printed p.408 (PDF p.419), and GLS3 §6.1,
Tables 6.1.2–6.1.3, citing Griess [Gr1].
-/

namespace Atlas.G2.FiniteCover.MultiplierThree
open PerfectCentralCovering
open MultiplierOrdinary

/-- The canonical universal kernel of the actual G₂(3) has odd order. -/
public theorem kernel_not_two_dvd : ¬ 2 ∣ Nat.card (Kernel (ZMod 3)) :=
  universal_not_two_dvd_kernel

/-- The three-primary part of the canonical universal kernel has order at most three. -/
public theorem kernel_not_nine_dvd : ¬ 9 ∣ Nat.card (Kernel (ZMod 3)) :=
  CubicRelations.not_nine_dvd_kernel

/-- Unconditional upper bound for the literal canonical universal kernel of G₂(3). -/
public theorem kernel_card_le_three : Nat.card (Kernel (ZMod 3)) ≤ 3 :=
  kernel_card_le_three_of_not_two_not_nine kernel_not_two_dvd kernel_not_nine_dvd

/-- Apply any two local constructions with the prescribed kernel bounds
to the canonical cover. -/
public theorem kernel_card_le_three_of_local_lifts
    (H : Subgroup (CoverGroup (ZMod 3)))
    (hH : H.map (universalProjection (Model (ZMod 3))) = TernaryLocals.Involution.P)
    (hodd : ¬ 2 ∣ Nat.card (H ⊓ Kernel (ZMod 3) : Subgroup (CoverGroup (ZMod 3))))
    (L : RootSections (universalProjection (Model (ZMod 3))))
    (z : CoverGroup (ZMod 3)) (hz : z ∈ Kernel (ZMod 3)) (hz3 : z ^ 3 = 1)
    (hL : L.ProductCompatibleModulo (Subgroup.zpowers z)) :
    Nat.card (Kernel (ZMod 3)) ≤ 3 :=
  kernel_card_le_three_of_not_two_not_nine
    (not_two_dvd_kernel_of_involution_lift (universalCover _) H hH hodd)
    (not_nine_dvd_kernel_of_cubic_root_defect (universalCover _) L z hz hz3 hL)

end Atlas.G2.FiniteCover.MultiplierThree
