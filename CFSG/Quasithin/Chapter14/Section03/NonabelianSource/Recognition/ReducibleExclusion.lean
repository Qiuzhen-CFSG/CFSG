module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.NormalCubic
public import CFSG.Quasithin.ChapterG.Section10.Reducible.NormalCubic

/-!
# Excluding the original reducible terminal action

The G.10 reducible action supplies a normal cubic subgroup. If Z(U) is the
original marked point, the cubic-index argument excludes that subgroup unless
the ambient group is a Theorem E model. This retains the literal terminal
quotient and representation from the source flag.

Source: Aschbacher--Smith 14.3.15, printed p.994.
-/

public section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open ChapterA.Section05To06
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03
variable {G : Type*} [Group G] [Finite G]

/-- The actual center-point terminal action is irreducible. -/
theorem irreducible_of_center_point
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (d : ClosureGeometry F) (hZ : F.ZU = F.Vi 1)
    (g : G) [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v (hatSpace F (F.E g))
      (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g)))) :
    Representation.IsIrreducible F.terminalRepresentation := by
  by_contra hred
  obtain ⟨C,hCnorm,hC⟩ := hyp.normal_cubic_of_reducible hred
  let := hCnorm
  exact no_normal_cubic_of_center_point hG T hempty hM hu hmany hcard e hnot F d hZ C hC

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
