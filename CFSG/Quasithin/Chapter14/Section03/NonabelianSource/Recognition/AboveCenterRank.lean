module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.DegreeTwo

/-!
# The actor rank above the marked center

The original displaced-center isomorphism makes the smaller G.10 actor
nontrivial, hence d≤2m. The degree-two exclusion now gives m≥2. This is the
source rank bound consumed by the above-center orthogonal branch.

Source: Aschbacher--Smith 14.3.14--15, printed pp.994--995.
-/

public section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original actor above the marked center has rank at least two. -/
theorem actor_rank_ge_two_of_center_ne_point
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
    (d : ClosureGeometry F) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v (hatSpace F (F.E g))
      (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hZ : F.ZU ≠ F.Vi 1) :
    2 ≤ finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) := by
  have hb := rankTwo_dimension_le_twice_actor_of_center_ne_point
    (source_lemma_14_2_4 hG T hempty hM hu hmany hcard e) F g d hne hgP hgH hyp hZ
  have hl := hyp.two_le_dimension
  by_contra hh
  have hd : finrank (ZMod 2) (Additive F.Uhat) = 2 := by omega
  exact false_of_degree_two hG T hempty hM hu hmany hcard e hnot F d hne g hgP hgH B v hyp hd

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
