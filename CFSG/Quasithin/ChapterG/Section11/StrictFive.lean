module
public import CFSG.Quasithin.ChapterG.Section11.FiveConstituent
public import CFSG.Quasithin.ChapterG.Section11.StrictMultiplicity

/-!
# The symmetric-five constituent row on the strict quotient

For the literal quotient action in 6.2.18(2), the natural S₅ row of the
actual HX constituent-kernel quotient reconstructs the entire action as
G.11.2(9). The original crossing image, smaller center, marked vector,
form and relative Sylow-normality are retained. The first theorem handles the selected G.6.4 row; the second applies G.6.4
and removes that row automatically from the remaining alternatives.

Source: Aschbacher--Smith G.11.8 and 6.2.18(2), printed pp.368,690.
-/

public section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  (T L R : Subgroup G) (z d : G)
  [IsElementaryAbelian 2 (StrictVectorQuotient T L R z)]
  [IsElementaryAbelian 2 (strictCrossingImage T L R z d)]

/-- Reconstruct the full strict action from the selected five-point G.6.4
row, including the actual group isomorphism and full tensor equivalence. -/
theorem strict_proper_marked_five_quotient_conclusion
    (B : LinearMap.BilinForm (ZMod 2) (Additive (StrictVectorQuotient T L R z)))
    (v : Additive (StrictVectorQuotient T L R z))
    (h : ChapterG.Section10.Hypothesis (strictRepresentation T L R z) B v
      (strictHatSpace T L R z (strictCrossingIntersection T L R z d))
      (strictCrossingImage T L R z d)
      ((strictCrossingCenterImage T L R z d).subgroupOf (strictCrossingImage T L R z d)))
    (cover : Nonempty (ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple
      (StrictActor T L R z)))
    (a : StrictActor T L R z) (ha : a ∈ strictCrossingImage T L R z d)
    (hr : finrank (ZMod 2) (RankTwo.movedSpace (strictRepresentation T L R z) a) ≤ 2)
    (hv : v ∈ RankTwo.movedSpace (strictRepresentation T L R z) a)
    (S : Sylow 2 (StrictActor T L R z))
    (hSv : (S : Subgroup (StrictActor T L R z)) ≤
      ChapterG.Section10.pointCentralizer (strictRepresentation T L R z) v)
    (hXS : strictCrossingImage T L R z d ≤ S)
    (hXn : ((strictCrossingImage T L R z d).subgroupOf
      (S : Subgroup (StrictActor T L R z))).Normal)
    (hn : ¬ Group.IsSolvable (StrictActor T L R z))
    (K : Subgroup (StrictActor T L R z)) (hK : Theory.GroupTheory.IsComponent _ K)
    (hm : ⁅K,strictCrossingImage T L R z d⁆ ≠ ⊥)
    (I : Submodule (ZMod 2) (Additive (StrictVectorQuotient T L R z)))
    (hI : BinaryOffender.IsIrrPlus (strictRepresentation T L R z) (componentOrbit K ⊤) I)
    (hvI : v ∈ I) (hp : I ≠ ⊤)
    (hfive :
      let ρ := strictRepresentation T L R z
      let X := strictCrossingImage T L R z d
      let H := componentOrbit K ⊤
      letI := componentOrbit_top_normal K
      let hXI := h.stabilizes_constituent_of_point_mem (h.irreducible_of_not_solvable hn) H hI hvI
      let σ := ChapterG.Section09.constituentAction ρ H X I hI.choose hXI
      ChapterG.Section06.HasModelOn (kerRepresentation σ) ⊤ ⊤
        (BinaryPermutation.naturalRepresentation (Fin 5))) :
    ChapterG.Section11.Conclusion (strictRepresentation T L R z) B
      (strictCrossingImage T L R z d) :=
  ChapterG.Section11.proper_marked_five_quotient_conclusion h cover
    ⟨a,ha,hr,hv⟩ ⟨S,hSv,hXS,hXn⟩ hn hK hm hI hvI hp hfive

/-- The literal strict action reaches its full G.11.2 conclusion in the
five-point row; all other G.6.4 rows retain their exact quotient and witness. -/
theorem strict_proper_marked_constituent_remaining_models
    (B : LinearMap.BilinForm (ZMod 2) (Additive (StrictVectorQuotient T L R z)))
    (v : Additive (StrictVectorQuotient T L R z))
    (h : ChapterG.Section10.Hypothesis (strictRepresentation T L R z) B v
      (strictHatSpace T L R z (strictCrossingIntersection T L R z d))
      (strictCrossingImage T L R z d)
      ((strictCrossingCenterImage T L R z d).subgroupOf (strictCrossingImage T L R z d)))
    (cover : Nonempty (ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple
      (StrictActor T L R z)))
    (a : StrictActor T L R z) (ha : a ∈ strictCrossingImage T L R z d)
    (hr : finrank (ZMod 2) (RankTwo.movedSpace (strictRepresentation T L R z) a) ≤ 2)
    (hv : v ∈ RankTwo.movedSpace (strictRepresentation T L R z) a)
    (hS : ChapterG.Section11.NormalSylow (strictRepresentation T L R z) v
      (strictCrossingImage T L R z d))
    (hn : ¬ Group.IsSolvable (StrictActor T L R z))
    (K : Subgroup (StrictActor T L R z)) (hK : Theory.GroupTheory.IsComponent _ K)
    (hm : ⁅K,strictCrossingImage T L R z d⁆ ≠ ⊥)
    (I : Submodule (ZMod 2) (Additive (StrictVectorQuotient T L R z)))
    (hI : BinaryOffender.IsIrrPlus (strictRepresentation T L R z) (componentOrbit K ⊤) I)
    (hvI : v ∈ I) (hp : I ≠ ⊤) :
    ChapterG.Section11.Conclusion (strictRepresentation T L R z) B
      (strictCrossingImage T L R z d) ∨
    let ρ := strictRepresentation T L R z
    let X := strictCrossingImage T L R z d
    let H := componentOrbit K ⊤
    letI := Theory.GroupTheory.componentOrbit_top_normal K
    let hXI := h.stabilizes_constituent_of_point_mem (h.irreducible_of_not_solvable hn) H hI hvI
    let σ := ChapterG.Section09.constituentAction ρ H X I hI.choose hXI
    ∃ b : X, orderOf (b : StrictActor T L R z) = 2 ∧ v ∈ RankTwo.movedSpace ρ b ∧
      finrank (ZMod 2) (RankTwo.movedSpace ρ b) = 2 ∧
      let bP : (H ⊔ X : Subgroup (StrictActor T L R z)) :=
        ⟨b,(le_sup_right : X ≤ H ⊔ X) b.property⟩
      finrank (ZMod 2) (LinearMap.range (σ bP - LinearMap.id)) = 1 ∧
      ChapterG.Section06.Conclusion (kerRepresentation σ) (QuotientGroup.mk' σ.ker bP) ∧
      ChapterG.Section11.RemainingRankOneModels (kerRepresentation σ) (QuotientGroup.mk' σ.ker bP) :=
  ChapterG.Section11.proper_marked_constituent_remaining_models h cover
    ⟨a,ha,hr,hv⟩ hS hn hK hm hI hvI hp


end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
