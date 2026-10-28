module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.UnitaryBorel
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.OriginalUnitaryCenters
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.OriginalUnitaryCoreOrders
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.OriginalUnitaryNatural
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.OriginalUnitaryPaths
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.SourcePathParameters
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.OriginalUnitaryTreeRoots

/-!
# The original marked unitary Chapter 11 profiles

The source hypotheses, alpha actor catalogue and beta PSU/SU marking now
construct the centers, field relation, exact core orders, natural alpha
coordinates and the r=4, s=5 path profile. Three-walk transitivity supplies
the early supplements. The resulting odd five-walk fixers and exact edge-core
order prove five-walk transitivity by counting, then four-walk transitivity
by restriction. The marked central layers and natural quotient are re-exported
from OriginalUnitaryComplete. OriginalUnitaryTreeRoots applies both Chapter 14
inputs on the actual universal tree to the literal roots and apartment quotient,
preserving the supplied degree in their square and cube orders.

The historical `of_four_transitive` signatures retain their path argument
for compatibility. Their proofs delegate to the stronger marked results,
which require no initial path-transitivity premise. The alpha catalogue and
original beta marking remain explicit, and both unitary covers and every
positive degree are preserved. This does not identify the marked amalgam
or discharge the distinct elementary and mixed branches.
Source: DGS85, Groups and Graphs, (11.4)--(11.8), pp.171--177; (14.1), p.210.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open CommutingNontrivial NoncommutingProfile Subgroup.CosetGeometry.RankTwo Reduction
open Theory.GroupTheory RankTwoAmalgam OriginalExtension SuzukiContainment
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
variable {G : Type*} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F₀" => reducedFamily L₀ S₀
local notation "G₀" => Reduction.G₀ L₀ S₀
local notation "A" => reducedAmalgam L₀ S₀

variable (h : HypothesisF11 L₀ S₀)
    (hc : IsCriticalPair (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) false) (base (Reduction.reducedFamily L₀ S₀) true))
    (hb : DGS85.b (Reduction.reducedFamily L₀ S₀) = 1)
    (hcomm : ⁅Z (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) false),Z (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) true)⁆ = ⊥)
    (Ma : IsRankOneModel ((graphLocalGroup (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) false)).map ((Reduction.G₀ L₀ S₀)).subtype ⧸
      pCore 2 ((graphLocalGroup (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) false)).map ((Reduction.G₀ L₀ S₀)).subtype)))
    {m : ℕ} (hm : 0 < m)
    (mark : ClassicalGroup.IsPSU ((graphLocalGroup (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) true)).map ((Reduction.G₀ L₀ S₀)).subtype ⧸
        pCore 2 ((graphLocalGroup (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) true)).map ((Reduction.G₀ L₀ S₀)).subtype)) 3 (2^m) ∨
      IsSU ((graphLocalGroup (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) true)).map ((Reduction.G₀ L₀ S₀)).subtype ⧸
        pCore 2 ((graphLocalGroup (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) true)).map ((Reduction.G₀ L₀ S₀)).subtype)) 3 (2^m))
    (ht : ∀ x : Vertex (Reduction.reducedFamily L₀ S₀), x.type = false → RootPathTransitive (graph (Reduction.reducedFamily L₀ S₀)) (Reduction.G₀ L₀ S₀) x 4)

include h hc hb hcomm Ma hm mark ht

-- Keep the historical `ht` parameter for callers using this API.
set_option linter.unusedSectionVars false in
/-- Compatibility wrapper for the exact core orders. The marked short-path
calculation now discharges the path premise for this conclusion. -/
theorem original_borel_unitary_core_orders_of_four_transitive :
    Nat.card ((Q F₀ (base F₀ true)).map (G₀).subtype) = 2^(7*m) ∧
      Nat.card (twoCore (commonBorel L₀ S₀)) = 2^(10*m) ∧
      Nat.card ((Q F₀ (base F₀ false)).map (G₀).subtype) = 2^(8*m) ∧
      ((Z F₀ (base F₀ false)).map (G₀).subtype).relIndex
        ((Q F₀ (base F₀ false)).map (G₀).subtype) = 2^(4*m) := by
  exact original_borel_unitary_core_orders_from_marking h hc hb hcomm Ma hm mark

-- Keep the historical `ht` parameter for callers using this API.
set_option linter.unusedSectionVars false in
/-- Compatibility wrapper for the original natural alpha coordinates. The
short-path calculation preserves the field and literal conjugation action. -/
theorem original_borel_unitary_alpha_natural_of_four_transitive :
    let R := (Q F₀ (base F₀ false)).map (G₀).subtype
    let C := (Z F₀ (base F₀ false)).map (G₀).subtype
    let L := (graphLocalGroup F₀ (base F₀ false)).map (G₀).subtype
    (frattini R).map R.subtype = C ∧
      ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2),
        Nat.card k = 2^(2*m) ∧
        ∃ ea : (L ⧸ pCore 2 L) ≃* SL(2,k),
          ∃ f : R →* Multiplicative (Fin 2 → k), Function.Surjective f ∧
            f.ker = C.subgroupOf R ∧
            ∀ (l : L) (x y : R), (y : G) = (l : G) * (x : G) * (l : G)⁻¹ →
              (f y).toAdd = Matrix.mulVec (ea (QuotientGroup.mk' (pCore 2 L) l)).val (f x).toAdd := by
  exact original_borel_unitary_alpha_natural_from_marking h hc hb hcomm Ma hm mark

-- Keep the historical `ht` parameter for callers using this API.
set_option linter.unusedSectionVars false in
/-- Compatibility wrapper for the field and valences. The retained four-walk
premise is unnecessary for this conclusion; `original_unitary_field_and_valences`
provides the stronger API with the same input field. -/
theorem original_unitary_field_and_valences_of_four_transitive :
    ClassicalGroup.IsPSL ((graphLocalGroup F₀ (base F₀ false)).map (G₀).subtype ⧸
      pCore 2 ((graphLocalGroup F₀ (base F₀ false)).map (G₀).subtype)) 2 (2^(2*m)) ∧
      ∀ x : Vertex F₀, Nat.card ((graph F₀).neighborSet x) =
        2^(if x.type then 3*m else 2*m)+1 := by
  exact original_unitary_field_and_valences h hc hb hcomm Ma hm mark

-- Keep the historical `ht` parameter for callers using this API.
set_option linter.unusedSectionVars false in
/-- Compatibility wrapper for source (11.8)(g), with its initial
four-walk premise now discharged by the marked source calculation. -/
theorem original_borel_unitary_source_path_profile_of_four_transitive :
    HasSourcePathParameters (P := fun i => (P₀ L₀ S₀ i).subgroupOf G₀) 4 5 ∧
      (∀ x : Vertex F₀, RootPathTransitive (graph F₀) G₀ x 5) ∧
      ∀ {x y : Vertex F₀} (q : (graph F₀).Walk x y), IsSourcePath q → 5 ≤ q.length →
        Odd (Nat.card ((pathFixer (X := G₀) q).map (G₀).subtype)) := by
  exact original_borel_unitary_source_path_profile_from_marking h hc hb hcomm Ma hm mark

-- Keep the historical `ht` parameter for callers using this API.
set_option linter.unusedSectionVars false in
/-- Literal Chapter 14 path inputs on the actual full-Borel universal tree;
the original graph itself is not required to be a tree. -/
theorem original_unitary_tree_path_profile_of_four_transitive :
    BasedPathTransitive (X := (A).Universal) (sourceGraph A) 5 ∧
      ∀ {x y} (q : (sourceGraph A).Walk x y), q.IsPath → q.length = 5 →
        Odd (Nat.card (pathFixer (X := (A).Universal) q)) := by
  exact original_unitary_tree_path_profile_from_marking h hc hb hcomm Ma hm mark

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
