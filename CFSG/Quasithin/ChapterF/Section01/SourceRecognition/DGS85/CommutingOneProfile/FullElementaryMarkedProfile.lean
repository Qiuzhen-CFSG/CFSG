module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryAlphaCatalogue
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryCatalogueConsumers

/-!
# The elementary source profile with both local catalogues discharged

The literal elementary beta quotient constructs both local quotient markings.
Applying the established Chapter 11 calculations now supplies the full-Borel
orders, corrected seed span and center, source path parameters r=4 and s=5,
and the U4 profile without catalogue or nonsolvability premises. The original
inclusion, parabolic-core quotient and both field degrees are retained.

The last theorem feeds this profile to the literal marked comparison. Its
marked split quotient and rotation order remain explicit Chapter 14 inputs;
this does not assert their construction or the nonelementary source branch.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.7), pp.174--175, (14.1), p.210, and Theorem D, p.224.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open Reduction Theory.GroupTheory FongSeitzBinary
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "G₀" => Reduction.G₀ L S

open Theory.GroupTheory.RankTwoAmalgam OriginalExtension SuzukiContainment NoncommutingProfile
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
local notation "R" => reducedSylow L S
local notation:max "M" b:arg => (Subgroup.map (Subgroup.subtype G₀) (graphLocalGroup F (base F b)))

section FullBorel
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable (h : HypothesisF11 L S)
    (hc : IsCriticalPair (Reduction.reducedFamily L S)
      (base (Reduction.reducedFamily L S) false) (base (Reduction.reducedFamily L S) true))
    (hb : DGS85.b (Reduction.reducedFamily L S) = 1)
    (hcomm : ⁅Z (Reduction.reducedFamily L S) (base (Reduction.reducedFamily L S) false),
      Z (Reduction.reducedFamily L S) (base (Reduction.reducedFamily L S) true)⁆ = ⊥)
    (helem : ∃ hN : (((Q (Reduction.reducedFamily L S)
        (base (Reduction.reducedFamily L S) true)).map (Reduction.G₀ L S).subtype).subgroupOf
        (twoCore (commonBorel L S))).Normal,
      letI := hN
      IsElementaryAbelian 2 (twoCore (commonBorel L S) ⧸
        ((Q (Reduction.reducedFamily L S) (base (Reduction.reducedFamily L S) true)).map
          (Reduction.G₀ L S).subtype).subgroupOf (twoCore (commonBorel L S))))

include h hc hb hcomm helem

/-- The source conclusion on the actual full-Borel quotient, with both
local catalogues constructed from the elementary branch. -/
theorem original_borel_elementary_orders_and_paths_of_source :
    ∃ m, 0 < m ∧
      ClassicalGroup.IsPSL ((graphLocalGroup F (base F true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F (base F true)).map (G₀).subtype)) 2 (2^m) ∧
      ClassicalGroup.IsPSL ((graphLocalGroup F (base F false)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F (base F false)).map (G₀).subtype)) 2 (2^(2*m)) ∧
      (Q F (base F false)).map (G₀).subtype = (Z F (base F false)).map (G₀).subtype ∧
      Nat.card ((Z F (base F true)).map (G₀).subtype) = 2^m ∧
      Nat.card ((Q F (base F false)).map (G₀).subtype) = (2^(2*m))^2 ∧
      Nat.card ((Q F (base F true)).map (G₀).subtype) = (2^(2*m))^2 * 2^m ∧
      Nat.card (twoCore (commonBorel L S)) = (2^(2*m))^2 * (2^m)^2 ∧
      HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf G₀) 4 5 ∧
      (∀ x : Vertex F, RootPathTransitive (graph F) G₀ x 5) ∧
      ∀ {x y : Vertex F} (q : (graph F).Walk x y), IsSourcePath q → 5 ≤ q.length →
        Odd (Nat.card ((pathFixer (X := G₀) q).map (G₀).subtype)) := by
  exact original_borel_elementary_orders_and_paths h hc hb hcomm
    (original_borel_elementary_alpha_model h hc hb helem)
    (original_borel_elementary_beta_model h helem) helem

/-- The source conclusion on the actual full-Borel quotient, with both
local catalogues constructed from the elementary branch. -/
theorem original_borel_elementary_span_and_center_of_source :
    betaSpan ((stabilizer F (base F true)).map (G₀).subtype)
      ((Z F (base F false)).map (G₀).subtype) = (Q F (base F true)).map (G₀).subtype ∧
      centerIn ((Q F (base F true)).map (G₀).subtype) = (Z F (base F true)).map (G₀).subtype := by
  exact original_borel_elementary_span_and_center h hc hb hcomm
    (original_borel_elementary_alpha_model h hc hb helem)
    (original_borel_elementary_beta_model h helem) helem

end FullBorel

variable (h : HypothesisF11 L S)
    (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) (base (reducedFamily L S) true))
    (hb : DGS85.b (reducedFamily L S) = 1)
    (hcomm : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),Z (reducedFamily L S) (base (reducedFamily L S) true)⁆ = ⊥)
    (helem : letI := QuadrangleStructure.original_core_normal_in_sylow (L := L) (S := reducedSylow L S) 1
      IsElementaryAbelian 2 (reducedSylow L S ⧸
        ((parabolic L (reducedSylow L S) 1).pCoreIn 2).subgroupOf (reducedSylow L S)))

include h hc hb hcomm helem

omit hcomm in
/-- The original reduced-parabolic branch constructs the actual alpha marking. -/
theorem original_parabolic_elementary_alpha_model :
    IsRankOneModel (M false ⧸ pCore 2 (M false)) := by
  have he : ∃ hN : (((Q F (base F true)).map (G₀).subtype).subgroupOf R).Normal,
      letI := hN
      IsElementaryAbelian 2 (R ⧸ ((Q F (base F true)).map (G₀).subtype).subgroupOf R) := by
    have hq : (Q F (base F true)).map (G₀).subtype = (parabolic L R 1).pCoreIn 2 :=
      (reduced_base_Q_map h true).trans (reduced_parabolic_core h 1).symm
    rw [hq]
    exact ⟨FongSeitzBinary.QuadrangleStructure.original_core_normal_in_sylow (L := L) (S := R) 1,helem⟩
  exact original_borel_elementary_alpha_model (G := G) (L := L) (S := S) h hc hb he

/-- The literal elementary source consumer with both local catalogues discharged. -/
theorem original_borel_elementary_marked_profile_of_source :
    ∃ m : ℕ, 0 < m ∧
      ∃ (kₐ : Type) (_ : Field kₐ) (_ : Finite kₐ) (_ : CharP kₐ 2)
        (kᵦ : Type) (_ : Field kᵦ) (_ : Finite kᵦ) (_ : CharP kᵦ 2),
        Nat.card kₐ = 2^(2*m) ∧ Nat.card kᵦ = 2^m ∧
          Nonempty (Assembly.UnitaryFourSource.Profile L R kₐ kᵦ false) := by
  exact original_borel_elementary_marked_profile_of_alpha_model h hc hb hcomm
    (original_parabolic_elementary_alpha_model h hc hb helem) helem

/-- The literal elementary source consumer with both local catalogues discharged. -/
theorem original_elementary_tree_path_profile_of_source :
    BasedPathTransitive
        (X := (reducedAmalgam L S).Universal)
        (sourceGraph (reducedAmalgam L S)) 5 ∧
      ∀ {x y} (q : (sourceGraph
          (reducedAmalgam L S)).Walk x y),
        q.IsPath → q.length = 5 →
          Odd (Nat.card (pathFixer
            (X := (reducedAmalgam L S).Universal) q)) := by
  exact original_elementary_tree_path_profile_of_alpha_model h hc hb hcomm
    (original_parabolic_elementary_alpha_model h hc hb helem) helem

/-- The literal elementary source consumer with both local catalogues discharged. -/
theorem original_elementary_reduced_comparison_of_source
    {X : Type*} [Group X] {endpoints : Fin 2 → Subgroup X}
    (quot : MarkedQuotient endpoints)
    (e : Iso (reducedAmalgam L S) quot.standardAmalgam)
    (split : SplitData quot.tits) (hrot : rotationOrder quot = 4) :
    ∃ (m : ℕ) (hm : 0 < m), Nonempty (Iso (reducedAmalgam L S)
      (UnitaryFourNative.amalgam m hm false)) := by
  exact original_elementary_reduced_comparison_of_alpha_model h hc hb hcomm
    (original_parabolic_elementary_alpha_model h hc hb helem) helem quot e split hrot

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
