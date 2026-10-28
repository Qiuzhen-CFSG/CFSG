module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.IntrinsicCenterImage
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.OriginalNonElementarySource

/-!
# Nonelementary source profiles away from the exceptional binary seed

The literal critical-center image of order other than two excludes the
strict order-144 beta enlargement. This constructs the beta catalogue and
feeds the actual full-Borel nonelementary quotient into the proved Suzuki
exclusion. Both unitary covers remain possible. The same source calculations
then give exact orders, central and Frattini layers, the equivariant natural
alpha quotient, and the Chapter 14 universal-cover path inputs.

The alpha catalogue remains explicit. The image-order-two beta boundary,
the nonelementary alpha exclusion, Cartan/reflection construction, exchange,
root signs and complete marked assembly are not discharged by this module.
Source: DGS, Groups and Graphs (1985), (11.2)(b), p.168,
(11.8), pp.175--177, and (14.1), p.210.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open Reduction NoncommutingProfile
open Theory.GroupTheory RankTwoAmalgam OriginalExtension SuzukiContainment
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
variable {G : Type*} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L₀ S₀
local notation "G₀" => Reduction.G₀ L₀ S₀

variable (h : HypothesisF11 L₀ S₀)
    (hc : IsCriticalPair (Reduction.reducedFamily L₀ S₀)
      (base (Reduction.reducedFamily L₀ S₀) false) (base (Reduction.reducedFamily L₀ S₀) true))
    (hb : DGS85.b (Reduction.reducedFamily L₀ S₀) = 1)
    (hcomm : ⁅Z (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) false),
      Z (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) true)⁆ = ⊥)
    (Ma : IsRankOneModel ((graphLocalGroup (Reduction.reducedFamily L₀ S₀)
      (base (Reduction.reducedFamily L₀ S₀) false)).map (Reduction.G₀ L₀ S₀).subtype ⧸
      pCore 2 ((graphLocalGroup (Reduction.reducedFamily L₀ S₀)
        (base (Reduction.reducedFamily L₀ S₀) false)).map (Reduction.G₀ L₀ S₀).subtype)))
    (hseed : ((Q (Reduction.reducedFamily L₀ S₀)
        (base (Reduction.reducedFamily L₀ S₀) true)).map (Reduction.G₀ L₀ S₀).subtype).relIndex
      ((Z (Reduction.reducedFamily L₀ S₀)
        (base (Reduction.reducedFamily L₀ S₀) false)).map (Reduction.G₀ L₀ S₀).subtype) ≠ 2)
    (hne : ∃ hN : (((Q (Reduction.reducedFamily L₀ S₀)
        (base (Reduction.reducedFamily L₀ S₀) true)).map (Reduction.G₀ L₀ S₀).subtype).subgroupOf
        (twoCore (commonBorel L₀ S₀))).Normal,
      letI := hN
      ¬ IsElementaryAbelian 2 (twoCore (commonBorel L₀ S₀) ⧸
        ((Q (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) true)).map
          (Reduction.G₀ L₀ S₀).subtype).subgroupOf (twoCore (commonBorel L₀ S₀))))

include h hc hb hcomm Ma hseed hne

/-- Construct both possible unitary markings after discharging the beta catalogue from the literal critical-center index. -/
theorem original_borel_nonElementary_unitary_beta_of_seed_index_ne_two :
    ∃ m, 0 < m ∧
      (ClassicalGroup.IsPSU ((graphLocalGroup F₀ (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F₀ (base F₀ true)).map (G₀).subtype)) 3 (2^m) ∨
       IsSU ((graphLocalGroup F₀ (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F₀ (base F₀ true)).map (G₀).subtype)) 3 (2^m)) := by
  exact original_borel_nonElementary_unitary_beta h hc hb hcomm Ma
    (original_reduced_beta_model_of_seed_index_ne_two h hc hb hseed) hne

/-- The original nonelementary orders and source path parameters require no beta catalogue when the critical-center image has order other than two. -/
theorem original_borel_nonElementary_orders_and_paths_of_seed_index_ne_two :
    ∃ m, 0 < m ∧
      (ClassicalGroup.IsPSU ((graphLocalGroup F₀ (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F₀ (base F₀ true)).map (G₀).subtype)) 3 (2^m) ∨
       IsSU ((graphLocalGroup F₀ (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F₀ (base F₀ true)).map (G₀).subtype)) 3 (2^m)) ∧
      ClassicalGroup.IsPSL ((graphLocalGroup F₀ (base F₀ false)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F₀ (base F₀ false)).map (G₀).subtype)) 2 (2^(2*m)) ∧
      Nat.card ((Q F₀ (base F₀ true)).map (G₀).subtype) = 2^(7*m) ∧
      Nat.card (twoCore (commonBorel L₀ S₀)) = 2^(10*m) ∧
      Nat.card ((Q F₀ (base F₀ false)).map (G₀).subtype) = 2^(8*m) ∧
      ((Z F₀ (base F₀ false)).map (G₀).subtype).relIndex
        ((Q F₀ (base F₀ false)).map (G₀).subtype) = 2^(4*m) ∧
      HasSourcePathParameters (P := fun i => (P₀ L₀ S₀ i).subgroupOf G₀) 4 5 ∧
      (∀ x : Vertex F₀, RootPathTransitive (graph F₀) G₀ x 5) ∧
      ∀ {x y : Vertex F₀} (q : (graph F₀).Walk x y), IsSourcePath q → 5 ≤ q.length →
        Odd (Nat.card ((pathFixer (X := G₀) q).map (G₀).subtype)) := by
  exact original_borel_nonElementary_orders_and_paths h hc hb hcomm Ma
    (original_reduced_beta_model_of_seed_index_ne_two h hc hb hseed) hne

/-- The same original-inclusion core layers and equivariant natural alpha quotient, with the beta catalogue discharged by the seed index. -/
theorem original_borel_nonElementary_structural_profile_of_seed_index_ne_two :
    ∃ m, 0 < m ∧
      (ClassicalGroup.IsPSU ((graphLocalGroup F₀ (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F₀ (base F₀ true)).map (G₀).subtype)) 3 (2^m) ∨
       IsSU ((graphLocalGroup F₀ (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F₀ (base F₀ true)).map (G₀).subtype)) 3 (2^m)) ∧
      ((ballKernel F₀ (base F₀ false) 2).map (G₀).subtype = ⊥ ∧
      (ballKernel F₀ (base F₀ true) 3).map (G₀).subtype = ⊥ ∧
      ((ballKernel F₀ (base F₀ true) 2).map (G₀).subtype).pCoreIn 2 =
        (Z F₀ (base F₀ true)).map (G₀).subtype ∧
      Nat.card (((ballKernel F₀ (base F₀ true) 2).map (G₀).subtype).pCoreIn 2) = 2^m ∧
      (ballKernel F₀ (base F₀ true) 2).map (G₀).subtype ≠ ⊥) ∧
      (let R := (Q F₀ (base F₀ true)).map (G₀).subtype
        let C := (Z F₀ (base F₀ true)).map (G₀).subtype
        Nat.card R = 2^(7*m) ∧ Nat.card C = 2^m ∧
          centerIn R = C ∧ ⁅R,R⁆ = C ∧ (frattini R).map R.subtype = C ∧
          centerIn (twoCore (commonBorel L₀ S₀)) = C ∧
          (∀ x ∈ R, x^4 = 1) ∧ ⁅⁅R,R⁆,R⁆ = ⊥ ∧ ⁅R,R⁆ ≠ ⊥ ∧
          ∃ hN : (C.subgroupOf R).Normal, letI := hN
            IsElementaryAbelian 2 (R ⧸ C.subgroupOf R)) ∧
      (let R := (Q F₀ (base F₀ false)).map (G₀).subtype
        let C := (Z F₀ (base F₀ false)).map (G₀).subtype
        let L := (graphLocalGroup F₀ (base F₀ false)).map (G₀).subtype
        (frattini R).map R.subtype = C ∧
          ∃ hN : (C.subgroupOf R).Normal, letI := hN
            ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2),
              Nat.card k = 2^(2*m) ∧
              ∃ ea : (L ⧸ pCore 2 L) ≃* SL(2,k),
                ∃ e : (R ⧸ C.subgroupOf R) ≃* Multiplicative (Fin 2 → k),
                  ∀ (l : L) (x y : R), (y : G) = (l : G) * (x : G) * (l : G)⁻¹ →
                    (e (QuotientGroup.mk' (C.subgroupOf R) y)).toAdd =
                      Matrix.mulVec (ea (QuotientGroup.mk' (pCore 2 L) l)).val
                        (e (QuotientGroup.mk' (C.subgroupOf R) x)).toAdd) := by
  exact original_borel_nonElementary_structural_profile h hc hb hcomm Ma
    (original_reduced_beta_model_of_seed_index_ne_two h hc hb hseed) hne

/-- Apply the source branch to the actual Chapter 14 universal cover, preserving odd five-path fixers. -/
theorem original_nonElementary_tree_path_profile_of_seed_index_ne_two :
    BasedPathTransitive (X := (reducedAmalgam L₀ S₀).Universal)
      (sourceGraph (reducedAmalgam L₀ S₀)) 5 ∧
      ∀ {x y} (q : (sourceGraph (reducedAmalgam L₀ S₀)).Walk x y),
        q.IsPath → q.length = 5 →
          Odd (Nat.card (pathFixer (X := (reducedAmalgam L₀ S₀).Universal) q)) := by
  exact original_nonElementary_tree_path_profile h hc hb hcomm Ma
    (original_reduced_beta_model_of_seed_index_ne_two h hc hb hseed) hne

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
