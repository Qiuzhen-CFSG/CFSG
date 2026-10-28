module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.OriginalElementarySource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.OriginalNonElementarySource

/-!
# Source path assembly for the commuting critical edge

Relative normality of the actual beta core in O₂(B) permits the literal
elementary/nonelementary split. The two completed branch arguments now
construct their own quotient markings and paths. Hence the common source
parameters r=4, s=5, five-walk transitivity and odd long-path fixers require
neither a branch choice nor an escaping path. The second theorem applies
both path inputs to the full-Borel universal tree used in Chapter 14.

The actual local quotient catalogues remain explicit. The order-144
local-enlargement issue, compatible Cartans, exchange and marked model
recognition are not discharged by this path assembly.
Source: DGS, Groups and Graphs (1985), (11.7)(f), (11.8)(g), pp.174--177,
and (14.1), p.210.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open CommutingNontrivial NoncommutingProfile Subgroup.CosetGeometry.RankTwo Reduction
open Theory.GroupTheory RankTwoAmalgam OriginalExtension SuzukiContainment
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
variable {G : Type*} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L₀ S₀
local notation "G₀" => Reduction.G₀ L₀ S₀

private theorem original_beta_core_normal (h : HypothesisF11 L₀ S₀) :
    (((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf
      (twoCore (commonBorel L₀ S₀))).Normal := by
  let R := (stabilizer F₀ (base F₀ false) ⊓ stabilizer F₀ (base F₀ true)).pCoreIn 2
  have htr := Reduction.reduced_triple h
  have hBG : Reduction.B₀ L₀ S₀ ≤ G₀ :=
    (show Reduction.B₀ L₀ S₀ ≤ Reduction.P₀ L₀ S₀ 0 from le_sup_right).trans le_sup_left
  have hRG : twoCore (commonBorel L₀ S₀) ≤ G₀ :=
    (show twoCore (commonBorel L₀ S₀) ≤ Reduction.B₀ L₀ S₀ from le_sup_right).trans hBG
  have hmap : R.map (G₀).subtype = twoCore (commonBorel L₀ S₀) := by
    dsimp only [R]
    rw [show stabilizer F₀ (base F₀ false) = F₀ false from Subgroup.CosetGeometry.stabilizer_base _ _,
      show stabilizer F₀ (base F₀ true) = F₀ true from Subgroup.CosetGeometry.stabilizer_base _ _,
      show F₀ false ⊓ F₀ true = (Reduction.B₀ L₀ S₀).subgroupOf G₀ from htr.intersection,
      pCoreIn_subgroupOf 2 _ _ hBG,Reduction.B₀_core h]
    exact map_subgroupOf_eq_of_le hRG
  apply normal_subgroupOf_of_le_normalizer
  rw [←hmap]
  have hn : R ≤ normalizer (Q F₀ (base F₀ true) : Set G₀) :=
    ((pCoreIn_le 2 _).trans inf_le_right).trans (stabilizer_normalizes_Q F₀ _)
  exact (map_mono hn).trans ((Q F₀ (base F₀ true)).le_normalizer_map (G₀).subtype)


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
    (Mb : IsRankOneModel ((graphLocalGroup (Reduction.reducedFamily L₀ S₀)
      (base (Reduction.reducedFamily L₀ S₀) true)).map (Reduction.G₀ L₀ S₀).subtype ⧸
      pCore 2 ((graphLocalGroup (Reduction.reducedFamily L₀ S₀)
        (base (Reduction.reducedFamily L₀ S₀) true)).map (Reduction.G₀ L₀ S₀).subtype)))

include h hc hb hcomm Ma Mb

/-- The source path profile with both branch choices, original field
markings, earlier-local data and all path premises discharged. -/
theorem original_borel_commuting_source_path_profile :
    HasSourcePathParameters (P := fun i => (P₀ L₀ S₀ i).subgroupOf G₀) 4 5 ∧
      (∀ x : Vertex F₀, RootPathTransitive (graph F₀) G₀ x 5) ∧
      ∀ {x y : Vertex F₀} (q : (graph F₀).Walk x y), IsSourcePath q → 5 ≤ q.length →
        Odd (Nat.card ((pathFixer (X := G₀) q).map (G₀).subtype)) := by
  let hN := original_beta_core_normal h
  by_cases he : IsElementaryAbelian 2 (twoCore (commonBorel L₀ S₀) ⧸
      ((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf (twoCore (commonBorel L₀ S₀)))
  · obtain ⟨m,hm,mark⟩ := original_borel_elementary_linear_beta h hc hb hcomm Ma Mb ⟨hN,he⟩
    exact original_linear_beta_source_path_profile h hc hb hcomm Ma hm mark
  · obtain ⟨m,hm,mark⟩ := original_borel_nonElementary_unitary_beta h hc hb hcomm Ma Mb ⟨hN,he⟩
    exact original_borel_unitary_source_path_profile_from_marking h hc hb hcomm Ma hm mark

/-- Both Chapter 14 path premises on the literal full-Borel universal tree,
with no elementary/nonelementary choice or escaping-path input. -/
theorem original_commuting_tree_path_profile :
    BasedPathTransitive (X := (reducedAmalgam L₀ S₀).Universal)
      (sourceGraph (reducedAmalgam L₀ S₀)) 5 ∧
      ∀ {x y} (q : (sourceGraph (reducedAmalgam L₀ S₀)).Walk x y),
        q.IsPath → q.length = 5 →
          Odd (Nat.card (pathFixer (X := (reducedAmalgam L₀ S₀).Universal) q)) := by
  let hN := original_beta_core_normal h
  by_cases he : IsElementaryAbelian 2 (twoCore (commonBorel L₀ S₀) ⧸
      ((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf (twoCore (commonBorel L₀ S₀)))
  · exact original_elementary_tree_path_profile h hc hb hcomm Ma Mb ⟨hN,he⟩
  · exact original_nonElementary_tree_path_profile h hc hb hcomm Ma Mb ⟨hN,he⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
