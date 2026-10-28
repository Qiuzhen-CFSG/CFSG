module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.GeneratedIntersection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.CommonSylowIndex
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.MiddleCoreProduct

/-!
# The p.180 product in the order-ten dihedral branch

The actual original D10 quotient and the earlier common-Sylow marking give
index two for the first middle-core intersection. Starred local transitivity
transports this index to the other neighbor. The common Sylows generate the
starred endpoint, and the full-stabilizer nonnormality input from (6.5)
separates the two intersections. They therefore multiply to the middle core.
The original completion inclusion sends this product to the original
parabolic two-core, with both factors retained literally.

The final theorem applies this product to the existing intersection-commutator
argument, discharging its core-product premise. Its natural-center minimality,
center-centralization and commutator bounds are earlier Chapter 8 inputs;
common Sylows and relative nonnormality belong to the shared Chapter 6 setup.
These earlier inputs remain explicit. The central alternative still requires
the p.180 exclusion, and this theorem does not assert (12.3)(c), the TYPE
alternatives of (12.9), or the Chapter 13 prefix.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, (6.5), (12.1), (12.3), printed pp.121,178--180.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open Subgroup.CosetGeometry.RankTwo Reduction
namespace ReducedLayer
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The middle-core product and its literal original-parabolic image in the D10 row. -/
theorem source_dihedral_middle_core_product (h : HypothesisF11 L S) (i : Bool)
    {y : Vertex (reducedFamily L S)}
    (hy : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) y)
    (hne : y ≠ base (reducedFamily L S) (!i))
    (T R : Sylow 2 (stabilizer (reducedFamily L S) (base (reducedFamily L S) i)))
    (hT : (T : Subgroup (stabilizer (reducedFamily L S) (base (reducedFamily L S) i))).map
      (stabilizer (reducedFamily L S) (base (reducedFamily L S) i)).subtype =
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (stabilizer (reducedFamily L S) (base (reducedFamily L S) i))).map
      (stabilizer (reducedFamily L S) (base (reducedFamily L S) i)).subtype =
        Q (reducedFamily L S) y ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hTS : (T : Subgroup (stabilizer (reducedFamily L S) (base (reducedFamily L S) i))).map
      (stabilizer (reducedFamily L S) (base (reducedFamily L S) i)).subtype ≤ star L S i)
    (hRS : (R : Subgroup (stabilizer (reducedFamily L S) (base (reducedFamily L S) i))).map
      (stabilizer (reducedFamily L S) (base (reducedFamily L S) i)).subtype ≤ star L S i)
    (e : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* DihedralGroup 5)
    (D : Sylow 2 (star L S (!i)))
    (hD : (D : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hnot : ¬ stabilizer (reducedFamily L S) (base (reducedFamily L S) i) ≤ normalizer
      ((Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊓
        Q (reducedFamily L S) (base (reducedFamily L S) i) : Subgroup (G₀ L S)) : Set (G₀ L S))) :
    let F := reducedFamily L S
    let X := Q F (base F (!i)) ⊓ Q F (base F i)
    let Y := Q F y ⊓ Q F (base F i)
    Q F (base F i) = X ⊔ Y ∧
      (Q F (base F i) : Set (G₀ L S)) = (X : Set (G₀ L S)) * (Y : Set (G₀ L S)) ∧
      ((parabolic L S (if i then 1 else 0)).pCoreIn 2 : Set G) =
        (X.map (G₀ L S).subtype : Set G) * (Y.map (G₀ L S).subtype : Set G) := by
  let F := reducedFamily L S
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hadj : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hx : (Q F (base F (!i)) ⊓ Q F (base F i)).relIndex (Q F (base F i)) = 2 := by
    simpa only [inf_comm] using source_dihedral_core_index h (!i) e D hD
  obtain ⟨g, hg, hgy⟩ := star_locally_transitive h i hadj hy
  have hyindex := (middle_core_intersection_index_conjugate F g
    (star_le_stabilizer i hg) hgy).trans hx
  obtain ⟨hprod, hset⟩ := middle_core_product_of_index_two F
    (fun v => (source_Z_Q_U (reduced_triple h) v).2) hadj.symm hy.symm
    (star L S i) (star_three_core_generation_of_full_sylows h i hy hne T R hT hR hTS hRS)
    (fun hn => hnot ((core_intersection_normalizer_transfer F hadj (star L S i)
      (star_le_stabilizer i) (fun y hy => star_locally_transitive h i hadj hy)).mpr hn)) hx hyindex
  refine ⟨hprod, hset, ?_⟩
  have hm := congrArg (fun X : Set (G₀ L S) => (G₀ L S).subtype '' X) hset
  rw [Set.image_mul] at hm
  change (((Q F (base F i)).map (G₀ L S).subtype : Subgroup G) : Set G) = _ at hm
  have hcore : (Q F (base F i)).map (G₀ L S).subtype =
      (parabolic L S (if i then 1 else 0)).pCoreIn 2 := by
    rw [← star_core h i, ← Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective
      2 _ (G₀ L S).subtype_injective]
    change (((starredParabolic L S (if i then 1 else 0)).subgroupOf (G₀ L S)).map
      (G₀ L S).subtype).pCoreIn 2 = _
    rw [map_subgroupOf_eq_of_le (star_le_completion _)]
    exact h.starredParabolic_same_core _
  rwa [hcore] at hm

/-- Apply the binary core product to the exact intersection-commutator dichotomy. -/
theorem source_dihedral_intersection_center_alternative (h : HypothesisF11 L S) (i : Bool)
    {y : Vertex (reducedFamily L S)}
    (hy : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) y)
    (hne : y ≠ base (reducedFamily L S) (!i))
    (T R : Sylow 2 (stabilizer (reducedFamily L S) (base (reducedFamily L S) i)))
    (hT : (T : Subgroup (stabilizer (reducedFamily L S) (base (reducedFamily L S) i))).map
      (stabilizer (reducedFamily L S) (base (reducedFamily L S) i)).subtype =
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (stabilizer (reducedFamily L S) (base (reducedFamily L S) i))).map
      (stabilizer (reducedFamily L S) (base (reducedFamily L S) i)).subtype =
        Q (reducedFamily L S) y ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hTS : (T : Subgroup (stabilizer (reducedFamily L S) (base (reducedFamily L S) i))).map
      (stabilizer (reducedFamily L S) (base (reducedFamily L S) i)).subtype ≤ star L S i)
    (hRS : (R : Subgroup (stabilizer (reducedFamily L S) (base (reducedFamily L S) i))).map
      (stabilizer (reducedFamily L S) (base (reducedFamily L S) i)).subtype ≤ star L S i)
    (hcx : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      centralizer (Q (reducedFamily L S) (base (reducedFamily L S) i) : Set (G₀ L S)))
    (hcy : Z (reducedFamily L S) y ≤
      centralizer (Q (reducedFamily L S) (base (reducedFamily L S) i) : Set (G₀ L S)))
    (hx : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1,
        Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ ≤
      Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hycomm : ⁅V (reducedFamily L S) y 1, Q (reducedFamily L S) y⁆ ≤ Z (reducedFamily L S) y)
    (e : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* DihedralGroup 5)
    (D : Sylow 2 (star L S (!i)))
    (hD : (D : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hnot : ¬ stabilizer (reducedFamily L S) (base (reducedFamily L S) i) ≤ normalizer
      ((Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊓
        Q (reducedFamily L S) (base (reducedFamily L S) i) : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i)) :
    let F := reducedFamily L S
    let H := V F (base F (!i)) 1 ⊓ V F y 1
    ⁅H, Q F (base F i)⁆ = Z F (base F i) ∨ H ≤ centralizer (Q F (base F i) : Set (G₀ L S)) := by
  have hp := (source_dihedral_middle_core_product h i hy hne T R hT hR hTS hRS e D hD hnot).1
  exact source_intersection_center_alternative h i hy hne T R hT hR hTS hRS
    hcx hcy hx hycomm hp hmin

end ReducedLayer
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
