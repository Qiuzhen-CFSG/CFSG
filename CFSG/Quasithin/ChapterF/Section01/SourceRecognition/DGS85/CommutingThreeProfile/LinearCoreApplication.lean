module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.LinearCoreProduct
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.GeneratedIntersection

/-!
# Original-parabolic application of the linear middle-core product

The preceding linear product supplies the missing product premise of the
intersection-commutator argument. Common Sylows generate the actual starred
middle endpoint. Its normal action on H = V_x ∩ V_y and the earlier
minimal natural center give [H,Q_m] = Z_m or [H,Q_m] = 1.

Transport both the ordered product and this dichotomy through the literal
inclusion into the original completion. The target core is O₂ of the full
original parabolic, using the proved equality with the starred core.
The central alternative remains explicit; its exclusion and the later
source profiles are not asserted. The common Sylows, center inclusions,
commutator bounds and natural-center minimality are the preceding Chapter 8
inputs. No middle-core product or classification conclusion is assumed.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
Part II, (12.1), (12.3)(b--c), printed pp.178--180.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Apply the proved linear product to the reduced and original core commutators. -/
theorem source_linear_intersection_center_alternative
    {k l : Type*} [Field k] [Finite k] [CharP k 2]
    [Field l] [Finite l] [CharP l 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {a x : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) i))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hxm : (graph (reducedFamily L S)).Adj x (base (reducedFamily L S) (!i)))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    (eMid : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL(2,l))
    (R : Sylow 2 (star L S i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (T U : Sylow 2 (star L S (!i)))
    (hT : (T : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hU : (U : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hzx : Z (reducedFamily L S) x ≤ Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) i) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcommx : ⁅V (reducedFamily L S) x 1, Q (reducedFamily L S) x⁆ ≤ Z (reducedFamily L S) x)
    (hcommy : ⁅V (reducedFamily L S) (base (reducedFamily L S) i) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) i)⁆ ≤
        Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hmin : ∀ N : Subgroup (star L S (!i)), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) (!i))).subgroupOf (star L S (!i)) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) (!i))).subgroupOf (star L S (!i))) :
    let F := reducedFamily L S
    let m := base F (!i)
    let y := base F i
    let H := V F x 1 ⊓ V F y 1
    let Q₀ := (parabolic L S (if !i then 1 else 0)).pCoreIn 2
    (Q₀ : Set G) = ((Q F x ⊓ Q F m).map (G₀ L S).subtype : Set G) *
      ((Q F y ⊓ Q F m).map (G₀ L S).subtype : Set G) ∧
    (⁅H,Q F m⁆ = Z F m ∨ H ≤ centralizer (Q F m : Set (G₀ L S))) ∧
    (⁅H.map (G₀ L S).subtype,Q₀⁆ = (Z F m).map (G₀ L S).subtype ∨
      H.map (G₀ L S).subtype ≤ centralizer (Q₀ : Set G)) := by
  let F := reducedFamily L S
  let m := base F (!i)
  let y := base F i
  let A := star L S (!i)
  let H := V F x 1 ⊓ V F y 1
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  have hQU := fun v => (source_Z_Q_U (reduced_triple h) v).2
  have hadj : (graph F).Adj y m :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hne : x ≠ y := by
    intro he
    have hseed : Z F a ≤ V F x 1 :=
      le_iSup_of_le a (le_iSup_of_le ((mem_ball_one F x a).mpr (Or.inl hxa)) le_rfl)
    have hV := V_le_Q F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb x
    exact hc.2 (hseed.trans (hV.trans (by rw [he]; exact hQU y)))
  have hgen : A = (Q F x ⊔ Q F y) ⊔ Q F m := by
    have hh := star_three_core_generation h (!i) hxm.symm
      (by simpa only [Bool.not_not] using hne) T U
      (by simpa only [Bool.not_not] using hT) hU
    simpa only [Bool.not_not,sup_comm,sup_left_comm,sup_assoc] using hh
  have hprod := (source_linear_first_index_and_product h i hb hc hxa hxm e eMid R hR).2.2.1
  have hnH : A ≤ normalizer (H : Set (G₀ L S)) := by
    rw [hgen]
    exact intersection_normalized F hQU hxm hadj hcommx hcommy hzx hzy
  have hZA : Z F m ≤ A :=
    ((hZ m).trans (map_subtype_le _)).trans
      ((star_core h (!i)).ge.trans (map_subtype_le _))
  have hnZ : A ≤ normalizer (Z F m : Set (G₀ L S)) :=
    (star_le_stabilizer (!i)).trans
      ((normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer F m)).mp (Z_normal F m))
  let : ((Z F m).subgroupOf A).Normal := normal_subgroupOf_of_le_normalizer hnZ
  let : IsMinimalNormal ((Z F m).subgroupOf A) :=
    ⟨fun N _ hN => hmin N inferInstance hN⟩
  have halt : ⁅H,Q F m⁆ = Z F m ∨ H ≤ centralizer (Q F m : Set (G₀ L S)) :=
    intersection_commutator_dichotomy F A (star_le_stabilizer (!i)) hZA hnH
      (intersection_commutator_le_center F hcommx hcommy hzx hzy hprod)
  have hcore : (Q F m).map (G₀ L S).subtype =
      (parabolic L S (if !i then 1 else 0)).pCoreIn 2 := by
    rw [← star_core h (!i), ← Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective
      2 _ (G₀ L S).subtype_injective]
    change (((starredParabolic L S (if !i then 1 else 0)).subgroupOf (G₀ L S)).map
      (G₀ L S).subtype).pCoreIn 2 = _
    rw [map_subgroupOf_eq_of_le (star_le_completion _)]
    exact h.starredParabolic_same_core _
  refine ⟨?_,halt,?_⟩
  · have hset := middle_core_product_as_set F hQU (y := y) hxm
    rw [← hprod] at hset
    have hh := congrArg (fun X : Set (G₀ L S) => (G₀ L S).subtype '' X) hset
    rw [Set.image_mul] at hh
    change ((Q F m).map (G₀ L S).subtype : Set G) = _ at hh
    rwa [hcore] at hh
  · rcases halt with he | he
    · left
      have hh := congrArg (Subgroup.map (G₀ L S).subtype) he
      rwa [map_commutator,hcore] at hh
    · right
      apply commutator_eq_bot_iff_le_centralizer.mp
      have hh := congrArg (Subgroup.map (G₀ L S).subtype)
        (commutator_eq_bot_iff_le_centralizer.mpr he)
      rwa [map_commutator,hcore,Subgroup.map_bot] at hh

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
