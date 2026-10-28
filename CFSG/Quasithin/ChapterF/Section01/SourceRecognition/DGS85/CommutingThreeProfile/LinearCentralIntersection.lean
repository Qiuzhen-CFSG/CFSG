module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.LinearCoreProduct
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiCoreProduct

/-!
# The linear neighbor row forces a central intersection

The marked linear quotient gives Q_m = V_x (Q_y ∩ Q_m), including over
F₂. This is precisely the seed formula whose intersection centralizes Q_m
by center minimality, three-core generation and the finite two-group center
argument. Transport that centralization through the original inclusion.
The resulting zero commutator contradicts the exact original-parabolic
commutator identity required by (12.3)(c), since Z_m is nontrivial.

This provides the linear-row exclusion step for (12.4), with the literal
original core and center image retained. The common Sylows, natural-center
orders and minimality, centerlessness and commutator bounds remain genuine
Chapter 8 inputs. Proving (12.3)(c) for the linear row is still required
before this step excludes that row in the unconditional source assembly;
no binary classification or noncentrality is asserted here.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
Part II, (12.1), (12.3)(c), (12.4), printed pp.178--181.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Linear neighbors, including SL₂(2), force a central intersection and
contradict the literal original-parabolic conclusion of (12.3)(c). -/
theorem source_linear_intersection_centralizes
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
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) (!i))).subgroupOf (star L S (!i)))
    (hz : center (star L S (!i)) = ⊥)
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card l ^ 2)
    (hcardy : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card l) :
    let F := reducedFamily L S
    let m := base F (!i)
    let y := base F i
    let H := V F x 1 ⊓ V F y 1
    let Q₀ := (parabolic L S (if !i then 1 else 0)).pCoreIn 2
    H ≤ centralizer (Q F m : Set (G₀ L S)) ∧
      H.map (G₀ L S).subtype ≤ centralizer (Q₀ : Set G) ∧
      ⁅H.map (G₀ L S).subtype,Q₀⁆ ≠ (Z F m).map (G₀ L S).subtype := by
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
  have hproducts := source_linear_first_index_and_product h i hb hc hxa hxm e eMid R hR
  have hseed : (Q F x ⊓ Q F m) ⊔ (Q F y ⊓ Q F m) =
      V F x 1 ⊔ (Q F m ⊓ Q F y) := by
    calc
      _ = Q F m := hproducts.2.2.1.symm
      _ = V F x 1 ⊔ (Q F y ⊓ Q F m) := hproducts.2.1
      _ = _ := by rw [inf_comm]
  have hylt : ¬ Z F m ≤ Z F y := by
    intro hle
    let : Finite (Z F y) := Finite.of_injective
      (inclusion (Z_le_stabilizer F y)) (inclusion_injective _)
    have hlecard := Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective _)
    change Nat.card (Z F m) ≤ Nat.card (Z F y) at hlecard
    rw [hcard,hcardy] at hlecard
    have hq : 1 < Nat.card l := Finite.one_lt_card
    nlinarith
  have hcentral : H ≤ centralizer (Q F m : Set (G₀ L S)) :=
    seed_alternative_centralizes_intersection F hQU hZ hxm hadj A
      (star_le_stabilizer (!i)) hgen hz
      (V_le_neighbor_Q F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb hxm)
      (V_elementary F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb x)
      hcommx hcommy hzx hzy hylt hmin hseed
  have hcore : (Q F m).map (G₀ L S).subtype =
      (parabolic L S (if !i then 1 else 0)).pCoreIn 2 := by
    rw [← star_core h (!i), ← Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective
      2 _ (G₀ L S).subtype_injective]
    change (((starredParabolic L S (if !i then 1 else 0)).subgroupOf (G₀ L S)).map
      (G₀ L S).subtype).pCoreIn 2 = _
    rw [map_subgroupOf_eq_of_le (star_le_completion _)]
    exact h.starredParabolic_same_core _
  have hzero : ⁅H.map (G₀ L S).subtype,
      (parabolic L S (if !i then 1 else 0)).pCoreIn 2⁆ = ⊥ := by
    have hh := congrArg (Subgroup.map (G₀ L S).subtype)
      (commutator_eq_bot_iff_le_centralizer.mpr hcentral)
    rwa [map_commutator,hcore,Subgroup.map_bot] at hh
  refine ⟨hcentral, commutator_eq_bot_iff_le_centralizer.mp hzero, ?_⟩
  intro he
  have hbot : Z F m = ⊥ :=
    (map_eq_bot_iff_of_injective (Z F m) (G₀ L S).subtype_injective).mp
      (he.symm.trans hzero)
  exact hylt (hbot.le.trans bot_le)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
