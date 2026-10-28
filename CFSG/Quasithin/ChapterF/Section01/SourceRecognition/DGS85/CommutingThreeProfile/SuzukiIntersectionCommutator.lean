module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiCentralExclusion

/-!
# The Suzuki intersection commutator and its original-group application

Combine the nonbinary Suzuki central-case exclusion with relative minimality
of the natural middle center. The middle-core product then gives exactly
[ V_x ∩ V_y, Q_m ] = Z_m. Local transitivity and the earlier core commutator
identity generate the whole V_y from its commutator with the starred endpoint.
Both conclusions are transported through the literal inclusion into the
original completion, retaining the original parabolic two-core and starred
group rather than a model substitute.

The middle-core product remains explicit: its separate central quotient
must still be eliminated. The earlier Chapter 8 common Sylows, natural
center minimality and orders, and conjugated index data also remain explicit.
This is the conditional nonbinary Suzuki application of (12.3)(c--d), not
the full Chapter 12 profile or its unconditional assembly.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
Part II, (12.3), printed pp.179--180.
-/

@[expose] public noncomputable section
open Subgroup
open BenderSuzuki.MatrixGroups BenderSuzuki.Converse
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Apply the Suzuki exclusion to the actual intersection and transport both
commutator equations to the original core and starred parabolic. -/
theorem source_suzuki_intersection_commutator
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {a x σ : Vertex (reducedFamily L S)}
    (hxadj : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x)
    (hne : x ≠ base (reducedFamily L S) (!i))
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k)
    (hz : center (star L S i) = ⊥)
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k ^ 2)
    (hcardy : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (hzx : Z (reducedFamily L S) x ≤ Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hcommx : ⁅V (reducedFamily L S) x 1, Q (reducedFamily L S) x⁆ ≤ Z (reducedFamily L S) x)
    (hcommy : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ =
        Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcross : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) σ,
      V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥)
    (hsmall : (Q (reducedFamily L S) σ).relIndex
      (V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1) ≤ Nat.card k)
    (hactor : (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex
      (V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (hfield : Nat.card k = 2 ^ (2 * n + 1))
    (Ry : Sylow 2 (star L S (!i)))
    (hRy : (Ry : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) (!i)))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hprod : Q (reducedFamily L S) (base (reducedFamily L S) i) =
      (Q (reducedFamily L S) x ⊓ Q (reducedFamily L S) (base (reducedFamily L S) i)) ⊔
      (Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊓
        Q (reducedFamily L S) (base (reducedFamily L S) i)))
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i)) :
    let F := reducedFamily L S
    let H := V F x 1 ⊓ V F (base F (!i)) 1
    ⁅H, Q F (base F i)⁆ = Z F (base F i) ∧
      ⁅H.map (G₀ L S).subtype, (parabolic L S (if i then 1 else 0)).pCoreIn 2⁆ =
        (Z F (base F i)).map (G₀ L S).subtype ∧
      V F (base F (!i)) 1 = ⁅V F (base F (!i)) 1, star L S (!i)⁆ ∧
      (V F (base F (!i)) 1).map (G₀ L S).subtype =
        ⁅(V F (base F (!i)) 1).map (G₀ L S).subtype,
          starredParabolic L S (if !i then 1 else 0)⁆ := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let H := V F x 1 ⊓ V F y 1
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  have hadj : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hnot := source_suzuki_intersection_not_central h i hb hxadj hne T R hT hR e
    hz hcard hcardy hzx hzy hcommx hcommy.le hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa
  have hgen : star L S i = (Q F x ⊔ Q F y) ⊔ Q F m := by
    have hh := star_three_core_generation h i hxadj hne T R hT hR
    simpa only [sup_comm, sup_left_comm, sup_assoc] using hh
  have hnH : star L S i ≤ normalizer (H : Set (G₀ L S)) := by
    rw [hgen]
    exact intersection_normalized F (fun v => (source_Z_Q_U (reduced_triple h) v).2)
      hxadj.symm hadj.symm hcommx hcommy.le hzx hzy
  have hZA : Z F m ≤ star L S i :=
    ((hZ m).trans (map_subtype_le _)).trans
      ((star_core h i).ge.trans (map_subtype_le _))
  have hnZ : star L S i ≤ normalizer (Z F m : Set (G₀ L S)) :=
    (star_le_stabilizer i).trans
      ((normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer F m)).mp (Z_normal F m))
  let : ((Z F m).subgroupOf (star L S i)).Normal :=
    normal_subgroupOf_of_le_normalizer hnZ
  let : IsMinimalNormal ((Z F m).subgroupOf (star L S i)) :=
    ⟨fun N _ hN => hmin N inferInstance hN⟩
  have he : ⁅H,Q F m⁆ = Z F m :=
    (intersection_commutator_dichotomy F (star L S i) (star_le_stabilizer i) hZA hnH
      (intersection_commutator_le_center F hcommx hcommy.le hzx hzy hprod)).resolve_right hnot
  have hQy : Q F y ≤ star L S (!i) :=
    (le_sup_right.trans hRy.ge).trans (map_subtype_le _)
  have hQm : Q F m ≤ star L S (!i) :=
    (le_sup_left.trans hRy.ge).trans (map_subtype_le _)
  obtain ⟨hv,hvOriginal⟩ := source_span_commutator_of_intersection h (star L S (!i))
    (star_le_stabilizer (!i)) hadj.symm
    (fun z hz => star_locally_transitive h (!i) hadj.symm hz) hQy hQm hcommy he
  have hcore : (Q F m).map (G₀ L S).subtype =
      (parabolic L S (if i then 1 else 0)).pCoreIn 2 := by
    rw [← star_core h i, ← Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective
      2 _ (G₀ L S).subtype_injective]
    change (((starredParabolic L S (if i then 1 else 0)).subgroupOf (G₀ L S)).map
      (G₀ L S).subtype).pCoreIn 2 = _
    rw [map_subgroupOf_eq_of_le (star_le_completion _)]
    exact h.starredParabolic_same_core _
  refine ⟨he, ?_, hv, ?_⟩
  · have hh := congrArg (Subgroup.map (G₀ L S).subtype) he
    rwa [map_commutator, hcore] at hh
  · have hstar : (star L S (!i)).map (G₀ L S).subtype =
        starredParabolic L S (if !i then 1 else 0) :=
      map_subgroupOf_eq_of_le (star_le_completion _)
    rwa [hstar] at hvOriginal

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
