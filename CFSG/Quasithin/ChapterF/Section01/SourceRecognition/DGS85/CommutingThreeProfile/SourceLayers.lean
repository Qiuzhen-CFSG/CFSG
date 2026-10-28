module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.Reduced
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.CenterLayerAction

/-!
# The center layer in the original and reduced F1.11 pair

Use the published reduced graph, its whole Borel and its original completion
inclusion. The original starred endpoint, restricted to G0, has exactly the
graph vertex core. Its quotient is marked by the original local quotient,
and the representative maps are the original inclusions.

From the explicit earlier 6.2(d) Sylow conclusion and b=3, the actual critical
pair supplies a proper elementary center layer inside the radius-two kernel.
The Chapter 8 commutator identity constructs its quotient representation;
pulling back along the marked equivalence gives the literal original local
action. Mapping the span back into the original completion places it in the
original parabolic two-core.

Sources: DGS85 (6.2)(d), (8.1), (8.6)--(8.7), recalled as (12.1),
printed pp.178--183; Aschbacher--Smith F.1.9. The Chapter 6 and Chapter 8
premises retain their separate existing producers. These applications do
not prove the later 12.3--12.9 bounds, irreducibility or TYPE alternatives.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.AmalgamLocalCores
open Reduction
namespace ReducedLayer
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The original starred endpoint, with its literal inclusion in the reduced completion. -/
abbrev star (L : Fin 2 → Subgroup G) (S : Subgroup G) (i : Bool) : Subgroup (G₀ L S) :=
  (starredParabolic L S (if i then 1 else 0)).subgroupOf (G₀ L S)

/-- Both reduced endpoints lie in the same reduced completion. -/
theorem endpoint_le_completion (i : Fin 2) : P₀ L S i ≤ G₀ L S := by
  fin_cases i
  · exact le_sup_left
  · exact le_sup_right

/-- Each original starred endpoint lies in its reduced endpoint and completion. -/
theorem star_le_completion (i : Fin 2) : starredParabolic L S i ≤ G₀ L S :=
  (show starredParabolic L S i ≤ P₀ L S i from le_sup_left).trans (endpoint_le_completion i)

/-- The original starred endpoint acts inside the corresponding graph stabilizer. -/
theorem star_le_stabilizer (i : Bool) :
    star L S i ≤ stabilizer (reducedFamily L S) (base (reducedFamily L S) i) := by
  rw [stabilizer, Subgroup.CosetGeometry.stabilizer_base]
  cases i
  · exact subgroupOf_mono _ (show starredParabolic L S 0 ≤ P₀ L S 0 from le_sup_left)
  · exact subgroupOf_mono _ (show starredParabolic L S 1 ≤ P₀ L S 1 from le_sup_left)

/-- Reduction and restriction preserve the same embedded intrinsic two-core. -/
theorem star_core (h : HypothesisF11 L S) (i : Bool) :
    (star L S i).pCoreIn 2 = Q (reducedFamily L S) (base (reducedFamily L S) i) := by
  apply map_injective (G₀ L S).subtype_injective
  have hQ : (Q (reducedFamily L S) (base (reducedFamily L S) i)).map (G₀ L S).subtype =
      (parabolic L S (if i then 1 else 0)).pCoreIn 2 := by
    unfold Q stabilizer
    rw [Subgroup.CosetGeometry.stabilizer_base]
    have he : reducedFamily L S i = (P₀ L S (if i then 1 else 0)).subgroupOf (G₀ L S) := by
      cases i <;> rfl
    rw [he, ← pCoreIn_map_of_injective 2 _ (G₀ L S).subtype_injective,
      map_subgroupOf_eq_of_le (endpoint_le_completion _), P₀_core h]
  rw [hQ, ← pCoreIn_map_of_injective 2 _ (G₀ L S).subtype_injective]
  change ((starredParabolic L S (if i then 1 else 0)).subgroupOf (G₀ L S) |>.map
    (G₀ L S).subtype).pCoreIn 2 = _
  rw [map_subgroupOf_eq_of_le (star_le_completion _)]
  exact h.starredParabolic_same_core _

/-- The original local quotient marks the actual reduced starred quotient. -/
def originalQuotient (h : HypothesisF11 L S) (i : Bool) :
    (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      (star L S i ⧸ pCore 2 (star L S i)) :=
  (h.starredQuotientEquiv _).trans
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe (star_le_completion _)).symm
      (pCore_map_iso 2 _))

/-- The quotient marking retains both original inclusion maps on representatives. -/
theorem originalQuotient_mk (h : HypothesisF11 L S) (i : Bool)
    (x : L (if i then 1 else 0)) :
    originalQuotient h i (QuotientGroup.mk x) =
      QuotientGroup.mk ((subgroupOfEquivOfLe (star_le_completion _)).symm
        (inclusion (local_le_starredParabolic _) x)) := rfl

/-- An original local actor, carried by inclusion into the reduced completion. -/
def originalActor (i : Bool) (x : L (if i then 1 else 0)) : star L S i :=
  (subgroupOfEquivOfLe (star_le_completion _)).symm
    (inclusion (local_le_starredParabolic _) x)

/-- The actor in the original ambient group is exactly the original element. -/
theorem originalActor_coe (i : Bool) (x : L (if i then 1 else 0)) :
    (((originalActor (L := L) (S := S) i x : star L S i) : G₀ L S) : G) = (x : G) := rfl

/-- The original starred endpoint preserves the geometric center span. -/
theorem star_normalizes_span (h : HypothesisF11 L S) (i : Bool) :
    star L S i ≤ normalizer
      (V (reducedFamily L S) (base (reducedFamily L S) i) 1 : Set (G₀ L S)) := by
  let : ∀ i, Finite (reducedFamily L S i) := finite_endpoints (reduced_triple h)
  exact (star_le_stabilizer i).trans (stabilizer_normalizes_V _ _ 1)

/-- The literal original local quotient acts on the actual graph center layer. -/
theorem source_center_layer_action (h : HypothesisF11 L S)
    (hSyl : ∀ v, ∃ T : Sylow 2 (U (reducedFamily L S) v),
      (T : Subgroup (U (reducedFamily L S) v)).map (U (reducedFamily L S) v).subtype =
        Q (reducedFamily L S) v)
    (hb : 2 < b (reducedFamily L S)) (i : Bool)
    (hcomm : ⁅V (reducedFamily L S) (base (reducedFamily L S) i) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) i)⁆ ≤
        Z (reducedFamily L S) (base (reducedFamily L S) i)) :
    let F := reducedFamily L S
    let v := base F i
    let := V_elementary F (reduced_triple h).generate
      (fun w => (source_Z_Q_U (reduced_triple h) w).1) hSyl hb v
    let : ((Z F v).subgroupOf (V F v 1)).Normal := normal_of_isMulCommutative _
    ∃ ρ : Representation (ZMod 2)
      (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0)))
      (Additive (V F v 1 ⧸ (Z F v).subgroupOf (V F v 1))),
      ∀ x : L (if i then 1 else 0), ∀ y : V F v 1,
        (ρ (QuotientGroup.mk x) (Additive.ofMul (QuotientGroup.mk y))).toMul =
          QuotientGroup.mk ⟨(originalActor (L := L) (S := S) i x : G₀ L S) * y *
            (originalActor (L := L) (S := S) i x : G₀ L S)⁻¹,
            (mem_normalizer_iff.mp (star_normalizes_span h i (originalActor (L := L) (S := S) i x).property)
              y).mp y.property⟩ := by
  let : ∀ i, Finite (reducedFamily L S i) := finite_endpoints (reduced_triple h)
  let F := reducedFamily L S
  let v := base F i
  have hgen : F false ⊔ F true = ⊤ := (reduced_triple h).generate
  have hZ := fun w => (source_Z_Q_U (reduced_triple h) w).1
  let := V_elementary F hgen hZ hSyl hb v
  let : ((Z F v).subgroupOf (V F v 1)).Normal := normal_of_isMulCommutative _
  obtain ⟨σ, hσ⟩ := exists_center_layer_action F hgen hZ hSyl hb v (star L S i)
    (star_le_stabilizer i) (star_core h i).le hcomm
  refine ⟨σ.comp (originalQuotient h i).toMonoidHom, ?_⟩
  intro x y
  exact hσ (originalActor (L := L) (S := S) i x) y

/-- A genuine reduced critical pair supplies the proper elementary radius-two layer. -/
theorem source_critical_layer (h : HypothesisF11 L S)
    (hSyl : ∀ v, ∃ T : Sylow 2 (U (reducedFamily L S) v),
      (T : Subgroup (U (reducedFamily L S) v)).map (U (reducedFamily L S) v).subtype =
        Q (reducedFamily L S) v)
    (hb : b (reducedFamily L S) = 3) :
    ∃ a a' beta : Vertex (reducedFamily L S),
      IsCriticalPair (reducedFamily L S) a a' ∧
      (graph (reducedFamily L S)).Adj a beta ∧
      (graph (reducedFamily L S)).dist beta a' = 2 ∧
      Z (reducedFamily L S) beta < V (reducedFamily L S) beta 1 ∧
      IsElementaryAbelian 2 (V (reducedFamily L S) beta 1) ∧
      V (reducedFamily L S) beta 1 ≤ Q (reducedFamily L S) beta ∧
      V (reducedFamily L S) beta 1 ≤ ballKernel (reducedFamily L S) beta 2 := by
  let : ∀ i, Finite (reducedFamily L S i) := finite_endpoints (reduced_triple h)
  have hgen : reducedFamily L S false ⊔ reducedFamily L S true = ⊤ :=
    (reduced_triple h).generate
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  obtain ⟨a, a', hc⟩ := reduced_criticalPair h
  obtain ⟨beta, ha, hd, hstrict, hrad⟩ := critical_three_neighbor _ hgen hb hc
  exact ⟨a, a', beta, hc, ha, hd, hstrict,
    V_elementary _ hgen hZ hSyl (by omega) beta,
    V_le_Q _ hgen hZ hSyl (by omega) beta, hrad⟩

/-- The graph span maps into the original parabolic two-core, with the original S retained. -/
theorem source_span_le_original_core (h : HypothesisF11 L S)
    (hSyl : ∀ v, ∃ T : Sylow 2 (U (reducedFamily L S) v),
      (T : Subgroup (U (reducedFamily L S) v)).map (U (reducedFamily L S) v).subtype =
        Q (reducedFamily L S) v)
    (hb : 2 < b (reducedFamily L S)) (i : Bool) :
    (V (reducedFamily L S) (base (reducedFamily L S) i) 1).map (G₀ L S).subtype ≤
      (parabolic L S (if i then 1 else 0)).pCoreIn 2 := by
  let : ∀ i, Finite (reducedFamily L S i) := finite_endpoints (reduced_triple h)
  have hV := V_le_Q (reducedFamily L S) (reduced_triple h).generate
    (fun w => (source_Z_Q_U (reduced_triple h) w).1) hSyl hb
    (base (reducedFamily L S) i)
  rw [← star_core h i] at hV
  have hm := map_mono (f := (G₀ L S).subtype) hV
  rw [← pCoreIn_map_of_injective 2 _ (G₀ L S).subtype_injective] at hm
  change _ ≤ ((starredParabolic L S (if i then 1 else 0)).subgroupOf (G₀ L S) |>.map
    (G₀ L S).subtype).pCoreIn 2 at hm
  rw [map_subgroupOf_eq_of_le (star_le_completion _)] at hm
  exact hm.trans_eq (h.starredParabolic_same_core _)

end ReducedLayer
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
