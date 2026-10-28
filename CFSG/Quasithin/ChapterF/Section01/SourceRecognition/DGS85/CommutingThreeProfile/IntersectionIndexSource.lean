module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.LinearIntersectionIndex
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SourceLayers
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.KernelSylow

/-!
# The moved neighbor and linear index on the reduced source graph

The nonzero branch commutator selects a neighbor different from the middle
vertex, with nonzero action and escape from its core. F1.11 supplies the
full-kernel Sylow through `reduced_kernel_sylow`, so that premise is fully
discharged. The commutator and escape persist under the literal inclusion
of the reduced completion into the original group.

At a selected linear endpoint, the original local quotient marking and the
same-core theorem identify the action kernel with the actual graph core.
A complement fixing the two intersection vertices and supplementing the
marked Sylow forces the intersection image to be that whole Sylow. This
gives index |k| both in the reduced graph and relative to the original
parabolic core, together with a surjective field coordinate map and its
representative formula through the original quotient.

Source: DGS85, Groups and Graphs, (12.3)(a), printed p.179. The linear
marking is the earlier (12.1)(e) input. Constructing the complement and its
normalizer supplement, identifying the printed two-term denominator, and
proving the other index in (12.3)(a) remain with this Chapter 12 family.
This application does not assert (12.3)(c), (12.9), or (13.1).
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open Subgroup.CosetGeometry.RankTwo
open Reduction
open Theory.GroupTheory.AmalgamLocalCores
namespace ReducedLayer
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The source branch supplies a moved neighbor, retaining the original inclusion. -/
theorem source_intersection_moved_neighbor (h : HypothesisF11 L S)
    (hb : 2 < b (reducedFamily L S)) {x y m : Vertex (reducedFamily L S)}
    (hxm : (graph (reducedFamily L S)).Adj x m)
    (hym : (graph (reducedFamily L S)).Adj y m)
    (hmove : ⁅V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) y,
      V (reducedFamily L S) y 1⁆ ≠ ⊥) :
    let F := reducedFamily L S
    let W := V F x 1 ⊓ Q F y
    Q F m ≤ normalizer (W : Set (G₀ L S)) ∧
      ∃ z, (graph F).Adj y z ∧ z ≠ m ∧ ⁅W, Z F z⁆ ≠ ⊥ ∧ ¬ W ≤ Q F z ∧
        ⁅W.map (G₀ L S).subtype, (Z F z).map (G₀ L S).subtype⁆ ≠ ⊥ ∧
        ¬ W.map (G₀ L S).subtype ≤ (Q F z).map (G₀ L S).subtype := by
  let F := reducedFamily L S
  let : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  obtain ⟨z, hz, hzm, hzcomm, hzcore⟩ := intersection_moved_neighbor F
    (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb hxm hmove
  refine ⟨core_intersection_normalized_by_middle F
    (fun v => (source_Z_Q_U (reduced_triple h) v).2) hxm hym,
    z, hz, hzm, hzcomm, hzcore, ?_, ?_⟩
  · rw [← map_commutator]
    exact fun he => hzcomm ((map_eq_bot_iff_of_injective _ (G₀ L S).subtype_injective).mp he)
  · exact fun he => hzcore ((map_le_map_iff_of_injective (G₀ L S).subtype_injective).mp he)

/-- The exact conditional index and coordinates for the original/starred linear quotient. -/
theorem source_linear_intersection_index
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    {x y : Vertex (reducedFamily L S)}
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    (hW : V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) y ≤ star L S i)
    (hmove : ⁅V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) y,
      Z (reducedFamily L S) (base (reducedFamily L S) i)⁆ ≠ ⊥)
    (T : Sylow 2 SL(2,k)) (K : Subgroup (star L S i))
    (hT : ((V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) y).subgroupOf
        (star L S i)).map (((originalQuotient h i).symm.trans e).toMonoidHom.comp
          (QuotientGroup.mk' (pCore 2 (star L S i)))) ≤ T)
    (hKx : K.map (star L S i).subtype ≤ stabilizer (reducedFamily L S) x)
    (hKy : K.map (star L S i).subtype ≤ stabilizer (reducedFamily L S) y)
    (hcover : (T : Subgroup SL(2,k)) ⊔ K.map
        (((originalQuotient h i).symm.trans e).toMonoidHom.comp
          (QuotientGroup.mk' (pCore 2 (star L S i)))) = normalizer (T : Set SL(2,k))) :
    let F := reducedFamily L S
    let W := V F x 1 ⊓ Q F y
    (Q F (base F i)).relIndex W = Nat.card k ∧
      ((parabolic L S (if i then 1 else 0)).pCoreIn 2).relIndex
        (W.map (G₀ L S).subtype) = Nat.card k ∧
      ∃ f : W →* Multiplicative k, Function.Surjective f ∧
        f.ker = (Q F (base F i)).subgroupOf W ∧
        ∀ w, ((Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 T) (f w) : SL(2,k)) =
          e ((originalQuotient h i).symm
            (QuotientGroup.mk' (pCore 2 (star L S i)) ⟨w, hW w.property⟩)) := by
  let F := reducedFamily L S
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hescape : ¬ V F x 1 ⊓ Q F y ≤ Q F (base F i) := by
    intro hc
    apply hmove
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mpr
    intro z hz
    exact centralizer_le hc
      ((mem_omegaCenterIn_iff _ _).mp ((source_Z_Q_U (reduced_triple h) (base F i)).1 hz)).2.1
  obtain ⟨_, hindex, f, hf, hfker, hmark⟩ := linear_core_intersection_index F
    (star L S i) (star_core h i) ((originalQuotient h i).symm.trans e)
    hW hescape T K hT hKx hKy hcover
  have hcore : (Q F (base F i)).map (G₀ L S).subtype =
      (parabolic L S (if i then 1 else 0)).pCoreIn 2 := by
    rw [← star_core h i, ← pCoreIn_map_of_injective 2 _ (G₀ L S).subtype_injective]
    change (((starredParabolic L S (if i then 1 else 0)).subgroupOf (G₀ L S)).map
      (G₀ L S).subtype).pCoreIn 2 = _
    rw [map_subgroupOf_eq_of_le (star_le_completion _)]
    exact h.starredParabolic_same_core _
  refine ⟨hindex, ?_, f, hf, hfker, hmark⟩
  rw [← hcore, relIndex_map_map_of_injective _ _ (G₀ L S).subtype_injective]
  exact hindex

end ReducedLayer
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
