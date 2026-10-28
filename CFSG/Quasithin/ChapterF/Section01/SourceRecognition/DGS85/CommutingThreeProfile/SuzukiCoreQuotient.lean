module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiCoreBounds

/-!
# The literal central quotient of the middle core

For the nonbinary Suzuki neighbors x,y of the linear middle vertex m,
write N = (Q_x ∩ Q_m)(Q_y ∩ Q_m). The earlier common-Sylow markings give
three-core generation in the actual starred middle endpoint. SuzukiCoreBounds
then shows that Q_m/N is central in that endpoint modulo N and has order
dividing q. The conclusion constructs the relative-normality witness and
uses the actual quotient map; it also preserves the ordered product and
index bound after inclusion in the original completion.

This is a reduction of the middle-core-product obligation on DGS85 p.180,
not its completion: the central quotient still must be proved trivial.
The critical geometry and common Sylows are explicit earlier Chapter 8
inputs. This result does not assume a TYPE output, middle-core product,
center-kernel bound, or recognition callback. It does not treat Sz(2) or
establish the later alternatives (12.9) and (13.1).

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.1), (12.3)(a), printed pp.178--180.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction
open BenderSuzuki.MatrixGroups BenderSuzuki.Converse
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The actual middle-core quotient is central of order dividing q, with original product transport. -/
theorem source_suzuki_middle_core_central_quotient
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {a x : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) i))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hxm : (graph (reducedFamily L S)).Adj x (base (reducedFamily L S) (!i)))
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL2 k)
    (R : Sylow 2 (star L S i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (T U : Sylow 2 (star L S (!i)))
    (hT : (T : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hU : (U : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) (!i))) :
    let F := reducedFamily L S
    let A := star L S (!i)
    let m := base F (!i)
    let y := base F i
    let N := (Q F x ⊓ Q F m) ⊔ (Q F y ⊓ Q F m)
    (N.map (G₀ L S).subtype : Set G) =
      ((Q F x ⊓ Q F m).map (G₀ L S).subtype : Set G) *
        ((Q F y ⊓ Q F m).map (G₀ L S).subtype : Set G) ∧
    (N.map (G₀ L S).subtype).relIndex
      ((parabolic L S (if !i then 1 else 0)).pCoreIn 2) ∣ 2 ^ (2 * n + 1) ∧
    ∃ hN : (N.subgroupOf A).Normal,
      let : (N.subgroupOf A).Normal := hN
      ((Q F m).subgroupOf A).map (QuotientGroup.mk' (N.subgroupOf A)) ≤
        center (A ⧸ N.subgroupOf A) ∧
      Nat.card (((Q F m).subgroupOf A).map (QuotientGroup.mk' (N.subgroupOf A))) ∣
        2 ^ (2 * n + 1) := by
  let F := reducedFamily L S
  let A := star L S (!i)
  let m := base F (!i)
  let y := base F i
  let N := (Q F x ⊓ Q F m) ⊔ (Q F y ⊓ Q F m)
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hQU := fun v => (source_Z_Q_U (reduced_triple h) v).2
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
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
    simpa only [Bool.not_not, sup_comm, sup_left_comm, sup_assoc] using hh
  obtain ⟨_, hd, _, hi⟩ := source_suzuki_middle_core_bounds h i hb hc hxa hxm hn eSuz eLin R hR
  have hnorm : A ≤ normalizer (N : Set (G₀ L S)) :=
    middle_core_product_normalizer F hQU hxm hadj A hgen
  have hcomm : ⁅Q F m,A⁆ ≤ N :=
    middle_core_commutator_le_product F hQU hxm hadj A hgen hd
  have hQA : Q F m ≤ A := le_sup_right.trans hgen.ge
  have hcore : (Q F m).map (G₀ L S).subtype =
      (parabolic L S (if !i then 1 else 0)).pCoreIn 2 := by
    rw [← star_core h (!i), ← Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective
      2 _ (G₀ L S).subtype_injective]
    change (((starredParabolic L S (if !i then 1 else 0)).subgroupOf (G₀ L S)).map
      (G₀ L S).subtype).pCoreIn 2 = _
    rw [map_subgroupOf_eq_of_le (star_le_completion _)]
    exact h.starredParabolic_same_core _
  refine ⟨?_, ?_, ?_⟩
  · have hset := middle_core_product_as_set F hQU (y := y) hxm
    have himage := congrArg (fun X : Set (G₀ L S) => (G₀ L S).subtype '' X) hset
    rw [Set.image_mul] at himage
    exact himage
  · rw [← hcore, relIndex_map_map_of_injective _ _ (G₀ L S).subtype_injective]
    exact hi
  let hN : (N.subgroupOf A).Normal := normal_subgroupOf_of_le_normalizer hnorm
  refine ⟨hN, ?_⟩
  let : (N.subgroupOf A).Normal := hN
  constructor
  ·
    rintro _ ⟨c, hc, rfl⟩
    apply mem_center_iff.mpr
    intro z
    induction z using QuotientGroup.induction_on with
    | H z =>
      symm
      apply commutatorElement_eq_one_iff_mul_comm.mp
      change ⁅(QuotientGroup.mk' (N.subgroupOf A)) c,
        (QuotientGroup.mk' (N.subgroupOf A)) z⁆ = 1
      rw [← map_commutatorElement]
      apply (QuotientGroup.eq_one_iff _).mpr
      change ⁅(c : G₀ L S),(z : G₀ L S)⁆ ∈ N
      exact hcomm (commutator_mem_commutator hc z.property)
  · have hcard : Nat.card (((Q F m).subgroupOf A).map
        (QuotientGroup.mk' (N.subgroupOf A))) = N.relIndex (Q F m) := by
      rw [← relIndex_ker, QuotientGroup.ker_mk', relIndex_subgroupOf hQA]
    rwa [hcard]

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
