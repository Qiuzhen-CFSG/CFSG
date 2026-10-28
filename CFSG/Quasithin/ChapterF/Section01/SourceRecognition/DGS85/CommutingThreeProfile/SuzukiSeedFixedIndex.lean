module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiIndices
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.CommonSylowIndex
public import Theory.GroupTheory.CoreSpanIndex
public import Theory.GroupTheory.CommutatorPreimage

/-!
# The geometric q² seed bound for the second-kernel layer

On the path a--x--m--y, the marked common Sylows give [Q_x:Q_x ∩ Q_m] = q
and [Q_m:Q_m ∩ Q_y] = q². The proved first index in (12.3)(a) gives
[V_x:V_x ∩ Q_y] = q. Thus H = (Q_x ∩ Q_y)V_x has index at most q² in Q_x.
No index bound is supplied as a hypothesis of the source application.

For every neighbor z of y, [Q_x ∩ Q_y,Z_z] lies in Z_y ≤ Z_m ≤ V_x.
The other factor V_x is normalized by Z_z: the distant seed lies in Q_m,
which fixes x. Hence [H,Z_z] ≤ V_x ≤ G_x^(2). The literal preimage of
the seed-fixed part of Q_x/G_x^(2) consequently has index at most q².

The natural parameter equality, common Sylows, center inclusion and
commutator identity retain their earlier (12.1) source roles. This treats
q > 2, the range of the reused first-index proof. Combining two seed
bounds needs the actual two-seed generation and absence of fixed cosets;
this module does not assert the still-unfinished q⁴ bound or selection.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.1)(c,e,f), (12.3)(a), (12.6), printed pp.178--183.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
open BenderSuzuki.MatrixGroups
namespace ReducedLayer
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The literal core intersection enlarged by the radius-one span has index at most q². -/
theorem source_suzuki_core_span_index
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (hb : 2 < b (reducedFamily L S))
    {a x : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) i))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hxm : (graph (reducedFamily L S)).Adj x (base (reducedFamily L S) (!i)))
    {n : ℕ} (hn : 0 < n) (hq : Nat.card k = 2^(2*n+1))
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      SuzukiMatrixGroup n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃*
      SL(2,k))
    (T : Sylow 2 (star L S (!i)))
    (hT : (T : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (R : Sylow 2 (star L S i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i)) :
    let F := reducedFamily L S
    ((Q F x ⊓ Q F (base F i)) ⊔ V F x 1).relIndex (Q F x) ≤ (2^(2*n+1))^2 := by
  let F := reducedFamily L S
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite (Q F x) := Finite.of_injective (inclusion (Q_le_stabilizer F x))
    (inclusion_injective _)
  let : Finite (Q F (base F (!i))) := Finite.of_injective
    (inclusion (Q_le_stabilizer F (base F (!i)))) (inclusion_injective _)
  have hadj : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨P,_,hi,_⟩ := source_common_sylow_core_index h (!i) eLin T hT
  have hlin : (Q F (base F (!i))).relIndex (Q F x) = 2^(2*n+1) := by
    rw [inf_relIndex_left] at hi
    exact hi.trans ((Nat.card_congr
      (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 P).symm.toEquiv).trans hq)
  obtain ⟨U,_,hj,_⟩ := source_common_sylow_core_index h i eSuz R hR
  have hsuz : (Q F (base F i)).relIndex (Q F (base F (!i))) = (2^(2*n+1))^2 := by
    rw [inf_relIndex_left] at hj
    exact hj.trans (suzukiSylow_card hn (MulEquiv.refl _) U)
  have hv := (source_suzuki_first_index h i hb hc hxa hxm hadj hn eSuz eLin R hR).1
  rw [inf_relIndex_left] at hv
  exact core_span_index_bound (Q F x) (Q F (base F (!i))) (Q F (base F i)) (V F x 1)
    (by positivity) (V_le_Q F (reduced_triple h).generate
      (fun z => (source_Z_Q_U (reduced_triple h) z).1) (reduced_kernel_sylow h) hb x)
    hlin hsuz hv

/-- The distant center fixes a subgroup of index at most q² in the actual
second-kernel quotient. Both index estimates are derived from the marked
common Sylows and the previously proved first intersection index. -/
theorem source_suzuki_seed_fixed_index
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (hb : 2 < b (reducedFamily L S))
    {a x z : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) i))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hxm : (graph (reducedFamily L S)).Adj x (base (reducedFamily L S) (!i)))
    (hyz : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) z)
    {n : ℕ} (hn : 0 < n) (hq : Nat.card k = 2^(2*n+1))
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      SuzukiMatrixGroup n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃*
      SL(2,k))
    (T : Sylow 2 (star L S (!i)))
    (hT : (T : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (R : Sylow 2 (star L S i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) i) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcomm : ⁅V (reducedFamily L S) (base (reducedFamily L S) i) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) i)⁆ ≤
        Z (reducedFamily L S) (base (reducedFamily L S) i)) :
    let F := reducedFamily L S
    let H := (Q F x ⊓ Q F (base F i)) ⊔ V F x 1
    ⁅H,Z F z⁆ ≤ V F x 1 ∧
      (commutatorPreimage (Q F x) (Z F z) (ballKernel F x 2)).relIndex (Q F x) ≤
        (2^(2*n+1))^2 := by
  let F := reducedFamily L S
  let y := base F i
  let m := base F (!i)
  let H := (Q F x ⊓ Q F y) ⊔ V F x 1
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite (Q F x) := Finite.of_injective (inclusion (Q_le_stabilizer F x))
    (inclusion_injective _)
  have hadj : (graph F).Adj y m :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  have hVy : V F y 1 ≤ Q F m := V_le_neighbor_Q F (reduced_triple h).generate
    hZ (reduced_kernel_sylow h) hb hadj
  have hZzx : Z F z ≤ stabilizer F x :=
    (Z_neighbor_le_V F hyz).trans (hVy.trans
      ((source_Z_Q_U (reduced_triple h) m).2.trans
        ((ballKernel_one_le_edge F hxm.symm).trans inf_le_right)))
  have hVX : V F x 1 ≤ Q F x :=
    V_le_Q F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb x
  have hcommH : ⁅H,Z F z⁆ ≤ V F x 1 := by
    apply commutator_sup_le_of_relative_normal (stabilizer F x)
      (Q F x ⊓ Q F y) (V F x 1) (Z F z) (V F x 1)
      (stabilizer_normalizes_V F x 1)
      (inf_le_left.trans (Q_le_stabilizer F x)) (hVX.trans (Q_le_stabilizer F x))
    · have hh : ⁅Z F z,Q F x ⊓ Q F y⁆ ≤ Z F y :=
        (commutator_mono (Z_neighbor_le_V F hyz) inf_le_right).trans hcomm
      rw [commutator_comm] at hh
      exact hh.trans (hzy.trans (Z_neighbor_le_V F hxm))
    · exact le_normalizer_iff_commutator_le_left.mp
        (hZzx.trans (stabilizer_normalizes_V F x 1))
  refine ⟨hcommH,?_⟩
  have hHC : H ≤ commutatorPreimage (Q F x) (Z F z) (ballKernel F x 2) :=
    le_commutatorPreimage (sup_le inf_le_left hVX)
      (hcommH.trans (V_le_ballKernel F (reduced_triple h).generate x
        (i := 1) (j := 2) (by change 3 ≤ b (reducedFamily L S); omega)))
  exact (relIndex_le_of_le_left hHC (show (H.subgroupOf (Q F x)).index ≠ 0 from index_ne_zero_of_finite)).trans
    (source_suzuki_core_span_index h i hb hc hxa hxm hn hq eSuz eLin T hT R hR)

end ReducedLayer
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
