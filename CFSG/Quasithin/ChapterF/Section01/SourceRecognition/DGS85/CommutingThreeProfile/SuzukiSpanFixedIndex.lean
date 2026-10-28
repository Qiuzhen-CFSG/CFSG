module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiSeedFixedIndex

/-!
# The geometric fixed-index bound for the whole distant span

At the linear middle vertex, local transitivity and its root orbit construct
an element swapping the two Suzuki neighbors. Let H = (Q_x ∩ Q_y)V_x.
The existing core-span count gives [Q_x:H] ≤ q². The commutator identity at
y and center inclusion show [H,V_y] ≤ V_x. Swap x and y: the resulting
subgroup of Q_y has index at most q² and centralizes all of V_x modulo
G_y². This strengthens the individual-center bound to the actual span
used by SuzukiSpanPair, without an assumed reverse critical pair or bound.

The common field, common Sylows and (12.1) center/commutator inputs retain
their source roles. The actual second-kernel upper bound and irreducible
quotient application are in SuzukiSecondKernelUpper.

Source: DGS85, Groups and Graphs, (12.1), (12.3)(a), (12.6),
printed pp.178--183.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
open BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem linear_neighbor_swap
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    {x y : Vertex (reducedFamily L S)}
    (hx : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x)
    (hy : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) y)
    (hne : x ≠ y) :
    ∃ g ∈ stabilizer (reducedFamily L S) (base (reducedFamily L S) i),
      g • x = y ∧ g • y = x := by
  let F := reducedFamily L S
  obtain ⟨a,ha,hax⟩ := star_locally_transitive h i hx hy
  have ham : a • base F i = base F i := star_le_stabilizer i ha
  have hay : (graph F).Adj (base F i) (a • y) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F a).map_adj_iff.mpr hy
    change (graph F).Adj (a • base F i) (a • y) at hh
    rwa [ham] at hh
  have hny : a • y ≠ y := by
    intro he
    exact hne ((MulAction.injective a) (hax.trans he.symm))
  obtain ⟨t,ht,hty⟩ := linear_incident_core_transitive h i e hy hay hx hny hne
  have ht' := pCoreIn_le 2 (stabilizer F y ⊓ stabilizer F (base F i)) ht
  refine ⟨t*a,(stabilizer F (base F i)).mul_mem ht'.2 (star_le_stabilizer i ha),?_,?_⟩
  · rw [mul_smul,hax]
    exact ht'.1
  · rw [mul_smul,hty]


/-- The whole distant span fixes a subgroup of index at most q² in the literal second-kernel section. -/
theorem source_suzuki_span_fixed_index
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
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) i) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcomm : ⁅V (reducedFamily L S) (base (reducedFamily L S) i) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) i)⁆ ≤
        Z (reducedFamily L S) (base (reducedFamily L S) i)) :
    let F := reducedFamily L S
    (commutatorPreimage (Q F (base F i)) (V F x 1)
      (ballKernel F (base F i) 2)).relIndex (Q F (base F i)) ≤ (2^(2*n+1))^2 := by
  let F := reducedFamily L S
  let y := base F i
  let m := base F (!i)
  let H := (Q F x ⊓ Q F y) ⊔ V F x 1
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite (Q F y) := Finite.of_injective (inclusion (Q_le_stabilizer F y))
    (inclusion_injective _)
  have hadj : (graph F).Adj y m :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  have hVy : V F y 1 ≤ Q F m := V_le_neighbor_Q F (reduced_triple h).generate
    hZ (reduced_kernel_sylow h) hb hadj
  have hVyx : V F y 1 ≤ stabilizer F x := hVy.trans
    ((source_Z_Q_U (reduced_triple h) m).2.trans
      ((ballKernel_one_le_edge F hxm.symm).trans inf_le_right))
  have hVX : V F x 1 ≤ Q F x :=
    V_le_Q F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb x
  have hcommH : ⁅H,V F y 1⁆ ≤ V F x 1 := by
    apply commutator_sup_le_of_relative_normal (stabilizer F x)
      (Q F x ⊓ Q F y) (V F x 1) (V F y 1) (V F x 1)
      (stabilizer_normalizes_V F x 1)
      (inf_le_left.trans (Q_le_stabilizer F x)) (hVX.trans (Q_le_stabilizer F x))
    · have hh : ⁅V F y 1,Q F x ⊓ Q F y⁆ ≤ Z F y :=
        (commutator_mono le_rfl inf_le_right).trans hcomm
      rw [commutator_comm] at hh
      exact hh.trans (hzy.trans (Z_neighbor_le_V F hxm))
    · exact le_normalizer_iff_commutator_le_left.mp
        (hVyx.trans (stabilizer_normalizes_V F x 1))
  have hxy : x ≠ y := by
    intro he
    apply hc.2
    have hh := (Z_neighbor_le_V F hxa).trans hVX
    rw [he] at hh
    exact hh.trans (source_Z_Q_U (reduced_triple h) y).2
  obtain ⟨g,hgm,hgx,hgy⟩ := linear_neighbor_swap h (!i) eLin hxm.symm hadj.symm hxy
  let f := (MulAut.conj g).toMonoidHom
  have hQ : (Q F x).map f = Q F y := by rw [←Q_translate F,hgx]
  have hX : (V F x 1).map f = V F y 1 := by rw [←V_translate F,hgx]
  have hY : (V F y 1).map f = V F x 1 := by rw [←V_translate F,hgy]
  have hH : H.map f ≤ commutatorPreimage (Q F y) (V F x 1) (ballKernel F y 2) := by
    apply le_commutatorPreimage
    · exact (map_mono (sup_le inf_le_left hVX)).trans_eq hQ
    · have hh := map_mono (f := f) hcommH
      rw [map_commutator,hX,hY] at hh
      exact hh.trans (V_le_ballKernel F (reduced_triple h).generate y
        (i := 1) (j := 2) (by change 3 ≤ b (reducedFamily L S); omega))
  have hi : (H.map f).relIndex (Q F y) ≤ (2^(2*n+1))^2 := by
    rw [←hQ,relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
    exact source_suzuki_core_span_index h i hb hc hxa hxm hn hq eSuz eLin T hT R hR
  exact (relIndex_le_of_le_left hH
    (show ((H.map f).subgroupOf (Q F y)).index ≠ 0 from index_ne_zero_of_finite)).trans hi


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
