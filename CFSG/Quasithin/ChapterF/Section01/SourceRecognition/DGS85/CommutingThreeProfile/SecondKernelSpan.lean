module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.LinearCoreOrbit
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.NeighborSecondKernel
public import Theory.GroupTheory.ConjugateSpanCentralizer
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# The elementary span in the middle second kernel

For the linear middle vertex m and distinct Suzuki-side neighbors x,y,
put R = V_y intersect Q_x and W = <R^(G_m)>. The actual common Sylow
Q_y Q_m is transitive on the neighbors other than y and normalizes R.
Thus R = V_y intersect Q_z for every z different from y. It follows
that R, and hence its full stabilizer span W, fixes the second ball.
The earlier reciprocal intersection commutator then makes all conjugates
of R commute, proving W elementary abelian. We retain the literal normal
closure, its intersections with V_y, and its original inclusion.

These prove the elementary and containment steps (1),(2) on printed p.188,
not the subsequent equality W = G_m^(2). The common Sylow, natural linear
marking and (12.1)(f,g) commutators remain genuine earlier source inputs.
Source: DGS85, Groups and Graphs, (12.9), printed p.188.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The span--core intersection does not depend on the other neighbor. -/
theorem source_linear_span_core_intersection
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {x : Vertex (reducedFamily L S)}
    (hx : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x)
    (hne : x ≠ base (reducedFamily L S) (!i))
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    (hcomm : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ ≤
        Z (reducedFamily L S) (base (reducedFamily L S) (!i))) :
    let F := reducedFamily L S
    let y := base F (!i)
    ∀ z, (graph F).Adj (base F i) z → z ≠ y →
      V F y 1 ⊓ Q F z = V F y 1 ⊓ Q F x := by
  let F := reducedFamily L S
  change 2 < b F at hb
  let m := base F i
  let y := base F (!i)
  let R := V F y 1 ⊓ Q F x
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hy : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  have hQU := fun v => (source_Z_Q_U (reduced_triple h) v).2
  have hZx : Z F y ≤ Q F x := by
    apply Z_le_Q_of_dist_lt_b F hZ (reduced_kernel_sylow h)
    have hd := (connected F (reduced_triple h).generate).dist_triangle (u := y) (v := m) (w := x)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hy.symm,
      SimpleGraph.dist_eq_one_iff_adj.mpr hx] at hd
    omega
  have hQyR : Q F y ≤ normalizer (R : Set (G₀ L S)) :=
    le_normalizer_iff_commutator_le_left.mpr
      (((commutator_mono inf_le_left le_rfl).trans hcomm).trans
        (le_inf (Z_le_V F y 1) hZx))
  have hQmR : Q F m ≤ normalizer (R : Set (G₀ L S)) :=
    (le_inf (((hQU m).trans ((ballKernel_one_le_edge F hy).trans inf_le_right)).trans
      (stabilizer_normalizes_V F y 1))
      (((hQU m).trans ((ballKernel_one_le_edge F hx).trans inf_le_right)).trans
        (CommutingTrivial.stabilizer_normalizes_Q F x))).trans inf_normalizer_le_normalizer_inf
  change ∀ z : Vertex F, (graph F).Adj m z → z ≠ y → V F y 1 ⊓ Q F z = R
  intro z hz hzy
  obtain ⟨t,ht,htx⟩ := linear_common_sylow_transitive h i e T hT hx hz hne hzy
  have hty : t • y = y :=
    (sup_le (Q_le_stabilizer F y)
      ((hQU m).trans ((ballKernel_one_le_edge F hy).trans inf_le_right))) ht
  have he := mem_normalizer_iff_map_conj_eq.mp ((sup_le hQyR hQmR) ht)
  change (V F y 1 ⊓ Q F x).map (MulAut.conj t).toMonoidHom = R at he
  rw [map_inf _ _ _ (MulAut.conj t).injective, ←V_translate F, ←Q_translate F,
    hty,htx] at he
  exact he

/-- The exact source normal span is elementary abelian and lies in the full second kernel. -/
theorem source_linear_second_kernel_span
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {x : Vertex (reducedFamily L S)}
    (hx : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x)
    (hne : x ≠ base (reducedFamily L S) (!i))
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    (hcomm : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ ≤
        Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcross : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) x,
      V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥) :
    let F := reducedFamily L S
    let m := base F i
    let y := base F (!i)
    let R := V F y 1 ⊓ Q F x
    let W := conjugateSpanBy R (stabilizer F m)
    IsElementaryAbelian 2 W ∧ W ≤ ballKernel F m 2 ∧ W ≤ V F m 2 ∧
    stabilizer F m ≤ normalizer (W : Set (G₀ L S)) ∧
    W ⊓ V F y 1 = R ∧ V F x 1 ⊓ V F y 1 ≤ W ∧
    (∀ z, (graph F).Adj m z → W ≤ Q F z) ∧
    W.map (G₀ L S).subtype = conjugateSpanBy (R.map (G₀ L S).subtype)
      ((stabilizer F m).map (G₀ L S).subtype) ∧
    W.map (G₀ L S).subtype ≤ (ballKernel F m 2).map (G₀ L S).subtype := by
  let F := reducedFamily L S
  change 2 < b F at hb
  let m := base F i
  let y := base F (!i)
  let R := V F y 1 ⊓ Q F x
  let P := stabilizer F m
  let W := conjugateSpanBy R P
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hy : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  have hQU := fun v => (source_Z_Q_U (reduced_triple h) v).2
  let := V_elementary F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb y
  have hind := source_linear_span_core_intersection h i hb hx hne T hT e hcomm
  have hRy : R ≤ Q F y := inf_le_left.trans
    (V_le_Q F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb y)
  have hRm : R ≤ Q F m := inf_le_left.trans
    (V_le_neighbor_Q F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb hy.symm)
  have hRz : ∀ z, (graph F).Adj m z → R ≤ Q F z := by
    intro z hz
    by_cases hzy : z = y
    · exact hzy ▸ hRy
    · exact (hind z hz hzy).ge.trans inf_le_right
  have hR2 : R ≤ ballKernel F m 2 := by
    intro g hg z hz
    have hdist : (graph F).edist m z ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp : (2 : ℕ∞) ≠ ⊤) hz
    obtain ⟨p,hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top hdist
    have hlen : p.length ≤ 2 := by
      have hh : (p.length : ℕ∞) ≤ (2 : ℕ∞) := hp ▸ hz
      exact ENat.natCast_le_natCast.mp hh
    cases p with
    | nil => exact Q_le_stabilizer F m (hRm hg)
    | @cons _ u _ hu p =>
      exact hQU u (hRz u hu hg) z (p.edist_le.trans
        (ENat.natCast_le_natCast.mpr (by simpa using hlen)))
  have hW2 : W ≤ ballKernel F m 2 :=
    conjugateSpanBy_le hR2 (stabilizer_le_normalizer_ballKernel F m 2)
  have hWQ : W ≤ Q F m :=
    conjugateSpanBy_le hRm (CommutingTrivial.stabilizer_normalizes_Q F m)
  have hpW : IsPGroup 2 W := (isPGroup_pCoreIn 2 (stabilizer F m)).to_le hWQ
  have hWz : ∀ z, (graph F).Adj m z → W ≤ Q F z := by
    intro z hz
    exact CommutingTrivial.two_subgroup_le_Q F z (reduced_kernel_sylow h z)
      hpW (hW2.trans (ballKernel_succ_le F hz 1))
  have hnorm : P ≤ normalizer (W : Set (G₀ L S)) := le_normalizer_conjugateSpanBy R P
  have hWVy : W ⊓ V F y 1 = R := le_antisymm
    (le_inf inf_le_right (inf_le_left.trans (hWz x hx)))
    (le_inf (le_conjugateSpanBy R P) inf_le_left)
  have hcR : R ≤ centralizer (W : Set (G₀ L S)) := by
    apply le_centralizer_iff.mpr
    change conjugateSpanBy R P ≤ centralizer (R : Set (G₀ L S))
    rw [conjugateSpanBy_eq_iSup_conj]
    apply iSup_le
    intro g
    have hgm : (g : G₀ L S) • m = m := g.property
    have hgy : (graph F).Adj m ((g : G₀ L S) • y) := by
      have hh := (Subgroup.CosetGeometry.translationGraphIso F (g : G₀ L S)).map_adj_iff.mpr hy
      change (graph F).Adj ((g : G₀ L S) • m) ((g : G₀ L S) • y) at hh
      rwa [hgm] at hh
    have hRgW : R.map (MulAut.conj (g : G₀ L S)).toMonoidHom ≤ W := by
      change _ ≤ conjugateSpanBy R P
      rw [conjugateSpanBy_eq_iSup_conj]
      exact le_iSup (fun t : P => R.map (MulAut.conj (t : G₀ L S)).toMonoidHom) g
    have hRgV : R.map (MulAut.conj (g : G₀ L S)).toMonoidHom ≤ V F ((g : G₀ L S) • y) 1 := by
      rw [V_translate]
      exact map_mono inf_le_left
    by_cases hsame : (g : G₀ L S) • y = y
    · rw [hsame] at hRgV
      exact hRgV.trans ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
        (centralizer_le (show R ≤ V F y 1 from inf_le_left)))
    · obtain ⟨t,ht,htx⟩ := linear_common_sylow_transitive h i e T hT hx hgy hne hsame
      have hty : t • y = y :=
        (sup_le (Q_le_stabilizer F y)
          ((hQU m).trans ((ballKernel_one_le_edge F hy).trans inf_le_right))) ht
      have hh := congrArg (Subgroup.map (MulAut.conj t).toMonoidHom) hcross
      rw [map_commutator, map_inf _ _ _ (MulAut.conj t).injective,
        map_inf _ _ _ (MulAut.conj t).injective,
        ←V_translate F, ←V_translate F, ←Q_translate F, ←Q_translate F,
        hty,htx,Subgroup.map_bot,hind _ hgy hsame] at hh
      exact (le_inf hRgV (hRgW.trans (hWz y hy))).trans
        (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hh))
  let : IsMulCommutative W := (conjugateSpanBy_commutative_iff R P).mpr hcR
  let : IsElementaryAbelian 2 R := IsElementaryAbelian.of_le (show R ≤ V F y 1 from inf_le_left)
  have hWel : IsElementaryAbelian 2 W := conjugateSpanBy_elementary_of_commutative R P
  have hWV : W ≤ V F m 2 := conjugateSpanBy_le
    (inf_le_left.trans (Noncommuting.graph_V_adjacent_le hy 1)) (stabilizer_normalizes_V F m 2)
  have hHW : V F x 1 ⊓ V F y 1 ≤ W :=
    (le_inf inf_le_right (inf_le_left.trans
      (V_le_Q F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb x))).trans
      (le_conjugateSpanBy R P)
  exact ⟨hWel,hW2,hWV,hnorm,hWVy,hHW,hWz,map_conjugateSpanBy _ _ _,map_mono hW2⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
