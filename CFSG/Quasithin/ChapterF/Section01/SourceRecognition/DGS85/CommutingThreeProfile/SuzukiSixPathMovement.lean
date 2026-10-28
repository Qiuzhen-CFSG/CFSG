module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiNinePathOdd
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiNinePathOdd
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiSpanFixedIndex
public import Theory.GroupTheory.Commutator.IntersectionGeneration

/-!
# The moving intersection on the nonbinary source six-path

For the path a--x--m--y--z--w--c of DGS (12.8), let Y = V_y and
D = Y intersect Q_x intersect Q_w. The two remote spans V_x and V_w,
together with Q_y, generate the actual Suzuki star. Their mutual
normalization with Y and the already proved equality [Y,star] = Y
show that (V_x intersect Y)(V_w intersect Y) = Y.

The existing first and second indices identify Y intersect Q_x
intersect Q_a with V_x intersect Y, of order q^3. The first index at w
also gives |D| at least q^3. If D lay in Q_a, these two subgroups would
coincide, putting both generating intersections in Q_w. This contradicts
the nontrivial image of Y at w. Thus D escapes Q_a.

The final consumer constructs the literal nonbacktracking six-path,
places D in its pointwise stabilizer and obtains a neighbor of a moved
by D. All subgroup images retain the original completion inclusion.
The first/second indices, generation and cardinal bounds are proved
inputs, not extra hypotheses. The retained quotient markings, critical
placements, natural-center data and nonzero branch commutator are the
genuine earlier source inputs used by the preceding Chapter 12 chain.

This is the first endpoint-movement step of (12.8). Full endpoint
transitivity, the other six-path orientation needed to prove s >= 7,
full kernel equalities, Suzuki selection, binary alternatives and the
remaining (12.6)--(12.9)/(13.1) assembly and premise discharge are retained.
Implementation imports reuse the checked private neighbor exchange and
incoming-index arguments without changing their public boundaries.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.8), printed pp.185--186, using (12.3)(a) and (12.6).
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
open BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The two overlap subgroups generate the middle span, and the threefold intersection escapes the endpoint core. -/
theorem source_suzuki_six_path_intersection_escape
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
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i))
    (hnat : Noncommuting.HasNaturalCenter (star L S i)
      (Z (reducedFamily L S) (base (reducedFamily L S) i))
      (Q (reducedFamily L S) (base (reducedFamily L S) i)))
    {c w z : Vertex (reducedFamily L S)}
    (hyz : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) (!i)) z)
    (hwz : (graph (reducedFamily L S)).Adj w z)
    (hwc : (graph (reducedFamily L S)).Adj w c)
    (hzn : z ≠ base (reducedFamily L S) i)
    (hcc : IsCriticalPair (reducedFamily L S) c (base (reducedFamily L S) (!i)))
    (Rz : Sylow 2 (star L S (!i)))
    (hRz : (Rz : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) z ⊔ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hbranch : ⁅V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i)),
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥) :
    let F := reducedFamily L S
    let y := base F (!i)
    let D := (V F y 1 ⊓ Q F x) ⊓ Q F w
    (V F x 1 ⊓ V F y 1) ⊔ (V F w 1 ⊓ V F y 1) = V F y 1 ∧
      ¬ D ≤ Q F a ∧
      ((V F x 1).map (G₀ L S).subtype ⊓ (V F y 1).map (G₀ L S).subtype) ⊔
        ((V F w 1).map (G₀ L S).subtype ⊓ (V F y 1).map (G₀ L S).subtype) =
          (V F y 1).map (G₀ L S).subtype ∧
      ¬ D.map (G₀ L S).subtype ≤ (Q F a).map (G₀ L S).subtype := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let A := star L S (!i)
  let X := V F x 1
  let Y := V F y 1
  let W := V F w 1
  let H := X ⊓ Y
  let D := (Y ⊓ Q F x) ⊓ Q F w
  let q := 2^(2*n+1)
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  have hQU := fun v => (source_Z_Q_U (reduced_triple h) v).2
  have hadj : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hYQ := V_le_Q F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb y
  let : Finite Y := Finite.of_injective
    (inclusion (hYQ.trans (Q_le_stabilizer F y))) (inclusion_injective _)
  let : Finite H := Finite.of_injective (inclusion (show H ≤ Y from inf_le_right))
    (inclusion_injective _)
  have hXm : X ≤ Q F m := V_le_neighbor_Q F (reduced_triple h).generate hZ
    (reduced_kernel_sylow h) hb hxadj.symm
  have hYm : Y ≤ Q F m := V_le_neighbor_Q F (reduced_triple h).generate hZ
    (reduced_kernel_sylow h) hb hadj.symm
  have hWz : W ≤ Q F z := V_le_neighbor_Q F (reduced_triple h).generate hZ
    (reduced_kernel_sylow h) hb hwz
  have hYz : Y ≤ Q F z := V_le_neighbor_Q F (reduced_triple h).generate hZ
    (reduced_kernel_sylow h) hb hyz
  have hXi : (Q F y).relIndex X = q := by
    simpa only [inf_relIndex_left] using (source_suzuki_first_index h (!i) hb hc hxa
      hxadj.symm hadj.symm hn eSuz (by cases i <;> exact e) Ry hRy).1
  have hXesc : ¬ X ≤ Q F y := by
    intro he
    have hh := relIndex_eq_one.mpr he
    rw [hXi] at hh
    have hq : 1 < q := Nat.one_lt_pow (by omega) (by decide)
    omega
  have hgen : (X ⊔ W) ⊔ Q F y = A :=
    (source_suzuki_span_escape_generation h (!i) hb hyz hwz hwc
      (by simpa only [Bool.not_not] using hzn) hcc hn eSuz (by cases i <;> exact e)
      Ry Rz (by simpa only [Bool.not_not] using hRy) hRz X
      (by simpa only [Bool.not_not] using hXm) hXesc).1
  have hXY : X ≤ normalizer (Y : Set (G₀ L S)) :=
    (((hXm.trans (hQU m)).trans (ballKernel_one_le_edge F hadj)).trans inf_le_right).trans
      (stabilizer_normalizes_V F y 1)
  have hYX : Y ≤ normalizer (X : Set (G₀ L S)) :=
    (((hYm.trans (hQU m)).trans (ballKernel_one_le_edge F hxadj)).trans inf_le_right).trans
      (stabilizer_normalizes_V F x 1)
  have hWY : W ≤ normalizer (Y : Set (G₀ L S)) :=
    (((hWz.trans (hQU z)).trans (ballKernel_one_le_edge F hyz.symm)).trans inf_le_right).trans
      (stabilizer_normalizes_V F y 1)
  have hYW : Y ≤ normalizer (W : Set (G₀ L S)) :=
    (((hYz.trans (hQU z)).trans (ballKernel_one_le_edge F hwz.symm)).trans inf_le_right).trans
      (stabilizer_normalizes_V F w 1)
  have hfull := (source_suzuki_product_and_intersection_commutator
    h i hb hxadj hne T R hT hR e hz hcard hcardy hzx hzy hcommx hcommy
    hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin).2.2.2.1
  have hCY : Z F y ≤ H := le_inf (hzy.trans (Z_neighbor_le_V F hxadj.symm)) (Z_le_V F y 1)
  have hprod : H ⊔ (W ⊓ Y) = Y := sup_intersections_eq_of_generated_movement
    A Y X W (Q F y) hgen hfull hXY hYX hWY hYW
    (hcommy.le.trans (hCY.trans le_sup_left))
  have hHcard : Nat.card H = q^3 :=
    (source_suzuki_intersection_card h i hb hxadj hne T R hT hR e hz hcard hcardy
      hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat).1
  have hYcard : Nat.card Y = q^5 :=
    (source_suzuki_center_layer_of_intersection h i hb hxadj hne T R hT hR e hz
      hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy
      hc hxa hmin hnat).2.1
  have hYix : (Q F x).relIndex Y = q :=
    (source_suzuki_reverse_first_index h (!i) hb hc hxa hxadj.symm hadj.symm hn eSuz
      (by cases i <;> exact e) Ry hRy).1
  have hYiw : (Q F w).relIndex Y = q :=
    (source_suzuki_reverse_first_index h (!i) hb hcc hwc hwz hyz hn eSuz
      (by cases i <;> exact e) Rz hRz).1
  obtain ⟨g,hgm,hgx,hgy⟩ := linear_neighbor_swap h i e hxadj hadj hne
  have hgm' : g • m = m := hgm
  have hga : (graph F).Adj y (g • a) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr hxa
    change (graph F).Adj (g • x) (g • a) at hh
    rwa [hgx] at hh
  have han : a ≠ m := by
    intro he
    have hh := (Z_neighbor_le_V F hadj.symm).trans hYQ
    exact hc.2 (he ▸ hh.trans (hQU y))
  have hgan : g • a ≠ m := fun he => han ((MulAction.injective g) (he.trans hgm'.symm))
  have hi := incoming_second_index h (!i) hb hn eSuz (by cases i <;> exact e) hfield Ry
    (by simpa only [Bool.not_not] using hRy) (by cases i <;> exact T)
    (by cases i <;> exact hT) (by simpa only [Bool.not_not] using hxadj.symm) hga
    (by simpa only [Bool.not_not] using hgan) hbranch
  have hia : (Q F a).relIndex (Y ⊓ Q F x) = q := by
    have he := relIndex_map_map_of_injective (Q F a) (Y ⊓ Q F x)
      (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
    dsimp only [Y] at he
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,←V_translate F,←Q_translate F,
      ←Q_translate F,hgx,hgy] at he
    exact he.symm.trans (hi.trans hfield)
  let B := Y ⊓ Q F x
  let J := B ⊓ Q F a
  let : Finite B := Finite.of_injective (inclusion (show B ≤ Y from inf_le_left)) (inclusion_injective _)
  let : Finite J := Finite.of_injective (inclusion (show J ≤ B from inf_le_left)) (inclusion_injective _)
  let : Finite D := Finite.of_injective (inclusion (show D ≤ Y from inf_le_left.trans inf_le_left)) (inclusion_injective _)
  have hHJ : H ≤ J := le_inf
    (le_inf inf_le_right (inf_le_left.trans (V_le_Q F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb x)))
    (inf_le_left.trans (V_le_neighbor_Q F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb hxa))
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hBcard : Nat.card B = q^4 := by
    have he := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) B Y bot_le inf_le_left
    rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left,hYix,hYcard] at he
    exact Nat.eq_of_mul_eq_mul_right hqpos (he.trans (by ring))
  have hJcard : Nat.card J = q^3 := by
    have he := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) J B bot_le inf_le_left
    rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left,hia,hBcard] at he
    exact Nat.eq_of_mul_eq_mul_right hqpos (he.trans (by ring))
  have hHJ_eq : H = J := eq_of_le_of_card_ge hHJ (by rw [hJcard,hHcard])
  have hDlow : q^3 ≤ Nat.card D := by
    have hiD : D.relIndex B ≤ q := by
      rw [inf_relIndex_left]
      exact (relIndex_le_of_le_right (show B ≤ Y from inf_le_left) index_ne_zero_of_finite).trans_eq hYiw
    have he := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) D B bot_le inf_le_left
    rw [relIndex_bot_left,relIndex_bot_left,hBcard] at he
    have hm := Nat.mul_le_mul_left (Nat.card D) hiD
    rw [he,show q^4 = q^3*q by ring] at hm
    exact (mul_le_mul_iff_left₀ hqpos).mp (by simpa only [mul_comm] using hm)
  have hesc : ¬ D ≤ Q F a := by
    intro hD
    have hDJ : D ≤ J := le_inf inf_le_left hD
    have hDH : D = H := (eq_of_le_of_card_ge hDJ (by rw [hJcard]; exact hDlow)).trans hHJ_eq.symm
    have hHQ : H ≤ Q F w := hDH ▸ (show D ≤ Q F w from inf_le_right)
    have hYw : Y ≤ Q F w := by
      rw [←hprod]
      exact sup_le hHQ (inf_le_left.trans (V_le_Q F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb w))
    have hh := relIndex_eq_one.mpr hYw
    rw [hYiw] at hh
    have hq : 1 < q := Nat.one_lt_pow (by omega) (by decide)
    omega
  refine ⟨hprod,hesc,?_,?_⟩
  · have he := congrArg (Subgroup.map (G₀ L S).subtype) hprod
    rwa [Subgroup.map_sup,Subgroup.map_inf _ _ _ (G₀ L S).subtype_injective,
      Subgroup.map_inf _ _ _ (G₀ L S).subtype_injective] at he
  · intro hle
    apply hesc
    intro u hu
    obtain ⟨v,hv,he⟩ := hle (mem_map_of_mem (G₀ L S).subtype hu)
    exact (G₀ L S).subtype_injective he ▸ hv


/-- The original six-path fixer contains a two-subgroup moving an additional endpoint neighbor. -/
theorem source_suzuki_six_path_movement
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
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i))
    (hnat : Noncommuting.HasNaturalCenter (star L S i)
      (Z (reducedFamily L S) (base (reducedFamily L S) i))
      (Q (reducedFamily L S) (base (reducedFamily L S) i)))
    {c w z : Vertex (reducedFamily L S)}
    (hyz : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) (!i)) z)
    (hwz : (graph (reducedFamily L S)).Adj w z)
    (hwc : (graph (reducedFamily L S)).Adj w c)
    (hzn : z ≠ base (reducedFamily L S) i)
    (hcc : IsCriticalPair (reducedFamily L S) c (base (reducedFamily L S) (!i)))
    (Rz : Sylow 2 (star L S (!i)))
    (hRz : (Rz : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) z ⊔ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hbranch : ⁅V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i)),
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥) :
    let F := reducedFamily L S
    let m := base F i
    let y := base F (!i)
    let D := (V F y 1 ⊓ Q F x) ⊓ Q F w
    ∃ p : SimpleGraph.BasedWalk (graph F) 6 a,
      p.vertices = [a,x,m,y,z,w,c] ∧ p.Nonbacktracking ∧
      D ≤ pathStabilizer F p ∧
      D.map (G₀ L S).subtype ≤ (pathStabilizer F p).map (G₀ L S).subtype ∧
      ∃ t ∈ D, ∃ v, (graph F).Adj a v ∧ v ≠ x ∧ t • v ≠ v := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let D := (V F y 1 ⊓ Q F x) ⊓ Q F w
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  have hQU := fun v => (source_Z_Q_U (reduced_triple h) v).2
  have hadj : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hYQ := V_le_Q F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb y
  have hYDy : D ≤ Q F y := (inf_le_left.trans inf_le_left).trans hYQ
  have hDx : D ≤ Q F x := inf_le_left.trans inf_le_right
  have hDw : D ≤ Q F w := inf_le_right
  have hfix (u v : Vertex F) (hu : D ≤ Q F u) (huv : (graph F).Adj u v) :
      D ≤ stabilizer F v := ((hu.trans (hQU u)).trans (ballKernel_one_le_edge F huv)).trans inf_le_right
  have hDa : D ≤ stabilizer F a := hfix x a hDx hxa
  have hDy : D ≤ stabilizer F y := hYDy.trans (Q_le_stabilizer F y)
  have hDz : D ≤ stabilizer F z := hfix y z hYDy hyz
  have hDm : D ≤ stabilizer F m := hfix x m hDx hxadj.symm
  have hDc : D ≤ stabilizer F c := hfix w c hDw hwc
  have hDxx : D ≤ stabilizer F x := hDx.trans (Q_le_stabilizer F x)
  have hDww : D ≤ stabilizer F w := hDw.trans (Q_le_stabilizer F w)
  let p : SimpleGraph.BasedWalk (graph F) 6 a :=
    ⟨⟨x,hxa.symm⟩,⟨⟨m,hxadj.symm⟩,⟨⟨y,hadj⟩,⟨⟨z,hyz⟩,⟨⟨w,hwz.symm⟩,⟨⟨c,hwc⟩,PUnit.unit⟩⟩⟩⟩⟩⟩
  have hp : D ≤ pathStabilizer F p := by
    intro t ht v hv
    change v ∈ [a,x,m,y,z,w,c] at hv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hDa ht
    · exact hDxx ht
    · exact hDm ht
    · exact hDy ht
    · exact hDz ht
    · exact hDww ht
    · exact hDc ht
  have han : a ≠ m := by
    intro he
    have hh := (Z_neighbor_le_V F hadj.symm).trans hYQ
    exact hc.2 (he ▸ hh.trans (hQU y))
  have hwy : w ≠ y := by
    intro he
    have hh := (Z_neighbor_le_V F hwc).trans
      (V_le_Q F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb w)
    rw [he] at hh
    exact hcc.2 (hh.trans (hQU y))
  have hcz : c ≠ z := by
    intro he
    have hh := (Z_neighbor_le_V F hyz).trans hYQ
    exact hcc.2 (he ▸ hh.trans (hQU y))
  have hnb : p.Nonbacktracking := ⟨han.symm,hne.symm,hzn,hwy,hcz,trivial⟩
  have hesc := (source_suzuki_six_path_intersection_escape h i hb hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat
    hyz hwz hwc hzn hcc Rz hRz hbranch).2.1
  have hmove : ∃ t ∈ D, ∃ v, (graph F).Adj a v ∧ t • v ≠ v := by
    by_contra! hh
    apply hesc
    apply CommutingTrivial.two_subgroup_le_Q F a (reduced_kernel_sylow h a)
      ((isPGroup_pCoreIn 2 (stabilizer F x)).to_le hDx)
    intro t ht v hv
    rcases (mem_ball_one F a v).mp hv with hv | rfl
    · exact hh t ht v hv
    · exact hDa ht
  obtain ⟨t,ht,v,hav,htv⟩ := hmove
  exact ⟨p,rfl,hnb,hp,map_mono hp,t,ht,v,hav,
    (fun he => htv (he ▸ hDxx ht)),htv⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
