module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiSpanCentralizer
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiSecondKernelSpan
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiIntersectionKernels
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiSpanFixedIndex

/-!
# Exact centralizers of the elementary second-kernel span

For the linear middle vertex m and its two Suzuki neighbors x,y, let
W be the full stabilizer span of V_y intersect Q_x. The previously proved
elementary structure of W puts each span--core intersection in the
corresponding span centralizer. Suzuki Borel transitivity leaves only the
alternative that all of V_x centralizes W. In that case natural-center
faithfulness puts W in the second kernel at x. Its order-q^4 seed would
then lie in V_y intersect G_x^(2), whose proved order is q^3. This excludes
the alternative. A middle-stabilizer swap gives the other orientation.

Thus C_(V_x)(W) = V_x intersect Q_y and C_(V_y)(W) = V_y intersect Q_x,
with both indices exactly q. The same geometric contradiction proves
W is not contained in the full third kernel at m. The two centralizer
equalities retain their literal images in the original completion.

This proves the centralizer calculation preceding step (2) in DGS (12.9),
printed p.188, using (12.3)(a) and (12.6). The earlier markings, common
Sylows, natural center and commutators remain explicit. No full-kernel
equality, order upper bound, path bound or classification alternative is
inferred from these centralizer identities.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
open BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Both source span centralizers have exact index q; the elementary span escapes the third kernel. -/
theorem source_suzuki_second_kernel_span_centralizers
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
    (hnear : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) x,
      V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥) :
    let F := reducedFamily L S
    let m := base F i
    let y := base F (!i)
    let X := V F x 1
    let Y := V F y 1
    let A := Y ⊓ Q F x
    let B := X ⊓ Q F y
    let W := conjugateSpanBy A (stabilizer F m)
    X ⊓ centralizer (W : Set (G₀ L S)) = B ∧
    Y ⊓ centralizer (W : Set (G₀ L S)) = A ∧
    (centralizer (W : Set (G₀ L S))).relIndex X = 2^(2*n+1) ∧
    (centralizer (W : Set (G₀ L S))).relIndex Y = 2^(2*n+1) ∧
    ¬ W ≤ ballKernel F m 3 ∧
    X.map (G₀ L S).subtype ⊓ centralizer (W.map (G₀ L S).subtype : Set G) =
      B.map (G₀ L S).subtype ∧
    Y.map (G₀ L S).subtype ⊓ centralizer (W.map (G₀ L S).subtype : Set G) =
      A.map (G₀ L S).subtype := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let X := V F x 1
  let Y := V F y 1
  let A := Y ⊓ Q F x
  let B := X ⊓ Q F y
  let W := conjugateSpanBy A (stabilizer F m)
  let q := 2^(2*n+1)
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hy : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨hWel,hW2,_,hnW,hWY,_,hWz,_,_⟩ :=
    source_linear_second_kernel_span h i hb hxadj hne T hT e hcommy.le hnear
  let : IsElementaryAbelian 2 W := hWel
  have horders := source_suzuki_second_kernel_span_order h i hb hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hnear
  have hAcard : Nat.card A = q^4 := horders.2.2.2.2.1
  have hBW : B ≤ W := le_sup_right.trans horders.2.2.2.2.2.2.2.2.1
  have hAW : A ≤ W := le_conjugateSpanBy A (stabilizer F m)
  have hHcard := (source_suzuki_intersection_card h i hb hxadj hne T R hT hR e hz hcard
    hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat).1
  have hYN := (source_suzuki_intersection_kernels h i hb hxadj hne T R hT hR e hz hcard
    hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat).2.2.1
  have hnot : ¬ A ≤ X ⊓ Y := by
    intro hh
    let : Finite (X ⊓ Y : Subgroup (G₀ L S)) := Finite.of_injective
      (inclusion ((inf_le_left.trans (V_le_Q F (reduced_triple h).generate
        (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb x)).trans
        (Q_le_stabilizer F x))) (inclusion_injective _)
    have hh' := Nat.card_le_card_of_injective (inclusion hh) (inclusion_injective _)
    rw [hAcard,hHcard] at hh'
    exact (not_le_of_gt (Nat.pow_lt_pow_right (by dsimp [q]; exact Nat.one_lt_pow (by omega) (by decide))
      (by decide : 3 < 4))) hh'
  have hnotcentral : ¬ X ≤ centralizer (W : Set (G₀ L S)) := by
    intro hh
    have hWX : W ≤ Q F x ⊓ centralizer (X : Set (G₀ L S)) :=
      le_inf (hWz x hxadj) (le_centralizer_iff.mp hh)
    have hQx : Q F x ≤ star L S i := (le_sup_left.trans hR.ge).trans (map_subtype_le _)
    have hWN : W ≤ ballKernel F x 2 := hWX.trans
      ((source_neighbor_core_span_centralizer h i hxadj.symm hQx hnat).le.trans inf_le_right)
    exact hnot ((le_inf inf_le_left (hAW.trans hWN)).trans hYN.le)
  have hCX : X ⊓ centralizer (W : Set (G₀ L S)) = B := by
    apply (source_suzuki_span_centralizer_dichotomy h (!i) hb hxadj.symm hy.symm hn eSuz
      (by cases i <;> exact e) Ry hRy W hnW
      (hBW.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance))).resolve_right hnotcentral
  obtain ⟨g,hgm,hgx,hgy⟩ := linear_neighbor_swap h i e hxadj hy hne
  have hWg : W.map (MulAut.conj g).toMonoidHom = W :=
    mem_normalizer_iff_map_conj_eq.mp (hnW hgm)
  have hCY : Y ⊓ centralizer (W : Set (G₀ L S)) = A := by
    have hh := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hCX
    change (V F x 1 ⊓ centralizer (W : Set (G₀ L S))).map _ = (V F x 1 ⊓ Q F y).map _ at hh
    rw [←map_inf_centralizer_of_injective _ (MulAut.conj g).injective,
      hWg,←V_translate F,hgx,map_inf _ _ _ (MulAut.conj g).injective,
      ←V_translate F,←Q_translate F,hgx,hgy] at hh
    exact hh
  have hBindex : B.relIndex X = q :=
    (source_suzuki_first_index h (!i) hb hc hxa hxadj.symm hy.symm hn eSuz
      (by cases i <;> exact e) Ry hRy).1
  have hAindex : A.relIndex Y = q := by
    have hh := relIndex_map_map_of_injective B X (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective
    change ((X ⊓ Q F y).map (MulAut.conj g).toMonoidHom).relIndex
      (X.map (MulAut.conj g).toMonoidHom) = B.relIndex X at hh
    change ((V F x 1 ⊓ Q F y).map _).relIndex ((V F x 1).map _) = _ at hh
    rw [map_inf _ _ _ (MulAut.conj g).injective,←V_translate F,←Q_translate F,hgx,hgy] at hh
    exact hh.trans hBindex
  have hnot3 : ¬ W ≤ ballKernel F m 3 := by
    intro hh
    have hN : W ≤ ballKernel F x 2 := hh.trans (ballKernel_succ_le F hxadj 2)
    exact hnot ((le_inf inf_le_left (hAW.trans hN)).trans hYN.le)
  refine ⟨hCX,hCY,?_,?_,hnot3,?_,?_⟩
  · rw [←inf_relIndex_left,hCX]
    exact hBindex
  · rw [←inf_relIndex_left,hCY]
    exact hAindex
  · rw [map_inf_centralizer_of_injective _ (G₀ L S).subtype_injective,hCX]
  · rw [map_inf_centralizer_of_injective _ (G₀ L S).subtype_injective,hCY]

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
