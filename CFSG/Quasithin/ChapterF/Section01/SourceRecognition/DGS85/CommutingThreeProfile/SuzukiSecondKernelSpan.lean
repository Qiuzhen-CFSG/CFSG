module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SecondKernelSpan
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiIntersectionOrder
public import Theory.GroupTheory.NormalizedSupCard
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiSpanFixedIndex

/-!
# The source elementary span and its concrete order bounds

Apply the second-kernel span construction to the nonbinary Suzuki branch.
The actual first index and the order q^5 of either neighboring span give
order q^4 for each span--core intersection. A linear neighbor swap places
both intersections in the same normal span W. Their intersection is the
already computed H of order q^3, so their elementary product has order
q^5 and lies in W, hence in the full second kernel. Both intersections
with W and the original completion inclusion are retained.

The near reciprocal commutator is the (12.1)(g) input on the displayed
neighbor pair; the other retained commutator/index inputs have their
original earlier-source roles. This proves the elementary construction
and a lower bound needed by (12.9)(c3,c4), not equality with the full
second kernel or the final classification alternatives.
Source: DGS85, Groups and Graphs, (12.1), (12.6), (12.9), pp.178,183,188.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
open BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The literal source span contains the elementary order-q^5 product in the full second kernel. -/
theorem source_suzuki_second_kernel_span_order
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
    IsElementaryAbelian 2 W ∧ W ≤ ballKernel F m 2 ∧
    W ⊓ Y = A ∧ W ⊓ X = B ∧
    Nat.card A = (2^(2*n+1))^4 ∧ Nat.card B = (2^(2*n+1))^4 ∧
    A ⊓ B = X ⊓ Y ∧ Nat.card (A ⊔ B : Subgroup (G₀ L S)) = (2^(2*n+1))^5 ∧
    A ⊔ B ≤ W ∧ (2^(2*n+1))^5 ≤ Nat.card W ∧
    (2^(2*n+1))^5 ≤ Nat.card (ballKernel F m 2) ∧
    (A ⊔ B).map (G₀ L S).subtype ≤ (ballKernel F m 2).map (G₀ L S).subtype ∧
    Nat.card ((A ⊔ B).map (G₀ L S).subtype) = (2^(2*n+1))^5 := by
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
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  have hadj : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hXQ : X ≤ Q F x :=
    V_le_Q F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb x
  have hYQ : Y ≤ Q F y :=
    V_le_Q F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb y
  have hspan := source_linear_second_kernel_span h i hb hxadj hne T hT e hcommy.le hnear
  obtain ⟨hWel,hW2,hWV,hnW,hWY,hHW,hWz,hmap,hmaple⟩ := hspan
  let : IsElementaryAbelian 2 W := hWel
  let : Finite W := Finite.of_injective
    (inclusion (hW2.trans (ballKernel_le_stabilizer F m 2))) (inclusion_injective _)
  let : Finite (ballKernel F m 2) := Finite.of_injective
    (inclusion (ballKernel_le_stabilizer F m 2)) (inclusion_injective _)
  have hYcard := (source_suzuki_center_layer_of_intersection
    h i hb hxadj hne T R hT hR e hz hcard hcardy hzx hzy hcommx hcommy
    hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat).2.1
  have hHcard := (source_suzuki_intersection_card
    h i hb hxadj hne T R hT hR e hz hcard hcardy hzx hzy hcommx hcommy
    hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat).1
  obtain ⟨g,hgm,hgx,hgy⟩ := linear_neighbor_swap h i e hxadj hadj hne
  have hXY : X.map (MulAut.conj g).toMonoidHom = Y := by
    change (V F x 1).map _ = _
    rw [←V_translate F,hgx]
  have hAB : A.map (MulAut.conj g).toMonoidHom = B := by
    change (V F y 1 ⊓ Q F x).map _ = _
    rw [map_inf _ _ _ (MulAut.conj g).injective, ←V_translate F,←Q_translate F,hgy,hgx]
  have hXcard : Nat.card X = q^5 := by
    have hh := card_map_of_injective (K := X) (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
    rw [hXY] at hh
    exact hh.symm.trans hYcard
  have hBindex : B.relIndex X = q :=
    (source_suzuki_first_index h (!i) hb hc hxa hxadj.symm hadj.symm hn
      eSuz (by cases i <;> exact e) Ry hRy).1
  have hBcard : Nat.card B = q^4 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) B X bot_le inf_le_left
    rw [relIndex_bot_left,relIndex_bot_left,hBindex,hXcard] at hh
    have hpow : q^5 = q^4*q := by ring
    rw [hpow] at hh
    exact Nat.eq_of_mul_eq_mul_right (by dsimp [q]; positivity) hh
  have hAcard : Nat.card A = q^4 := by
    have hh := card_map_of_injective (K := A) (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
    rw [hAB] at hh
    exact hh.symm.trans hBcard
  have hAW : A ≤ W := le_conjugateSpanBy A (stabilizer F m)
  have hBW : B ≤ W := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hAW
    rw [hAB] at hh
    exact hh.trans_eq (mem_normalizer_iff_map_conj_eq.mp (hnW hgm))
  have hWX : W ⊓ X = B := le_antisymm
    (le_inf inf_le_right (inf_le_left.trans (hWz y hadj))) (le_inf hBW inf_le_left)
  have hABH : A ⊓ B = X ⊓ Y := by
    apply le_antisymm
    · exact le_inf (inf_le_right.trans inf_le_left) (inf_le_left.trans inf_le_left)
    · intro z hz
      exact ⟨⟨hz.2,hXQ hz.1⟩,⟨hz.1,hYQ hz.2⟩⟩
  have hJW : A ⊔ B ≤ W := sup_le hAW hBW
  have hJcard : Nat.card (A ⊔ B : Subgroup (G₀ L S)) = q^5 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes
      (A.subgroupOf W) (B.subgroupOf W) (by rw [normalizer_eq_top]; exact le_top)
    have hi : A.subgroupOf W ⊓ B.subgroupOf W = (A ⊓ B).subgroupOf W := rfl
    rw [hi, ←subgroupOf_sup hAW hBW] at hh
    rw [Nat.card_congr (subgroupOfEquivOfLe hAW).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hBW).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans hAW : A ⊓ B ≤ W)).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hJW).toEquiv,
      hAcard,hBcard,hABH,hHcard] at hh
    change q^4*q^4 = q^3 * Nat.card (A ⊔ B : Subgroup (G₀ L S)) at hh
    have hpow : q^4*q^4 = q^3*q^5 := by ring
    rw [hpow] at hh
    exact (Nat.eq_of_mul_eq_mul_left (by dsimp [q]; positivity) hh).symm
  have hWcard : q^5 ≤ Nat.card W := hJcard ▸
    Nat.card_le_card_of_injective (inclusion hJW) (inclusion_injective _)
  have hNcard : q^5 ≤ Nat.card (ballKernel F m 2) := hWcard.trans
    (Nat.card_le_card_of_injective (inclusion hW2) (inclusion_injective _))
  exact ⟨hWel,hW2,hWY,hWX,hAcard,hBcard,hABH,hJcard,hJW,hWcard,hNcard,
    map_mono (hJW.trans hW2),(card_map_of_injective (G₀ L S).subtype_injective).trans hJcard⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
