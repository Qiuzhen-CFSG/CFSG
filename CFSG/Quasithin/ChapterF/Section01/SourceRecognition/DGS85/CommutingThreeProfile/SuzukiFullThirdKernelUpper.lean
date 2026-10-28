module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiFullCoreUpper
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiThirdLayer

/-!
# An upper bound for the full linear third kernel

Write H = V_x ∩ V_y for the geometric intersection at the linear vertex m.
The full third kernel N at m lies in the full second kernel K at y.
Since |V_y| = q⁵ and |K| ≤ q⁶, the equality V_y ∩ N = H gives
[N : H] ≤ q. The already proved |H| = q³ then bounds |N| by q⁴.
Moreover K centralizes V_y, so H is central in N. All bounds retain the
literal full ball kernels and the original completion inclusion.

This bounds the possible extra third-kernel layer; it does not identify
N with H. Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs
(1985), (12.6)--(12.9), printed pp.183--188. The earlier source premises
and nonbinary Suzuki marking remain explicit.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
open BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The geometric order-q³ intersection is central of index at most q in
the full linear third kernel, whose order is consequently at most q⁴. -/
theorem source_suzuki_full_linear_third_kernel_upper
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb3 : b (reducedFamily L S) = 3)
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
    (hbranch : ⁅V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i)),
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥) :
    let F := reducedFamily L S
    let m := base F i
    let y := base F (!i)
    let H := V F x 1 ⊓ V F y 1
    let N := ballKernel F m 3
    H ≤ N ∧ H.subgroupOf N ≤ center N ∧
    H.relIndex N ≤ 2^(2*n+1) ∧
    Nat.card (N ⧸ H.subgroupOf N) ≤ 2^(2*n+1) ∧
    Nat.card N ≤ (2^(2*n+1))^4 ∧
    Nat.card (N.map (G₀ L S).subtype) ≤ (2^(2*n+1))^4 ∧
    (H.map (G₀ L S).subtype).relIndex (N.map (G₀ L S).subtype) ≤ 2^(2*n+1) := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let Y := V F y 1
  let H := V F x 1 ⊓ Y
  let N := ballKernel F m 3
  let K := ballKernel F y 2
  let q := 2^(2*n+1)
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hb : 2 < b F := by change 2 < b (reducedFamily L S); omega
  have hadj : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hthird := source_suzuki_third_kernel_layer h i hb hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat
  have hHN : H ≤ N := hthird.2.2.1
  have hYN : Y ⊓ N = H := hthird.2.2.2.1
  have hHcard : Nat.card H = q^3 := hthird.2.2.2.2.2.2.2.2.1
  have hprod := source_suzuki_product_and_intersection_commutator h i hb hxadj hne
    T R hT hR e hz hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin
  have hfull := hprod.2.2.2.1
  have hKcard := (source_suzuki_full_second_kernel_upper h i hb3 T hT e hz hcard hcardy
    hzy hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hmin hnat hxadj hne hbranch hfull).1
  have hYcard : Nat.card Y = q^5 :=
    (source_suzuki_center_layer_of_intersection h i hb hxadj hne T R hT hR e hz hcard hcardy
      hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat).2.1
  have hYK : Y ≤ K := V_le_ballKernel F (reduced_triple h).generate y
    (by change 3 ≤ b (reducedFamily L S); omega)
  have hNK : N ≤ K := ballKernel_succ_le F hadj 2
  let : Finite K := Finite.of_injective (inclusion (ballKernel_le_stabilizer F y 2))
    (inclusion_injective _)
  let : Finite N := Finite.of_injective (inclusion hNK) (inclusion_injective _)
  have hYindex : Y.relIndex K ≤ q := by
    have hm := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) Y K bot_le hYK
    rw [relIndex_bot_left,relIndex_bot_left,hYcard] at hm
    apply Nat.le_of_mul_le_mul_left (c := q^5) _ (by positivity)
    calc
      q^5 * Y.relIndex K = Nat.card K := hm
      _ ≤ q^6 := hKcard
      _ = q^5 * q := by ring
  have hindex : H.relIndex N ≤ q := by
    rw [←hYN,inf_relIndex_right]
    exact (relIndex_le_of_le_right hNK (by exact index_ne_zero_of_finite)).trans hYindex
  have hNcard : Nat.card N ≤ q^4 := by
    have hm := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) H N bot_le hHN
    rw [relIndex_bot_left,relIndex_bot_left,hHcard] at hm
    calc
      Nat.card N = q^3 * H.relIndex N := hm.symm
      _ ≤ q^3 * q := Nat.mul_le_mul_left _ hindex
      _ = q^4 := by ring
  have hk : 4 ≤ Nat.card k := by
    rw [hfield]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : 2 ≤ 2*n+1)
  have hQyA : Q F y ≤ star L S i := (le_sup_left.trans hT.ge).trans (map_subtype_le _)
  have hcent : Q F y ⊓ centralizer (Y : Set (G₀ L S)) = K :=
    source_suzuki_second_kernel_centralizer h (!i) eSuz
      (by cases i <;> exact e) hk (by cases i <;> exact hQyA) (by cases i <;> exact hnat)
  have hNY : N ≤ centralizer (Y : Set (G₀ L S)) := hNK.trans (hcent.ge.trans inf_le_right)
  have hcentral : H.subgroupOf N ≤ center N := by
    intro z hz
    apply mem_center_iff.mpr
    intro t
    apply Subtype.ext
    have hzY : (z : G₀ L S) ∈ Y := hz.2
    exact ((le_centralizer_iff.mp hNY) hzY) t t.property
  refine ⟨hHN,hcentral,hindex,?_,hNcard,?_,?_⟩
  · change (H.subgroupOf N).index ≤ q
    exact hindex
  · rw [card_map_of_injective (G₀ L S).subtype_injective]
    exact hNcard
  · rw [relIndex_map_map_of_injective _ _ (G₀ L S).subtype_injective]
    exact hindex

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
