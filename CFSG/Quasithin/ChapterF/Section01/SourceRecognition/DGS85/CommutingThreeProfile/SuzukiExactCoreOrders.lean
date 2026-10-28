module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiCentralizerIrreducible

/-!
# Exact core orders in the nonbinary commuting branch

The now irreducible literal C/W has order between q³ and q⁴.
Odd-degree binary SL₂ orbit dimensions force its order to be q⁴.
Together with |W| = q⁵ and |Q_m/C| = q² this gives |C| = q⁹
and |Q_m| = q¹¹. The two marked common-Sylow indices are q and q²,
so the opposite core has order q¹⁰. Its existing irreducible quotient
over the full second kernel has order q⁴; that full kernel therefore
has order q⁶.

All orders refer to the actual geometric subgroups, and the original
completion inclusions retain the same orders. No upper bound or source
selection is assumed beyond the explicitly retained earlier hypotheses.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.9)(c), printed pp.186--190.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
/-- Exact centralizer, endpoint-core and Suzuki second-kernel orders, including the original completion. -/
theorem source_suzuki_exact_core_orders
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
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥)
    (hnear : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) x,
      V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥) :
    let F := reducedFamily L S
    let m := base F i
    let y := base F (!i)
    let C := Q F m ⊓ centralizer (ballKernel F m 3 : Set (G₀ L S))
    let W := ballKernel F m 2
    W.relIndex C = Nat.card k ^ 4 ∧
    Nat.card C = Nat.card k ^ 9 ∧
    Nat.card (Q F m) = Nat.card k ^ 11 ∧
    Nat.card (Q F y) = Nat.card k ^ 10 ∧
    Nat.card (ballKernel F y 2) = Nat.card k ^ 6 ∧
    Nat.card (C.map (G₀ L S).subtype) = Nat.card k ^ 9 ∧
    Nat.card ((Q F m).map (G₀ L S).subtype) = Nat.card k ^ 11 ∧
    Nat.card ((Q F y).map (G₀ L S).subtype) = Nat.card k ^ 10 ∧
    Nat.card ((ballKernel F y 2).map (G₀ L S).subtype) = Nat.card k ^ 6 := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let Qm := Q F m
  let Qy := Q F y
  let C := Qm ⊓ centralizer (ballKernel F m 3 : Set (G₀ L S))
  let W := conjugateSpanBy (V F y 1 ⊓ Q F x) (stabilizer F m)
  let K := ballKernel F y 2
  let q := Nat.card k
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite C := Finite.of_injective (inclusion
    (show C ≤ stabilizer F m from inf_le_left.trans (Q_le_stabilizer F m))) (inclusion_injective _)
  let : Finite Qm := Finite.of_injective (inclusion (Q_le_stabilizer F m)) (inclusion_injective _)
  let : Finite Qy := Finite.of_injective (inclusion (Q_le_stabilizer F y)) (inclusion_injective _)
  let : Finite K := Finite.of_injective (inclusion (ballKernel_le_stabilizer F y 2)) (inclusion_injective _)
  have hb : 2 < b F := by change 2 < b (reducedFamily L S); omega
  have hqpos : 0 < q := Nat.card_pos
  obtain ⟨_,hW,hlo,hup,hCE,ρ,_,hirr⟩ := source_suzuki_centralizer_irreducible
    h i hb3 hxadj hne T R hT hR e hz hcard hcardy hzx hzy hcommx hcommy
    hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear
  let _ := hW
  let _ := hCE
  let E := Additive (C ⧸ W.subgroupOf C)
  let τ := FrattiniAction.ofAutomorphismHom (ρ.comp e.symm.toMonoidHom)
  let : τ.IsIrreducible := hirr
  have hE : Nat.card E = q^4 := Representation.SL2.card_eq_four_of_odd_irreducible_bounds
    τ (show Odd (2*n+1) from ⟨n,rfl⟩) (by omega) hfield hlo hup
  have hWC : W ≤ C := (source_linear_second_kernel_span h i hb hxadj hne T hT e hcommy.le hnear).2.1.trans
    (source_suzuki_centralizer_second_kernel h i hb3 hxadj hne T R hT hR e hz
      hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch).2.1
  obtain ⟨_,_,_,_,hWcard,_⟩ := source_suzuki_span_natural
    h i hb3 hxadj hne T R hT hR e hz hcard hcardy hzx hzy hcommx hcommy
    hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear
  have hWCindex : W.relIndex C = q^4 := hE
  have hCcard : Nat.card C = q^9 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) W C bot_le hWC
    rw [relIndex_bot_left,relIndex_bot_left,hWCindex,hWcard] at hh
    exact hh.symm.trans (by dsimp [q]; ring)
  have hCQ : C.relIndex Qm = q^2 := by
    obtain ⟨_,hi,_⟩ := source_suzuki_centralizer_quotient
      h i hb3 hxadj hne T R hT hR e hz hcard hcardy hzx hzy hcommx hcommy
      hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch
    change (Qm ⊓ centralizer (ballKernel F m 3 : Set (G₀ L S))).relIndex Qm = _
    rw [inf_relIndex_left]
    exact hi
  have hQmcard : Nat.card Qm = q^11 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) C Qm bot_le inf_le_left
    rw [relIndex_bot_left,relIndex_bot_left,hCcard,hCQ] at hh
    exact hh.symm.trans (by ring)
  obtain ⟨P,_,hiLin,_⟩ := source_common_sylow_core_index h i e T hT
  have hiL : (Qy ⊓ Qm).relIndex Qy = q :=
    hiLin.trans ((Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 P).symm.toEquiv))
  obtain ⟨P',_,hiSuz,_⟩ := source_common_sylow_core_index h (!i) eSuz Ry hRy
  have hiS : (Qm ⊓ Qy).relIndex Qm = q^2 :=
    hiSuz.trans ((suzukiSylow_card hn (MulEquiv.refl _) P').trans (by dsimp [q]; rw [hfield]))
  have hB : Nat.card (Qm ⊓ Qy : Subgroup (G₀ L S)) = q^9 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) (Qm ⊓ Qy) Qm bot_le inf_le_left
    rw [relIndex_bot_left,relIndex_bot_left,hiS,hQmcard] at hh
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hqpos 2) (hh.trans (by ring))
  have hQycard : Nat.card Qy = q^10 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) (Qy ⊓ Qm) Qy bot_le inf_le_left
    rw [relIndex_bot_left,relIndex_bot_left,hiL,inf_comm Qy Qm,hB] at hh
    exact hh.symm.trans (by ring)
  have hfull := (source_suzuki_product_and_intersection_commutator h i hb hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin).2.2.2.1
  obtain ⟨_,_,_,hKindex,_⟩ := source_suzuki_second_kernel_layer h (!i) hb hc hxa
    (by simpa only [Bool.not_not] using hxadj.symm)
    hn hfield eSuz (by cases i <;> exact e) (by cases i <;> exact R)
    (by cases i <;> exact hR) Ry (by cases i <;> exact hRy) (by cases i <;> exact hzy)
    hcommy (by cases i <;> exact T) (by cases i <;> exact hT) (by cases i <;> exact hnat) hfull
  have hk : 4 ≤ Nat.card k := by
    rw [hfield]
    exact (by decide : 4 ≤ 2^2).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hKQ : K ≤ Qy := source_suzuki_second_kernel_le_core h (!i) eSuz
    (by cases i <;> exact e) hk y
  have hKcard : Nat.card K = q^6 := by
    have hi : K.relIndex Qy = q^4 := hKindex.trans (by dsimp [q]; rw [hfield])
    have hh := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) K Qy bot_le hKQ
    rw [relIndex_bot_left,relIndex_bot_left,hi,hQycard] at hh
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hqpos 4) (hh.trans (by ring))
  have hNW := (source_suzuki_full_linear_second_kernel h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear).1
  refine ⟨?_,hCcard,hQmcard,hQycard,hKcard,?_,?_,?_,?_⟩
  · change (ballKernel F m 2).relIndex C = _
    rw [hNW]
    exact hWCindex
  all_goals rw [card_map_of_injective (G₀ L S).subtype_injective]
  · exact hCcard
  · exact hQmcard
  · exact hQycard
  · exact hKcard

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
