module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiSpanNatural
public import Theory.Representation.ElementarySeedQuotient

/-!
# The Suzuki conjugates of the middle elementary span

Put K = G_y^(2), Y = V_y and W = ⟨(Y ∩ Q_x)^(G_m)⟩, with m the
linear vertex and x,y its distinct Suzuki neighbors. The proved identity
Ω₁(K) = Y and the elementary structure of W identify W ∩ K with Y ∩ Q_x.
Since Q_y normalizes W and Q_y/K is elementary, [W,Q_y] lies in that
intersection. All Suzuki-star conjugates of W consequently centralize
Q_y/Y.

The positive branch commutator prevents W from lying in K, since K
centralizes Y. Irreducibility of the already constructed literal Q_y/K
action now shows that J = ⟨W^(star_y)⟩ supplements K in Q_y. The proof
uses the original local quotient representation and its conjugation formula;
the conclusions also retain the original completion inclusion and normal span.

This establishes the seed action needed in the inference preceding (3),
not the complete equality [Q_y,Q_y] = Y or the later C_(Q_m)(H)/W
irreducibility and G_m^(2) = W. All earlier source, marking and reciprocal
commutator premises remain explicit.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
proof of (12.9), printed p.188.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
open BenderSuzuki.MatrixGroups
open scoped MatrixGroups commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
/-- The literal middle span has elementary displacement, and its Suzuki-star
normal span centralizes Q_y/Y and surjects onto Q_y/G_y^(2). -/
theorem source_suzuki_core_span_supplement
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
    let Y := V F y 1
    let K := ballKernel F y 2
    let W := conjugateSpanBy (Y ⊓ Q F x) (stabilizer F m)
    let J := conjugateSpanBy W (star L S (!i))
    W ⊓ K = Y ⊓ Q F x ∧
    ⁅W,Q F y⁆ ≤ Y ⊓ Q F x ∧
    ⁅J,Q F y⁆ ≤ Y ∧ J ⊔ K = Q F y ∧
    J.map (G₀ L S).subtype = conjugateSpanBy (W.map (G₀ L S).subtype)
      ((star L S (!i)).map (G₀ L S).subtype) ∧
    ⁅J.map (G₀ L S).subtype,(Q F y).map (G₀ L S).subtype⁆ ≤ Y.map (G₀ L S).subtype ∧
    J.map (G₀ L S).subtype ⊔ K.map (G₀ L S).subtype = (Q F y).map (G₀ L S).subtype := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let Y := V F y 1
  let K := ballKernel F y 2
  let Qy := Q F y
  let A := star L S (!i)
  let W := conjugateSpanBy (Y ⊓ Q F x) (stabilizer F m)
  let J := conjugateSpanBy W A
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hb : 2 < b F := by change 2 < b (reducedFamily L S); omega
  have hadj : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  have hspan := source_linear_second_kernel_span h i hb hxadj hne T hT e hcommy.le hnear
  obtain ⟨hWel,hW2,_,hnW,hWY,_,hWQz,_,_⟩ := hspan
  let : IsElementaryAbelian 2 W := hWel
  have hWQ : W ≤ Qy := hWQz y hadj
  have hQym : Qy ≤ stabilizer F m :=
    ((source_Z_Q_U (reduced_triple h) y).2.trans
      (ballKernel_one_le_edge F hadj.symm)).trans inf_le_right
  have hQW : Qy ≤ normalizer (W : Set (G₀ L S)) := hQym.trans hnW
  have homega : omegaOneAmbient K = Y :=
    (source_suzuki_full_kernel_omegas h i hb3 hxadj hne T R hT hR e hz hcard hcardy
      hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch).1
  have hWK : W ⊓ K = Y ⊓ Q F x := (elementary_inf_eq_of_omega W K Y homega).trans hWY
  have hQyA : Qy ≤ star L S i := (le_sup_left.trans hT.ge).trans (map_subtype_le _)
  have hk : 4 ≤ Nat.card k := by
    rw [hfield]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : 2 ≤ 2*n+1)
  have hKQ : K ≤ Qy := source_suzuki_second_kernel_le_core h (!i) eSuz
    (by cases i <;> exact e) hk y
  let : (K.subgroupOf Qy).Normal := normal_subgroupOf_of_le_normalizer
    ((Q_le_stabilizer F y).trans (stabilizer_le_normalizer_ballKernel F y 2))
  let : IsElementaryAbelian 2 (Qy ⧸ K.subgroupOf Qy) :=
    source_second_kernel_elementary h (!i) (by cases i <;> exact hQyA)
      (by cases i <;> exact hnat) hcommy.le
  have hder : ⁅Qy,Qy⁆ ≤ K := by
    have hd := Normal.quotient_commutative_iff_commutator_le.mp
      (inferInstance : IsMulCommutative (Qy ⧸ K.subgroupOf Qy))
    have hh := map_mono (f := Qy.subtype) hd
    rw [map_subtype_commutator,subgroupOf_map_subtype] at hh
    exact hh.trans inf_le_left
  have hWcomm : ⁅W,Qy⁆ ≤ Y ⊓ Q F x := by
    exact (elementary_commutator_le_of_omega W Qy K Y hWQ hQW hder homega).trans hWY.le
  have hAQ : A ≤ normalizer (Qy : Set (G₀ L S)) :=
    (star_le_stabilizer (!i)).trans (CommutingTrivial.stabilizer_normalizes_Q F y)
  have hAY : A ≤ normalizer (Y : Set (G₀ L S)) :=
    (star_le_stabilizer (!i)).trans (stabilizer_normalizes_V F y 1)
  have hQA : Qy ≤ A := by
    change Q F y ≤ A
    rw [←star_core h (!i)]
    exact pCoreIn_le 2 _
  have hJQ : J ≤ Qy := conjugateSpanBy_le hWQ hAQ
  have hJcomm : ⁅J,Qy⁆ ≤ Y := by
    have hQY := hQA.trans hAY
    exact ((commutator_mono (conjugateSpanBy_le
      (le_commutatorPreimage hWQ (hWcomm.trans inf_le_left))
      (commutatorPreimage_normalized Qy Qy Y A hQY hAQ hAQ hAY)) le_rfl).trans
      (commutator_commutatorPreimage_le Qy Qy Y hQY))
  have hWnotK : ¬ W ≤ K := by
    intro hWKle
    have hB : V F x 1 ⊓ Qy ≤ W :=
      (source_suzuki_second_kernel_span_order h i hb hxadj hne T R hT hR e hz hcard hcardy
        hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hnear).2.2.2.1.ge.trans inf_le_left
    have hcent := source_suzuki_second_kernel_centralizer h (!i) eSuz
      (by cases i <;> exact e) hk (by cases i <;> exact hQyA) (by cases i <;> exact hnat)
    exact hbranch (commutator_eq_bot_iff_le_centralizer.mpr
      ((hB.trans hWKle).trans (hcent.ge.trans inf_le_right)))
  have hfull := (source_suzuki_product_and_intersection_commutator h i hb hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin).2.2.2.1
  obtain ⟨ρ,_,hirr,_,hρ⟩ := source_suzuki_second_kernel_layer h (!i) hb hc hxa (by simpa only [Bool.not_not] using hxadj.symm)
    hn hfield eSuz (by cases i <;> exact e) (by cases i <;> exact R)
    (by cases i <;> exact hR) Ry (by cases i <;> exact hRy) (by cases i <;> exact hzy)
    hcommy (by cases i <;> exact T) (by cases i <;> exact hT) (by cases i <;> exact hnat) hfull
  let := hirr
  have hgen : J ⊔ K = Qy := by
    apply (inf_or_sup_of_irreducible_quotient Qy K J hKQ hJQ
      (fun u => (originalActor (L := L) (S := S) (!i) u : G₀ L S))
      (QuotientGroup.mk' (pCore 2 (L (if !i then 1 else 0))))
      (QuotientGroup.mk'_surjective _)
      (fun u => hAQ (originalActor (L := L) (S := S) (!i) u).property)
      (fun u => le_normalizer_conjugateSpanBy W A
        (originalActor (L := L) (S := S) (!i) u).property) ρ hρ).resolve_left
    intro hJK
    exact hWnotK ((le_conjugateSpanBy W A).trans hJK)
  refine ⟨hWK,hWcomm,hJcomm,hgen,?_,?_,?_⟩
  · exact map_conjugateSpanBy W A (G₀ L S).subtype
  · have hh := map_mono (f := (G₀ L S).subtype) hJcomm
    rwa [map_commutator] at hh
  · have hh := congrArg (Subgroup.map (G₀ L S).subtype) hgen
    rwa [Subgroup.map_sup] at hh
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
