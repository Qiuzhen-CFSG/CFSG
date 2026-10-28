module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiExactCoreOrders
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.LinearCenterNatural

/-!
# The marked top and irreducible radius-two layers

Construct the linear center from the earlier minimality, Sylow, order and
commutator data. The equivariant isomorphism Q_m/C_(Q_m)(G_m^(3)) ≃ Z_m
then transports those coordinates to the literal source denominator
V_m^(2). Its matrix action is the prescribed original SL₂(k) marking,
with no separately chosen field or natural-action premise.

The established centralizer and full second-kernel identities likewise
put the irreducible quotient on the literal V_m^(2)/G_m^(2). Its order
is q⁴ and its action uses the original endpoint quotient and conjugation.
Both results construct their natural-center input using LinearCenterNatural.
Earlier field/quotient markings, critical geometry, minimality, orders and
reciprocal commutators remain genuine source inputs. These statements do
not select the Suzuki branch or discharge the binary alternatives.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.9)(c4), printed p.186, with proof on pp.188--190.
-/

public noncomputable section
open Subgroup Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial BenderSuzuki.MatrixGroups
local instance suzukiMarkedLayersBinaryAlgebra {k : Type*} [Field k] [CharP k 2] : Algebra (ZMod 2) k := ZMod.algebra k 2
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Natural coordinates on Q_alpha/V_alpha^(2), with the original SL₂ marking and inclusion. -/
theorem source_suzuki_marked_top_layer
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
    (hbranch : ⁅V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i)),
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥)
    (hnear : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) x,
      V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥) :
    let F := reducedFamily L S
    let m := base F i
    let A := star L S i
    let Qm := Q F m
    let U := V F m 2
    let π := e.toMonoidHom.comp ((originalQuotient h i).symm.toMonoidHom.comp
      (QuotientGroup.mk' (pCore 2 A)))
    ∃ d : BinaryConjugationSection A Qm U
      ((SL2NaturalOffenders.NoStrong.natural (F := k)).comp π),
      U.relIndex Qm = Nat.card k ^ 2 ∧
      ∀ u : L (if i then 1 else 0), ∀ q : Qm,
        (d.coordinates ⟨(originalActor (L := L) (S := S) i u : G₀ L S) * q *
          (originalActor (L := L) (S := S) i u : G₀ L S)⁻¹,
          (mem_normalizer_iff.mp (d.normalized
            (originalActor (L := L) (S := S) i u).property) q).mp q.property⟩).toAdd =
          Matrix.mulVec (e (QuotientGroup.mk u)).val (d.coordinates q).toAdd := by
  let F := reducedFamily L S
  let m := base F i
  let A := star L S i
  let Qm := Q F m
  let H := ballKernel F m 3
  let C := Qm ⊓ centralizer (H : Set (G₀ L S))
  let U := V F m 2
  let π := e.toMonoidHom.comp ((originalQuotient h i).symm.toMonoidHom.comp
    (QuotientGroup.mk' (pCore 2 A)))
  have hnat := source_linear_hasNaturalCenter h i T hT e hcard hcardy hzy hcommy.le hmin hz
  obtain ⟨dZ⟩ := source_linear_center_marked_natural h i T hT e hcard hcardy hzy hcommy.le hmin
  obtain ⟨hN,horder,E,hE⟩ := source_suzuki_centralizer_quotient h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch
  let := hN
  have hEq : C = U := (source_suzuki_centralizer_eq_radius_two_span h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear).1
  have hden : U.subgroupOf Qm = (centralizer (H : Set (G₀ L S))).subgroupOf Qm := by
    rw [←hEq]
    ext q
    exact and_iff_right q.property
  let : (U.subgroupOf Qm).Normal := hden.symm ▸ hN
  let E' : (Qm ⧸ U.subgroupOf Qm) ≃* Z F m :=
    (QuotientGroup.quotientMulEquivOfEq hden).trans E
  have hQA : Qm ≤ A := (le_sup_right.trans hT.ge).trans (map_subtype_le _)
  have hAQ : A ≤ normalizer (Qm : Set (G₀ L S)) :=
    (star_le_stabilizer i).trans (CommutingTrivial.stabilizer_normalizes_Q F m)
  let dQ : BinaryConjugationSection A Qm U
      ((SL2NaturalOffenders.NoStrong.natural (F := k)).comp π) :=
    BinaryConjugationSection.of_equivariant_quotient A Qm U (Z F m) dZ hQA
      (hEq.ge.trans inf_le_left) hAQ E' hE
  have hindex : U.relIndex Qm = Nat.card k ^ 2 := by
    change (U.subgroupOf Qm).index = _
    rw [hden,index_eq_card]
    exact horder
  refine ⟨dQ,hindex,?_⟩
  intro u q
  have hh := dQ.equivariant (originalActor (L := L) (S := S) i u) q
  have hπ : π (originalActor (L := L) (S := S) i u) = e (QuotientGroup.mk u) := by
    change e ((originalQuotient h i).symm (QuotientGroup.mk
      (originalActor (L := L) (S := S) i u))) = _
    change e ((originalQuotient h i).symm ((originalQuotient h i) (QuotientGroup.mk u))) = _
    rw [(originalQuotient h i).symm_apply_apply]
  change (dQ.coordinates _).toAdd = Matrix.mulVec (π (originalActor (L := L) (S := S) i u)).val _ at hh
  rw [hπ] at hh
  exact hh

/-- The literal radius-two span modulo the full second kernel is irreducible of order q⁴. -/
theorem source_suzuki_radius_two_quotient_irreducible
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
    (hbranch : ⁅V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i)),
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥)
    (hnear : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) x,
      V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥) :
    let F := reducedFamily L S
    let m := base F i
    let A := star L S i
    let C := V F m 2
    let W := ballKernel F m 2
    ∃ hAC : A ≤ normalizer (C : Set (G₀ L S)),
    ∃ hW : (W.subgroupOf C).Normal,
      letI := hW
      let E := C ⧸ W.subgroupOf C
      Nat.card E = Nat.card k ^ 4 ∧
      ∃ hCE : IsElementaryAbelian 2 E,
        letI := hCE
        ∃ ρ : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) →*
          MulAut E,
          (∀ t : A, ∀ c : C,
            ρ ((originalQuotient h i).symm (QuotientGroup.mk' (pCore 2 A) t)) (QuotientGroup.mk' (W.subgroupOf C) c) =
              QuotientGroup.mk' (W.subgroupOf C) ⟨(t : G₀ L S)*c*(t : G₀ L S)⁻¹,
                (mem_normalizer_iff.mp (hAC t.property) c).mp c.property⟩) ∧
          let τ : Representation (ZMod 2) SL(2,k) (Additive E) :=
            FrattiniAction.ofAutomorphismHom (ρ.comp e.symm.toMonoidHom)
          τ.IsIrreducible := by
  let F := reducedFamily L S
  let m := base F i
  let C := Q F m ⊓ centralizer (ballKernel F m 3 : Set (G₀ L S))
  let W := conjugateSpanBy (V F (base F (!i)) 1 ⊓ Q F x) (stabilizer F m)
  have hnat := source_linear_hasNaturalCenter h i T hT e hcard hcardy hzy hcommy.le hmin hz
  have hEq : C = V F m 2 := (source_suzuki_centralizer_eq_radius_two_span h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear).1
  have hNW : ballKernel F m 2 = W := (source_suzuki_full_linear_second_kernel h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear).1
  have hsize : W.relIndex C = Nat.card k ^ 4 := by
    rw [←hNW]
    exact (source_suzuki_exact_core_orders h i hb3 hxadj hne T R hT hR e hz
      hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear).1
  obtain ⟨hAC,hW,_,_,hel,ρ,hρ,hirr⟩ := source_suzuki_centralizer_irreducible h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear
  dsimp only
  change ∃ hAC : star L S i ≤ normalizer (V F m 2 : Set (G₀ L S)), _
  rw [←hEq,hNW]
  exact ⟨hAC,hW,hsize,hel,ρ,hρ,hirr⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
