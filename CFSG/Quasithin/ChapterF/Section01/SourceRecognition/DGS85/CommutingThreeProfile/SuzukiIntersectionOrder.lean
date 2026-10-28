module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiCenterApplication
public import Theory.Representation.Suzuki.AbelianIntersection

/-!
# The literal intersection order in the nonbinary branch of DGS 12.6

The preceding center-layer application supplies |V_y/Z_y| = q^4.
Construct its actual starred conjugation action and identify the image of
V_x with the whole Suzuki Sylow omega-center using the proved first index
of (12.3)(a). Both spans lie in the middle core, so each normalizes the
other. The neighboring-center inclusion puts Z_y in their intersection.

Apply the faithful action and dual square bounds to this same quotient:
the intersection image contains the moved space and lies in the fixed
space, hence has order q^2. Thus |V_x intersect V_y| = q^3, also under
the literal inclusion into the original completion. No intersection
order, fixed-space size or natural Suzuki coordinates are assumed.

All earlier inputs are those of SuzukiCenterApplication. The original
linear and Suzuki markings, common parameter and (12.1) data remain
explicit. The full second/third-kernel equalities, binary case, selection
in (12.5) and final (12.9)/(13.1) assembly remain with this source family.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.6)(c) and (12.9)(c3), printed pp.183 and186.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
open BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The source spans have intersection of order q³, with the original inclusion retained. -/
theorem source_suzuki_intersection_card
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
      (Q (reducedFamily L S) (base (reducedFamily L S) i))) :
    let F := reducedFamily L S
    let H := V F x 1 ⊓ V F (base F (!i)) 1
    Nat.card H = (2^(2*n+1))^3 ∧
      Nat.card (H.map (G₀ L S).subtype) = (2^(2*n+1))^3 := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let A := star L S (!i)
  let X := V F x 1
  let Y := V F y 1
  let C := Z F y
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  have hQU := fun v => (source_Z_Q_U (reduced_triple h) v).2
  have hadj : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  let := V_elementary F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb x
  let := V_elementary F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb y
  let : (C.subgroupOf Y).Normal := normal_of_isMulCommutative _
  let : Finite Y := Finite.of_injective
    (inclusion ((V_le_Q F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb y).trans
      (Q_le_stabilizer F y))) (inclusion_injective _)
  obtain ⟨_,_,_,ρ₀,_,_,hYcard,_⟩ := source_suzuki_center_layer_of_intersection
    h i hb hxadj hne T R hT hR e hz hcard hcardy hzx hzy hcommx hcommy
    hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat
  have hAY := star_normalizes_span h (!i)
  obtain ⟨σ,hσ⟩ := exists_center_layer_action F (reduced_triple h).generate hZ
    (reduced_kernel_sylow h) hb y A (star_le_stabilizer (!i)) (star_core h (!i)).le hcommy.le
  have hAC : A ≤ centralizer (C : Set (G₀ L S)) := le_centralizer_iff.mp
    (source_center_centralizes_star_of_neighbor_inclusion h (!i)
      (by simpa only [Bool.not_not] using hzy) Ry (by simpa only [Bool.not_not] using hRy))
  have hfσ := central_quotient_conjugation_faithful A Y C hAY hAC
    (source_suzuki_span_centralizer_le_core h (!i) eSuz) σ hσ
  let eA := (originalQuotient h (!i)).symm.trans eSuz
  let q := eA.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  let ρ := σ.comp eA.symm.toMonoidHom
  have hXQ : X ≤ Q F m :=
    V_le_neighbor_Q F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb hxadj.symm
  have hYQ : Y ≤ Q F m :=
    V_le_neighbor_Q F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb hadj.symm
  have hXA : X ≤ A := (hXQ.trans (le_sup_left.trans hRy.ge)).trans (map_subtype_le _)
  let f := q.comp (inclusion hXA)
  have hXY : X ≤ normalizer (Y : Set (G₀ L S)) :=
    ((hXQ.trans (hQU m)).trans ((ballKernel_one_le_edge F hadj).trans inf_le_right)).trans
      (stabilizer_normalizes_V F y 1)
  have hYX : Y ≤ normalizer (X : Set (G₀ L S)) :=
    ((hYQ.trans (hQU m)).trans ((ballKernel_one_le_edge F hxadj).trans inf_le_right)).trans
      (stabilizer_normalizes_V F x 1)
  obtain ⟨_,_,P,hP⟩ := source_suzuki_first_index h (!i) hb hc hxa hxadj.symm hadj.symm hn
    eSuz (by cases i <;> exact e) Ry hRy
  have hP' : f.range = omegaOneAmbient (P : Subgroup _) := by
    rw [MonoidHom.range_comp,inclusion_range]
    exact hP
  have hC : C ≤ X ⊓ Y := le_inf
    (hzy.trans (Z_neighbor_le_V F hxadj.symm)) (Z_le_V F y 1)
  have hact : ∀ u : X, ∀ v : Y,
      ρ (f u) (Additive.ofMul (QuotientGroup.mk v)) =
        Additive.ofMul (QuotientGroup.mk ⟨(u : G₀ L S) * v * (u : G₀ L S)⁻¹,
          le_normalizer_iff.mp hXY u u.property v v.property⟩) := by
    intro u v
    change σ (eA.symm (eA (QuotientGroup.mk (inclusion hXA u)))) _ = _
    rw [eA.symm_apply_apply]
    exact congrArg Additive.ofMul (hσ (inclusion hXA u) v)
  have hH := suzuki_abelian_intersection_card X Y C hC hXY hYX hn ρ
    (hfσ.comp eA.symm.injective) f P hP' hact hYcard (hcardy.trans hfield)
  exact ⟨hH,(card_map_of_injective (G₀ L S).subtype_injective).trans hH⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
