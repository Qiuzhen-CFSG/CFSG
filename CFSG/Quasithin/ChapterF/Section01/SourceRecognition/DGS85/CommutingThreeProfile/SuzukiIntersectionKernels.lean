module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiCenterApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.NeighborSecondKernel
public import Theory.Representation.Suzuki.AbelianCentralizer
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiSpanFixedIndex

/-!
# The literal span intersections with full second kernels

The actual center-layer action identifies C_Y(X) with X intersect Y for
two Suzuki spans across a linear vertex. Kernel-Sylow control puts the
two-subgroup Y intersect G_x^(2) in Q_x, where the natural-center kernel
calculation identifies it with that same intersection. A linear neighbor
swap proves the reverse orientation. Both reduced-to-original inclusion
maps are retained.

This proves the identity used in the path argument of (12.8), with no
assumed intersection or centralizer equality. The earlier (12.1), (12.3)
data and the Suzuki marking remain explicit. It does not yet place the
whole nonbinary second kernel in Q or prove the path bound.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.6), (12.8), printed pp.183,185. The implementation import reuses the
private neighbor swap within this family without changing public APIs.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
open BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Both full second-kernel intersections and mutual span centralizers are the literal overlap. -/
theorem source_suzuki_intersection_kernels
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
    V F (base F (!i)) 1 ⊓ centralizer (V F x 1 : Set (G₀ L S)) = H ∧
    V F x 1 ⊓ centralizer (V F (base F (!i)) 1 : Set (G₀ L S)) = H ∧
    V F (base F (!i)) 1 ⊓ ballKernel F x 2 = H ∧
    V F x 1 ⊓ ballKernel F (base F (!i)) 2 = H ∧
    (V F (base F (!i)) 1).map (G₀ L S).subtype ⊓
      (ballKernel F x 2).map (G₀ L S).subtype = H.map (G₀ L S).subtype ∧
    (V F x 1).map (G₀ L S).subtype ⊓
      (ballKernel F (base F (!i)) 2).map (G₀ L S).subtype = H.map (G₀ L S).subtype := by
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
  have hH := suzuki_abelian_intersection_centralizer X Y C hC hXY hYX hn ρ
    (hfσ.comp eA.symm.injective) f P hP' hact hYcard (hcardy.trans hfield)
  have hQx : Q F x ≤ star L S i :=
    (le_sup_left.trans hR.ge).trans (map_subtype_le _)
  have hkernel := source_neighbor_core_span_centralizer h i hxadj.symm hQx hnat
  have hXcore := V_le_Q F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb x
  have hYN : Y ⊓ ballKernel F x 2 ≤ Q F x :=
    CommutingTrivial.two_subgroup_le_Q F x (reduced_kernel_sylow h x)
      ((IsElementaryAbelian.isPGroup 2 Y).to_le inf_le_left)
      (inf_le_right.trans (ballKernel_antitone F x (by decide : 1 ≤ 2)))
  have hYNH : Y ⊓ ballKernel F x 2 = X ⊓ Y := by
    apply le_antisymm
    · intro z hz
      exact hH.le ⟨hz.1,(hkernel.ge ⟨hYN hz,hz.2⟩).2⟩
    · intro z hz
      exact ⟨hz.2,(hkernel.le ⟨hXcore hz.1,(hH.ge hz).2⟩).2⟩
  obtain ⟨g,hgm,hgx,hgy⟩ := linear_neighbor_swap h i e hxadj hadj hne
  have hother : X ⊓ ballKernel F y 2 = X ⊓ Y := by
    have hh := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hYNH
    dsimp only [X,Y] at hh
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
      ←V_translate F, ←V_translate F, ←ballKernel_translate F, hgx,hgy] at hh
    exact hh.trans (inf_comm _ _)
  have hcentralOther : X ⊓ centralizer (Y : Set (G₀ L S)) = X ⊓ Y := by
    apply le_antisymm
    · intro z hz
      have hzQ : z ∈ Q F y := by
        have hc := source_span_centralizer_le_kernel (reduced_triple h) hadj.symm
        have hzU : z ∈ U F y := hc ⟨hXA hz.1 |> star_le_stabilizer (!i),hz.2⟩
        exact ((source_suzuki_star_kernel h (!i) eSuz).le ⟨hXA hz.1,hzU⟩)
      have hyker := source_neighbor_core_span_centralizer h i hadj.symm
        ((le_sup_left.trans hT.ge).trans (map_subtype_le _)) hnat
      exact hother.le ⟨hz.1,(hyker.le ⟨hzQ,hz.2⟩).2⟩
    · intro z hz
      refine ⟨hz.1,?_⟩
      intro t ht
      exact congrArg Subtype.val (mul_comm (⟨t,ht⟩ : Y) ⟨z,hz.2⟩)
  have hmap₁ := congrArg (Subgroup.map (G₀ L S).subtype) hYNH
  have hmap₂ := congrArg (Subgroup.map (G₀ L S).subtype) hother
  rw [Subgroup.map_inf _ _ _ (G₀ L S).subtype_injective] at hmap₁ hmap₂
  exact ⟨hH,hcentralOther,hYNH,hother,hmap₁,hmap₂⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
