module
public import Theory.Representation.SL2.NaturalResidualFixed
public import Theory.GroupTheory.CentralizerInjectiveImage
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearEnlargement
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.LinearNaturalLayer

/-!
# The literal residual quotient in the linear-neighbor row

The natural layer constructed in LinearNaturalLayer is V_y/Z_y. Source
(8.5) concerns V_y/C_{V_y}(O²(L_y)), where L_y is the intrinsic graph
local group. We identify these exact denominators before applying that
source theorem.

The common Sylow Q_m Q_y centralizes Z_y, since Z_y lies in Z_m.
Normality of Z_y and generation by two conjugate Sylows make the whole
starred endpoint centralize Z_y. In the other direction, a residual-fixed
vector maps to zero in the natural quotient: its original two-residual
maps onto a subgroup containing an order-three matrix with no nonzero
fixed vectors. This includes the binary field. The original completion
inclusion preserves the relative centralizer, and the proved linear
local-group equality identifies the intrinsic source actor with the star.

The final application constructs natural coordinates and order q² for the
literal residual-centralizer quotient from the preceding linear-row inputs.
It preserves the original quotient marking and conjugation formula. The
independent (8.5) nonnaturality theorem remains with
qt-dgs85-critical-commuting-nontrivial; no linear exclusion is claimed here.
Earlier common Sylows, natural-center data and conjugated indices remain
explicit. D10/binary exclusions and the full (12.9)/(13.1) assembly remain
obligations of this theorem family.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(8.5), (12.1), (12.3), printed pp.139,178--180.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- A center included in the neighboring center is fixed by the whole starred endpoint. -/
theorem source_center_centralizes_star_of_neighbor_inclusion
    (h : HypothesisF11 L S) (i : Bool)
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) i) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i)) :
    Z (reducedFamily L S) (base (reducedFamily L S) i) ≤
      centralizer (star L S i : Set (G₀ L S)) := by
  let F := reducedFamily L S
  let A := star L S i
  let C := centralizer (Z F (base F i) : Set (G₀ L S))
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite A := Finite.of_injective (inclusion (star_le_stabilizer i))
    (inclusion_injective _)
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  have hnZ : A ≤ normalizer (Z F (base F i) : Set (G₀ L S)) :=
    (star_le_stabilizer i).trans (stabilizer_normalizes_Z F _)
  have hTC : (T : Subgroup A).map A.subtype ≤ C := by
    rw [hT]
    exact sup_le (le_centralizer_iff.mp (hzy.trans (Z_centralizes_Q F _ (hZ _))))
      (le_centralizer_iff.mp (Z_centralizes_Q F _ (hZ _)))
  have hmodel : IsRankOneModel (A ⧸ pCore 2 A) :=
    (h.quotient (if i then 1 else 0)).of_equiv (originalQuotient h i).symm
  obtain ⟨g,hg⟩ := SetLike.exists_not_mem_of_ne_top (normalizer (T : Set A))
    (rankOneSylowFacts_of_rankOneQuotient hmodel T).proper.ne
  have hne : T ≠ g • T := by
    intro he
    exact hg (Sylow.smul_eq_iff_mem_normalizer.mp he.symm)
  have hpair := rankOne_sylow_pair_generates A hmodel T (g • T) hne
  apply le_centralizer_iff.mpr
  change A ≤ C
  rw [← hpair]
  apply sup_le hTC
  have he : ((g • T : Sylow 2 A) : Subgroup A).map A.subtype =
      ((T : Subgroup A).map A.subtype).map (MulAut.conj (g : G₀ L S)).toMonoidHom := by
    change ((T : Subgroup A).map (MulAut.conj g).toMonoidHom).map A.subtype = _
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  rw [he]
  exact (map_mono hTC).trans (mem_normalizer_iff_map_conj_eq.mp
    ((normalizer_le_normalizer_centralizer (Z F (base F i))) (hnZ g.property))).le

/-- The original local inclusion viewed in the reduced completion. -/
def originalActorHom (i : Bool) : L (if i then 1 else 0) →* G₀ L S where
  toFun x := (originalActor (L := L) (S := S) i x : G₀ L S)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Mapping the reduced actor back to the original completion is the original inclusion. -/
theorem originalActorHom_coe (i : Bool) (x : L (if i then 1 else 0)) :
    ((originalActorHom (L := L) (S := S) i x : G₀ L S) : G) = x := rfl

/-- The source's intrinsic linear local group is the actual starred subgroup. -/
theorem source_linear_graphLocalGroup_eq_star
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k)) :
    graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i) = star L S i := by
  apply map_injective (G₀ L S).subtype_injective
  rw [reduced_graphLocalGroup_image h]
  change family (enlargedEndpoint L S) i =
    ((starredParabolic L S (if i then 1 else 0)).subgroupOf (G₀ L S)).map (G₀ L S).subtype
  rw [map_subgroupOf_eq_of_le (star_le_completion _)]
  cases i
  · exact reduced_enlargedEndpoint_eq_starred_of_linear h 0
      (e.trans (Theory.PSL2.sl2QuotientEquiv k))
  · exact reduced_enlargedEndpoint_eq_starred_of_linear h 1
      (e.trans (Theory.PSL2.sl2QuotientEquiv k))

local instance {k : Type*} [Field k] [CharP k 2] : Algebra (ZMod 2) k := ZMod.algebra k 2

/-- Natural coordinates identify both the original and starred residual denominators. -/
theorem source_natural_residual_denominators
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) i) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k)) :
    let F := reducedFamily L S
    let y := base F i
    let D := V F y 1
    let := V_elementary F (reduced_triple h).generate
      (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb y
    let : ((Z F y).subgroupOf D).Normal := normal_of_isMulCommutative _
    ∀ E : Additive (D ⧸ (Z F y).subgroupOf D) ≃ₗ[ZMod 2] (Fin 2 → k),
    (∀ u : L (if i then 1 else 0), ∀ d : D,
      E (Additive.ofMul (QuotientGroup.mk
        ⟨(originalActor (L := L) (S := S) i u : G₀ L S) * d *
          (originalActor (L := L) (S := S) i u : G₀ L S)⁻¹,
          (mem_normalizer_iff.mp (star_normalizes_span h i
            (originalActor (L := L) (S := S) i u).property) d).mp d.property⟩)) =
        Matrix.mulVec (e (QuotientGroup.mk u)).val (E (Additive.ofMul (QuotientGroup.mk d)))) →
    D ⊓ centralizer ((pResidual 2 (L (if i then 1 else 0))).map
      (originalActorHom (L := L) (S := S) i) : Set (G₀ L S)) = Z F y ∧
    D ⊓ centralizer ((pResidual 2 (star L S i)).map (star L S i).subtype : Set (G₀ L S)) =
      Z F y ∧
    D.map (G₀ L S).subtype ⊓ centralizer ((pResidual 2 (L (if i then 1 else 0))).map
      (L (if i then 1 else 0)).subtype : Set G) = (Z F y).map (G₀ L S).subtype ∧
    D ⊓ centralizer ((pResidual 2 (graphLocalGroup F y)).map
      (graphLocalGroup F y).subtype : Set (G₀ L S)) = Z F y := by
  dsimp only
  intro E hE
  let F := reducedFamily L S
  let y := base F i
  let D := V F y 1
  let := h.finite_local (if i then 1 else 0)
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let := V_elementary F (reduced_triple h).generate
    (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb y
  let : ((Z F y).subgroupOf D).Normal := normal_of_isMulCommutative _
  let f := originalActorHom (L := L) (S := S) i
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (L (if i then 1 else 0))))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hcentral := source_center_centralizes_star_of_neighbor_inclusion h i hzy T hT
  have horig : D ⊓ centralizer ((pResidual 2 (L (if i then 1 else 0))).map f : Set (G₀ L S)) = Z F y := by
    apply le_antisymm
    · intro z hz
      let d : D := ⟨z,hz.1⟩
      have hz0 : E (Additive.ofMul (QuotientGroup.mk d)) = 0 := by
        apply Matrix.SL2.natural_residual_fixed_eq_zero q hq
        intro u hu
        have hc : f u * z * (f u)⁻¹ = z := by
          rw [hz.2 (f u) (mem_map_of_mem f hu),mul_inv_cancel_right]
        have he := hE u d
        have hd : (⟨(originalActor (L := L) (S := S) i u : G₀ L S) * d *
            (originalActor (L := L) (S := S) i u : G₀ L S)⁻¹,
            (mem_normalizer_iff.mp (star_normalizes_span h i
              (originalActor (L := L) (S := S) i u).property) d).mp d.property⟩ : D) = d :=
          Subtype.ext hc
        rw [hd] at he
        exact he.symm
      have hd0 : Additive.ofMul (QuotientGroup.mk d : D ⧸ (Z F y).subgroupOf D) = 0 :=
        E.map_eq_zero_iff.mp hz0
      exact (QuotientGroup.eq_one_iff d).mp (congrArg Additive.toMul hd0)
    · intro z hz
      refine ⟨Z_le_V F y 1 hz,?_⟩
      rintro _ ⟨u,hu,rfl⟩
      exact hcentral hz _ (originalActor (L := L) (S := S) i u).property
  have hres : (pResidual 2 (L (if i then 1 else 0))).map f ≤
      (pResidual 2 (star L S i)).map (star L S i).subtype := by
    let j : L (if i then 1 else 0) →* star L S i := {
      toFun := originalActor i
      map_one' := rfl
      map_mul' _ _ := rfl }
    have hh := map_mono (f := (star L S i).subtype) (map_pResidual_le 2 j)
    rw [Subgroup.map_map] at hh
    exact hh
  have hstar : D ⊓ centralizer ((pResidual 2 (star L S i)).map
      (star L S i).subtype : Set (G₀ L S)) = Z F y := by
    apply le_antisymm ((inf_le_inf_left _ (centralizer_le hres)).trans horig.le)
    exact le_inf (Z_le_V F y 1)
      (hcentral.trans (centralizer_le (map_subtype_le _)))
  refine ⟨horig,hstar,?_,?_⟩
  · have hm := congrArg (Subgroup.map (G₀ L S).subtype) horig
    rw [← map_inf_centralizer_of_injective _ (G₀ L S).subtype_injective,
      Subgroup.map_map] at hm
    exact hm
  · change D ⊓ centralizer ((pResidual 2 (graphLocalGroup F (base F i))).map
      (graphLocalGroup F (base F i)).subtype : Set (G₀ L S)) = Z F y
    rw [source_linear_graphLocalGroup_eq_star h i e]
    exact hstar

/-- The linear-row hypotheses construct the natural module on the exact residual-centralizer quotient of (8.5). -/
theorem source_linear_intersection_residual_natural
    {k l : Type*} [Field k] [Finite k] [CharP k 2]
    [Field l] [Finite l] [CharP l 2]
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
      Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ ≤
        Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcross : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) σ,
      V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥)
    (hsmall : (Q (reducedFamily L S) σ).relIndex
      (V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1) ≤ Nat.card k)
    (hactor : (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex
      (V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* Matrix.SpecialLinearGroup (Fin 2) l)
    (hfield : Nat.card k = Nat.card l)
    (Ry : Sylow 2 (star L S (!i)))
    (hRy : (Ry : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) (!i)))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i)) :
    let F := reducedFamily L S
    let y := base F (!i)
    let D := V F y 1
    let := V_elementary F (reduced_triple h).generate
      (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb y
    let A := graphLocalGroup F y
    let C := (centralizer ((pResidual 2 A).map A.subtype : Set (G₀ L S))).subgroupOf D
    let : C.Normal := normal_of_isMulCommutative _
    D ⊓ centralizer ((pResidual 2 A).map A.subtype : Set (G₀ L S)) = Z F y ∧
    Nat.card (D ⧸ C) = Nat.card l ^ 2 ∧
      ∃ E : Additive (D ⧸ C) ≃ₗ[ZMod 2] (Fin 2 → l),
        ∀ u : L (if !i then 1 else 0), ∀ d : D,
          E (Additive.ofMul (QuotientGroup.mk
            ⟨(originalActor (L := L) (S := S) (!i) u : G₀ L S) * d *
              (originalActor (L := L) (S := S) (!i) u : G₀ L S)⁻¹,
              (mem_normalizer_iff.mp (star_normalizes_span h (!i)
                (originalActor (L := L) (S := S) (!i) u).property) d).mp d.property⟩)) =
            Matrix.mulVec (eLin (QuotientGroup.mk u)).val (E (Additive.ofMul (QuotientGroup.mk d))) := by
  let F := reducedFamily L S
  let y := base F (!i)
  let D := V F y 1
  let A := graphLocalGroup F y
  let C := (centralizer ((pResidual 2 A).map A.subtype : Set (G₀ L S))).subgroupOf D
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let := V_elementary F (reduced_triple h).generate
    (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb y
  let : ((Z F y).subgroupOf D).Normal := normal_of_isMulCommutative _
  let : C.Normal := normal_of_isMulCommutative _
  obtain ⟨horder,E,hE⟩ := source_linear_intersection_natural h i hb hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor eLin hfield Ry hRy hc hxa hmin
  have hzy' : Z F y ≤ Z F (base F (!(!i))) := by simpa only [Bool.not_not] using hzy
  have hRy' : (Ry : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q F (base F (!(!i))) ⊔ Q F y := by simpa only [Bool.not_not] using hRy
  have hden := (source_natural_residual_denominators h (!i) hb hzy' Ry hRy' eLin E hE).2.2.2
  change D ⊓ centralizer ((pResidual 2 A).map A.subtype : Set (G₀ L S)) = Z F y at hden
  have hC : C = (Z F y).subgroupOf D := by
    ext d
    change (d : G₀ L S) ∈ centralizer ((pResidual 2 A).map A.subtype : Set (G₀ L S)) ↔
      (d : G₀ L S) ∈ Z F y
    constructor
    · intro hd
      exact hden ▸ (show (d : G₀ L S) ∈ D ⊓ centralizer
        ((pResidual 2 A).map A.subtype : Set (G₀ L S)) from ⟨d.property,hd⟩)
    · intro hd
      exact (show (d : G₀ L S) ∈ D ⊓ centralizer
        ((pResidual 2 A).map A.subtype : Set (G₀ L S)) from hden.symm ▸ hd).2
  refine ⟨hden,?_⟩
  dsimp only [C,A,D,y,F] at hC ⊢
  rw [hC]
  exact ⟨horder,E,hE⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
