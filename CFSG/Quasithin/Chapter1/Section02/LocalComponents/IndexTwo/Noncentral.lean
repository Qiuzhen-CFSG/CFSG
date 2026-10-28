module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Projections
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.SmallSylow

/-!
# A nonsolvable component commutator in the index-two argument

Let `R` have index two in a Sylow two-subgroup `S`, and let `L ∈ L(G,R)`
lie in the C-component layer. A nontrivial coordinate of `L` modulo the
solvable radical is intrinsically a C-component. The image of `S ∩ L` is
Sylow in this coordinate and lies in the image of `S ∩ K`, where `K` is
the ambient C-component lifting that coordinate factor.

Lift that projected Sylow subgroup inside `S ∩ K`, and intersect the lift
with `R`. Intersections and homomorphic images cannot increase the index
beyond two. The small-Sylow obstruction makes the resulting commutator
nonsolvable; it is a homomorphic image of a subgroup of `[L,R ∩ K]`. No
normalization of `L` by `R`, or preservation of their intersections by the
radical quotient, is assumed.

This is the projection-to-commutator step in Aschbacher–Smith,
*The Classification of Quasithin Groups*, proof of Lemma 1.2.5, printed
p.505 (combined manuscript, 1 March 2004). The layer premise and the final
containment and uniqueness belong to the separate assembly.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.Section02.IndexTwo
variable {G : Type*} [Group G] [Finite G]

/-- Apply the intrinsic small-Sylow obstruction inside an arbitrary ambient group. -/
private theorem intrinsic_nonsolvable_commutator {X : Type*} [Group X] [Finite X]
    {P Q V : Subgroup X} (hP : (⊤ : Subgroup P).IsCComponent)
    (hQ : IsSylowIn 2 Q P) (hVP : V ≤ P) (hi : V.relIndex Q ≤ 2) :
    ¬ Group.IsSolvable (⁅P, V⁆ : Subgroup X) := by
  obtain ⟨T, hT⟩ := hQ
  let e : (⊤ : Subgroup P) ≃* P := topEquiv
  let T' := T.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let V' := (V.subgroupOf P).map e.symm.toMonoidHom
  have hi' : V'.relIndex (T' : Subgroup (⊤ : Subgroup P)) ≤ 2 := by
    change ((V.subgroupOf P).map e.symm.toMonoidHom).relIndex
      ((T : Subgroup P).map e.symm.toMonoidHom) ≤ 2
    rw [relIndex_map_map_of_injective _ _ e.symm.injective]
    have hm := relIndex_map_map_of_injective (V.subgroupOf P) (T : Subgroup P)
      P.subtype_injective
    rw [map_subgroupOf_eq_of_le hVP, hT] at hm
    exact hm ▸ hi
  intro hs
  let := hs
  have hf : Function.Injective (P.subtype.comp e.toMonoidHom) :=
    P.subtype_injective.comp e.injective
  have he : (⁅(⊤ : Subgroup (⊤ : Subgroup P)), V'⁆ : Subgroup (⊤ : Subgroup P)).map
      (P.subtype.comp e.toMonoidHom) = ⁅P, V⁆ := by
    rw [map_commutator, ← map_map, map_top_of_surjective _ e.surjective,
      ← MonoidHom.range_eq_map, P.range_subtype]
    congr 1
    change ((V.subgroupOf P).map e.symm.toMonoidHom).map
      (P.subtype.comp e.toMonoidHom) = V
    rw [map_map]
    have hid : (P.subtype.comp e.toMonoidHom).comp e.symm.toMonoidHom = P.subtype := by
      ext x
      simp
    rw [hid, map_subgroupOf_eq_of_le hVP]
  have hm : Group.IsSolvable ((⁅(⊤ : Subgroup (⊤ : Subgroup P)), V'⁆ :
      Subgroup (⊤ : Subgroup P)).map (P.subtype.comp e.toMonoidHom)) := he.symm ▸ hs
  let := hm
  exact nonsolvable_commutator_of_sylow_index_le_two hP T' V' hi'
    (Group.isSolvable_of_isSolvable_injective
      (f := (⁅(⊤ : Subgroup (⊤ : Subgroup P)), V'⁆ : Subgroup (⊤ : Subgroup P)).equivMapOfInjective
        (P.subtype.comp e.toMonoidHom) hf |>.toMonoidHom)
      ((⁅(⊤ : Subgroup (⊤ : Subgroup P)), V'⁆ : Subgroup (⊤ : Subgroup P)).equivMapOfInjective
        (P.subtype.comp e.toMonoidHom) hf).injective)

/-- The Sylow intersection with a subnormal subgroup commutes with taking images. -/
private theorem sylow_intersection_map (S : Sylow 2 G) {K : Subgroup G}
    (hK : K.IsSubnormal) {X : Type*} [Group X] (f : G →* X) :
    ((S : Subgroup G) ⊓ K).map f = (S : Subgroup G).map f ⊓ K.map f := by
  obtain ⟨T, hT⟩ := S.exists_subgroupOf_eq_of_subnormal K hK
  have hSK : IsSylowIn 2 ((S : Subgroup G) ⊓ K) K := by
    refine ⟨T, ?_⟩
    rw [hT, subgroupOf_map_subtype]
  have hm := (isSylowIn_iff.mp (isSylowIn_map hSK f)).2.2
  exact (hm _ ((S.isPGroup'.map f).to_le inf_le_left)
    (map_inf_le _ _ _) inf_le_right).symm

/-- On the lifted component, the coordinate map is precisely the radical quotient map. -/
private theorem radicalProjection_on_component
    (J : ComponentIndex (G ⧸ solvableRadical G)) {K : Subgroup G}
    (hK : K.IsCComponent)
    (he : K.map (QuotientGroup.mk' (solvableRadical G)) = J.1)
    (x : K) :
    radicalProjection J ⟨x, le_cComponentLayer hK x.2⟩ =
      ⟨QuotientGroup.mk' (solvableRadical G) x, he ▸ mem_map.mpr ⟨x, x.2, rfl⟩⟩ := by
  unfold radicalProjection radicalLayerMap
  exact componentProjection_self (solvableRadical_quotient_solvableRadical (G := G)) J
    ⟨QuotientGroup.mk' (solvableRadical G) x, he ▸ mem_map.mpr ⟨x, x.2, rfl⟩⟩

/-- The coordinate of an element of `S` lies in the corresponding quotient Sylow subgroup. -/
private theorem radicalProjection_sylow_mem
    (S : Sylow 2 G) (J : ComponentIndex (G ⧸ solvableRadical G))
    (x : cComponentLayer G) (hx : (x : G) ∈ (S : Subgroup G)) :
    radicalProjection J x ∈
      ((S : Subgroup G).map (QuotientGroup.mk' (solvableRadical G))).subgroupOf J.1 := by
  let T := S.mapSurjective (QuotientGroup.mk'_surjective (solvableRadical G))
  change radicalProjection J x ∈ (T : Subgroup _).subgroupOf J.1
  rw [← componentProjection_map_sylow (solvableRadical_quotient_solvableRadical (G := G)) T J]
  exact mem_map.mpr ⟨radicalLayerMap x, mem_map.mpr ⟨x, hx, rfl⟩, rfl⟩

/-- Lift a subgroup of the quotient Sylow intersection inside the actual component `K`. -/
private theorem radicalProjection_sylow_lift
    (S : Sylow 2 G) (J : ComponentIndex (G ⧸ solvableRadical G))
    {K : Subgroup G} (hK : K.IsCComponent)
    (he : K.map (QuotientGroup.mk' (solvableRadical G)) = J.1)
    (Q : Subgroup J.1)
    (hQ : Q ≤ ((S : Subgroup G).map
      (QuotientGroup.mk' (solvableRadical G))).subgroupOf J.1) :
    ∃ U : Subgroup G, U ≤ (S : Subgroup G) ⊓ K ∧
      (U.subgroupOf (cComponentLayer G)).map (radicalProjection J) = Q := by
  let q := QuotientGroup.mk' (solvableRadical G)
  let U := ((S : Subgroup G) ⊓ K) ⊓ (Q.map J.1.subtype).comap q
  have hU : U ≤ (S : Subgroup G) ⊓ K := inf_le_left
  have hmap : ((S : Subgroup G) ⊓ K).map q = (S : Subgroup G).map q ⊓ J.1 := by
    rw [sylow_intersection_map S hK.subnormal q, he]
  refine ⟨U, hU, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxK : (x : G) ∈ K := (hU hx).2
    have hcoord := radicalProjection_on_component J hK he ⟨x, hxK⟩
    rw [hcoord]
    obtain ⟨z, hz, hez⟩ := (show q (x : G) ∈ Q.map J.1.subtype from hx.2)
    exact (Subtype.ext hez : z = ⟨q x, he ▸ mem_map.mpr ⟨x, hxK, rfl⟩⟩) ▸ hz
  · intro hy
    have hym : (y : G ⧸ solvableRadical G) ∈ ((S : Subgroup G) ⊓ K).map q :=
      hmap.symm ▸ ⟨hQ hy, y.2⟩
    obtain ⟨x, hx, hxy⟩ := mem_map.mp hym
    have hxU : x ∈ U := ⟨hx, mem_map.mpr ⟨y, hy, hxy.symm⟩⟩
    refine mem_map.mpr ⟨⟨x, le_cComponentLayer hK hx.2⟩, hxU, ?_⟩
    rw [radicalProjection_on_component J hK he ⟨x, hx.2⟩]
    exact Subtype.ext hxy

/-- The index-two hypothesis detects a nonsolvable commutator in some ambient C-component. -/
theorem exists_nonsolvable_component_commutator_of_index_two
    (S : Sylow 2 G) {R L : Subgroup G}
    (hRS : R ≤ S) (hidx : R.relIndex (S : Subgroup G) = 2)
    (hL : L ∈ Chapter1.L G R) (hLayer : L ≤ cComponentLayer G) :
    ∃ K : Subgroup G, K.IsCComponent ∧
      ¬ Group.IsSolvable (⁅L, R ⊓ K⁆ : Subgroup G) := by
  obtain ⟨J, hJ⟩ := exists_nontrivial_radicalProjection (mem_L_not_isSolvable hL) hLayer
  let E := cComponentLayer G
  let π := radicalProjection J
  let B := L.subgroupOf E
  let P := B.map π
  let f : (L.subgroupOf (L ⊔ R)) →* J.1 :=
    π.comp ((inclusion hLayer).comp
      (subgroupOfEquivOfLe (show L ≤ L ⊔ R from le_sup_left)).toMonoidHom)
  have hf : f.range = P := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact mem_map.mpr ⟨⟨x, hLayer x.2⟩, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨⟨x, (show L ≤ L ⊔ R from le_sup_left) hx⟩, hx⟩, rfl⟩
  have hP : (⊤ : Subgroup P).IsCComponent := by
    have hc := cComponent_nontrivial_range hL.1 f (hf.symm ▸ hJ)
    rwa [hf] at hc
  have hSL : IsSylowIn 2 ((S : Subgroup G) ⊓ L) L := by
    obtain ⟨hs, he⟩ := local_component_sylow_intersection S hRS hL
    exact he.symm ▸ hs
  have hSL' : IsSylowIn 2 (((S : Subgroup G) ⊓ L).subgroupOf E) B := by
    apply (IsSylowIn.map_iff E.subtype E.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le (inf_le_right.trans hLayer),
      map_subgroupOf_eq_of_le hLayer]
    exact hSL
  let Q := (((S : Subgroup G) ⊓ L).subgroupOf E).map π
  have hQ : IsSylowIn 2 Q P := isSylowIn_map hSL' π
  have hQle : Q ≤ ((S : Subgroup G).map
      (QuotientGroup.mk' (solvableRadical G))).subgroupOf J.1 := by
    rintro y ⟨x, hx, rfl⟩
    exact radicalProjection_sylow_mem S J x hx.1
  obtain ⟨K, hK, heK⟩ := J.2.exists_map_quotient_eq (solvableRadical G)
  obtain ⟨U, hU, heU⟩ := radicalProjection_sylow_lift S J hK heK Q hQle
  have hUE : U ≤ E := (hU.trans inf_le_right).trans (le_cComponentLayer hK)
  let D := R ⊓ U
  let V := (D.subgroupOf E).map π
  have hVQ : V ≤ Q := by
    rw [← heU]
    exact map_mono (comap_mono inf_le_right)
  have hi : V.relIndex Q ≤ 2 := by
    rw [← heU]
    exact (map_relIndex_le π (D.subgroupOf E) (U.subgroupOf E)).trans (by
      rw [relIndex_subgroupOf hUE]
      have huS : (S : Subgroup G) ⊓ U = U := inf_eq_right.mpr (hU.trans inf_le_left)
      simpa only [huS] using intersection_relIndex_le_two hidx U)
  have hn := intrinsic_nonsolvable_commutator hP hQ
    (hVQ.trans (isSylowIn_iff.mp hQ).2.1) hi
  refine ⟨K, hK, ?_⟩
  intro hs
  let := hs
  let C := ⁅B, D.subgroupOf E⁆
  have hC : C.map E.subtype ≤ ⁅L, R ⊓ K⁆ := by
    rw [map_commutator, map_subgroupOf_eq_of_le hLayer,
      map_subgroupOf_eq_of_le (inf_le_right.trans hUE)]
    exact commutator_mono le_rfl (inf_le_inf_left R (hU.trans inf_le_right))
  let : Group.IsSolvable (C.map E.subtype) :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hC)
  let : Group.IsSolvable C := Group.isSolvable_of_isSolvable_injective
    (f := (C.equivMapOfInjective E.subtype E.subtype_injective).toMonoidHom)
    (C.equivMapOfInjective E.subtype E.subtype_injective).injective
  have hm : Group.IsSolvable (C.map π) :=
    Group.isSolvable_of_surjective (π.subgroupMap_surjective C)
  rw [map_commutator] at hm
  exact hn hm

end CFSG.Quasithin.Chapter1.Section02.IndexTwo
