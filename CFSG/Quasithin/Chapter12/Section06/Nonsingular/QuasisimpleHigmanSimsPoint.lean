module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.CanonicalRank
public import Theory.SpecificGroups.J2HSMultipliers.HSDoubleCover.ElementaryPoint

/-!
# The original moved subgroup in the HS double cover

For a nonsingular point with quasisimple residual and an actual HS central
quotient, the original order-32 moved subgroup contains the full covering
center. Hence it is the full preimage of its order-16 image. The compatible
double-cover equivalence and its literal projection show that this image
fixes a common letter in the original degree-100 HS action.

This supplies an actual point stabilizer containing the source subgroup,
without replacing its covering kernel or changing the chosen point. It is
a local step toward the HS exclusion; that exclusion is not asserted here.

Source: Aschbacher--Smith, proof of 12.6.12, printed pp.825--826, with the
HS central-quotient row retained by the preceding source reduction.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original moved subgroup is the full preimage of its image in HS;
no additional covering kernel has been discarded. -/
theorem SourceHypothesis.nonsingular_hs_moved_full_preimage
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier) :
    let C := Kv (v : G)
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (center C))
    let W := (Vv L V (v : G)).subgroupOf C
    (W.map f).comap f = W := by
  let C := Kv (v : G)
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center C))
  let W := (Vv L V (v : G)).subgroupOf C
  have hk : f.ker = center C := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hZ : center C ≤ W := by
    rw [←H.nonsingular_hs_fixed_line_eq_center D v hv hK ⟨e⟩]
    exact comap_mono inf_le_left
  change (W.map f).comap f = W
  rw [comap_map_eq,hk,sup_eq_left.mpr hZ]

/-- The actual order-sixteen image of V_v has a common fixed point in the
original HS action. The compatible double-cover map supplies every lift. -/
theorem SourceHypothesis.nonsingular_hs_moved_image_fixed_point
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier) :
    ∃ p : Fin 100, ∀ x : Kv (v : G), (x : G) ∈ Vv L V (v : G) →
      (e (QuotientGroup.mk' (center (Kv (v : G))) x) : Equiv.Perm (Fin 100)) p = p := by
  let := hK
  let : Group.IsPerfect Sporadic.LeechRelated.HS.Carrier :=
    Group.IsPerfect.ofSurjective
      (f := e.toMonoidHom.comp (QuotientGroup.mk' (center (Kv (v : G)))))
      (e.surjective.comp (QuotientGroup.mk'_surjective _))
  obtain ⟨f,hf⟩ := H.nonsingular_hs_doubleCover D v hv hK e
  let C := Kv (v : G)
  let W := (Vv L V (v : G)).subgroupOf C
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center C))
  let U := W.map f.toMonoidHom
  let := Vv_elementary H.chosen.normalizes (v : G)
  let : IsElementaryAbelian 2 W :=
    IsElementaryAbelian.subgroupOf (H.nonsingular_component_rank D v hv).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map f.toMonoidHom
  have hm : U.map Theory.SpecificGroups.J2HSMultipliers.HS.projection = W.map q := by
    rw [map_map]
    congr 1
    exact MonoidHom.ext hf
  have hc : Nat.card (U.map Theory.SpecificGroups.J2HSMultipliers.HS.projection) = 16 := by
    rw [hm,←map_map,card_map_of_injective e.injective]
    exact H.nonsingular_hs_moved_image_card D v hv ⟨e⟩
  obtain ⟨p,hp⟩ := Theory.SpecificGroups.J2HSMultipliers.HS.elementary_projection_common_fixed_point
    U (by omega)
  refine ⟨p,?_⟩
  intro x hx
  have hh := hp (f x) (mem_map_of_mem f.toMonoidHom hx)
  rwa [hf] at hh

end CFSG.Quasithin.Chapter12.Section06
