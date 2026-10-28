module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.QuasisimpleHigmanSimsPoint

/-!
# The full original V-action on the HS double cover

Transport conjugation through the actual isomorphism from K_v to the HS
cover, retaining its commuting triangle with the central quotient. The
original V acts with the original component-centralizer kernel and has
image of order 32. Its action fixes every element of the order-32 moved
subgroup upstairs, including the entire covering kernel.

The moved subgroup is the full preimage of its order-16 image, which fixes
an actual letter in the degree-100 action. The inner-part calculation in
the simple quotient selects an original element of V whose action on the
full cover is an outer involution. Thus this is a restriction on the full
source action, not only on a subgroup of the simple quotient.

These constructions retain the original V, V_v, K_v and projection. They
do not assert that the resulting local configuration is impossible. The
HS exclusion and the other outstanding source branches remain required.

Source: Aschbacher--Smith, proof of 12.6.12, printed pp.825--826;
GLS3 Proposition 5.2.4(e) for the compatible HS double cover.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {F : Type*} [Group F]

/-- Conjugation on a specified model of the full original residual. -/
@[expose] def nonsingularCoverAction (v : G) (f : Kv v ≃* F) : Gv v →* MulAut F :=
  (MulAut.congr f).toMonoidHom.comp ((Kv v).normalizerMonoidHom.comp
    (inclusion ((normal_subgroupOf_iff_le_normalizer (Kv_le_Gv v)).mp (Kv_normalIn_Gv v))))

omit [Finite G] in
theorem nonsingularCoverAction_apply (v : G) (f : Kv v ≃* F)
    (x : Gv v) (y : Kv v) :
    nonsingularCoverAction v f x (f y) =
      f ((Kv v).normalizerMonoidHom
        (inclusion ((normal_subgroupOf_iff_le_normalizer (Kv_le_Gv v)).mp
          (Kv_normalIn_Gv v)) x) y) := by
  change f (((Kv v).normalizerMonoidHom _) (f.symm (f y))) = _
  rw [f.symm_apply_apply]

omit [Finite G] in
theorem nonsingularCoverAction_ker (v : G) (f : Kv v ≃* F) :
    (nonsingularCoverAction v f).ker =
      (centralizer (Kv v : Set G)).subgroupOf (Gv v) := by
  rw [nonsingularCoverAction,MonoidHom.ker_comp_of_injective _ _ (MulAut.congr f).injective,
    ←MonoidHom.comap_ker,normalizerMonoidHom_ker]
  rfl

omit [Finite G] in
theorem nonsingularCoverAction_projection (v : G)
    {B : Type*} [Group B] (e : ((Kv v) ⧸ center (Kv v)) ≃* B)
    (f : Kv v ≃* F) (q : F →* B)
    (hf : ∀ y, q (f y) = e (QuotientGroup.mk' (center (Kv v)) y))
    (x : Gv v) (y : F) :
    q (nonsingularCoverAction v f x y) = nonsingularModelAction v e x (q y) := by
  obtain ⟨z,rfl⟩ := f.surjective y
  rw [nonsingularCoverAction_apply,hf,hf]
  exact (MulAut.centralQuotientAction_apply e _ z).symm

variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- An outer automorphism is supplied by an element of the original V,
not by an arbitrary automorphism of the simple quotient. -/
theorem SourceHypothesis.nonsingular_hs_exists_original_outer
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier) :
    ∃ x : V, orderOf (nonsingularModelAction (v : G) e (inclusion (V_le_Gv v) x)) = 2 ∧
      nonsingularModelAction (v : G) e (inclusion (V_le_Gv v) x) ∉
        MulAut.innerSubgroup Sporadic.LeechRelated.HS.Carrier := by
  let a := nonsingularModelAction (v : G) e
  let E := (V.subgroupOf (Gv (v : G))).map a
  have hi := H.nonsingular_hs_original_inner_part D v hv hK e
  have hn : ¬ E ≤ MulAut.innerSubgroup Sporadic.LeechRelated.HS.Carrier := by
    intro hh
    have he : E = ((Vv L V (v : G)).subgroupOf (Gv (v : G))).map a :=
      (inf_eq_left.mpr hh).symm.trans hi.2.2.1
    have hc := congrArg (fun U : Subgroup (MulAut Sporadic.LeechRelated.HS.Carrier) => Nat.card U) he
    rw [hi.1,hi.2.1] at hc
    omega
  obtain ⟨y,hy,hn⟩ := SetLike.not_le_iff_exists.mp hn
  obtain ⟨z,hz,rfl⟩ := hy
  let x : V := ⟨z,hz⟩
  refine ⟨x,?_,hn⟩
  apply orderOf_eq_prime
  · change a z ^ 2 = 1
    rw [←map_pow]
    have hz2 : z ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian _ hz)
    rw [hz2,map_one]
  · intro he
    exact hn (he ▸ (MulAut.innerSubgroup Sporadic.LeechRelated.HS.Carrier).one_mem)

/-- The subgroup fixed by the original cover action is the full preimage
of its order-sixteen image, and that image fixes an actual HS letter. -/
theorem SourceHypothesis.nonsingular_hs_cover_moved_geometry
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier)
    [Group.IsPerfect Sporadic.LeechRelated.HS.Carrier]
    (f : Kv (v : G) ≃* Theory.SpecificGroups.J2HSMultipliers.HS.DoubleCover)
    (hf : ∀ y, Theory.SpecificGroups.J2HSMultipliers.HS.projection (f y) =
      e (QuotientGroup.mk' (center (Kv (v : G))) y)) :
    let U := ((Vv L V (v : G)).subgroupOf (Kv (v : G))).map f.toMonoidHom
    let q := Theory.SpecificGroups.J2HSMultipliers.HS.projection
    q.ker ≤ U ∧ (U.map q).comap q = U ∧ Nat.card (U.map q) = 16 ∧
      ∃ p : Fin 100, ∀ y ∈ U, (q y : Equiv.Perm (Fin 100)) p = p := by
  let C := Kv (v : G)
  let W := (Vv L V (v : G)).subgroupOf C
  let U := W.map f.toMonoidHom
  let q := Theory.SpecificGroups.J2HSMultipliers.HS.projection
  have hZ : center C ≤ W := by
    rw [←H.nonsingular_hs_fixed_line_eq_center D v hv hK ⟨e⟩]
    exact comap_mono inf_le_left
  have hk : q.ker ≤ U := by
    intro y hy
    obtain ⟨x,rfl⟩ := f.surjective y
    have hxe : e (QuotientGroup.mk' (center C) x) = 1 := (hf x).symm.trans hy
    have hx : x ∈ center C := by
      apply (QuotientGroup.eq_one_iff x).mp
      exact e.injective (hxe.trans e.map_one.symm)
    exact mem_map_of_mem f.toMonoidHom (hZ hx)
  have hm : U.map q = (W.map (QuotientGroup.mk' (center C))).map e.toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    exact MonoidHom.ext hf
  refine ⟨hk,comap_map_eq_self hk,?_,?_⟩
  · rw [hm,card_map_of_injective e.injective]
    exact H.nonsingular_hs_moved_image_card D v hv ⟨e⟩
  · obtain ⟨p,hp⟩ := H.nonsingular_hs_moved_image_fixed_point D v hv hK e
    refine ⟨p,?_⟩
    rintro y ⟨x,hx,rfl⟩
    change (q (f x) : Equiv.Perm (Fin 100)) p = p
    rw [show q (f x) = e (QuotientGroup.mk' (center C) x) from hf x]
    exact hp x hx


private theorem hs_full_cover_action_base
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier) :
    letI : IsQuasisimple (Kv (v : G)) := hK
    letI : Group.IsPerfect Sporadic.LeechRelated.HS.Carrier :=
      Group.IsPerfect.ofSurjective
        (f := e.toMonoidHom.comp (QuotientGroup.mk' (center (Kv (v : G)))))
        (e.surjective.comp (QuotientGroup.mk'_surjective _))
    ∃ f : Kv (v : G) ≃* Theory.SpecificGroups.J2HSMultipliers.HS.DoubleCover,
      (∀ y, Theory.SpecificGroups.J2HSMultipliers.HS.projection (f y) =
        e (QuotientGroup.mk' (center (Kv (v : G))) y)) ∧
      let U := ((Vv L V (v : G)).subgroupOf (Kv (v : G))).map f.toMonoidHom
      let r := (nonsingularCoverAction (v : G) f).comp (inclusion (V_le_Gv v))
      IsElementaryAbelian 2 U ∧ Nat.card U = 32 ∧
      r.ker = (centralizer (Kv (v : G) : Set G)).subgroupOf V ∧
      Nat.card r.range = 32 ∧
      (∀ (x : V) y, Theory.SpecificGroups.J2HSMultipliers.HS.projection (r x y) =
        nonsingularModelAction (v : G) e (inclusion (V_le_Gv v) x)
          (Theory.SpecificGroups.J2HSMultipliers.HS.projection y)) ∧
      (∀ (x : V) y, y ∈ U → r x y = y) ∧
      ∃ x : V, orderOf (r x) = 2 ∧
        r x ∉ MulAut.innerSubgroup Theory.SpecificGroups.J2HSMultipliers.HS.DoubleCover := by
  let := hK
  let : Group.IsPerfect Sporadic.LeechRelated.HS.Carrier :=
    Group.IsPerfect.ofSurjective
      (f := e.toMonoidHom.comp (QuotientGroup.mk' (center (Kv (v : G)))))
      (e.surjective.comp (QuotientGroup.mk'_surjective _))
  obtain ⟨f,hf⟩ := H.nonsingular_hs_doubleCover D v hv hK e
  let U := ((Vv L V (v : G)).subgroupOf (Kv (v : G))).map f.toMonoidHom
  let r := (nonsingularCoverAction (v : G) f).comp (inclusion (V_le_Gv v))
  have hWC := (H.nonsingular_component_rank D v hv).1
  let := Vv_elementary H.chosen.normalizes (v : G)
  let : IsElementaryAbelian 2 ((Vv L V (v : G)).subgroupOf (Kv (v : G))) :=
    IsElementaryAbelian.subgroupOf hWC
  have hu : Nat.card U = 32 := by
    rw [card_map_of_injective f.injective,
      Nat.card_congr (subgroupOfEquivOfLe hWC).toEquiv]
    exact D.nonsingular_moved_card H.chosen v hv
  have hk : r.ker = (centralizer (Kv (v : G) : Set G)).subgroupOf V := by
    rw [←MonoidHom.comap_ker,nonsingularCoverAction_ker]
    rfl
  have hr : Nat.card r.range = 32 := by
    rw [←index_ker,hk]
    exact (H.nonsingular_original_model_action D v hv hK e).2.1.symm.trans
      (H.nonsingular_hs_original_centralizer D v hv hK e).1
  have hq (x : V) (y) : Theory.SpecificGroups.J2HSMultipliers.HS.projection (r x y) =
      nonsingularModelAction (v : G) e (inclusion (V_le_Gv v) x)
        (Theory.SpecificGroups.J2HSMultipliers.HS.projection y) :=
    nonsingularCoverAction_projection (v : G) e f _ hf _ y
  refine ⟨f,hf,IsElementaryAbelian.map f.toMonoidHom,hu,hk,hr,hq,?_,?_⟩
  · intro x y hy
    obtain ⟨z,hz,rfl⟩ := hy
    change nonsingularCoverAction (v : G) f (inclusion (V_le_Gv v) x) (f z) = f z
    rw [nonsingularCoverAction_apply]
    apply congrArg f
    apply Subtype.ext
    change (x : G) * (z : G) * (x : G)⁻¹ = z
    have hc : (x : G) * (z : G) = (z : G) * (x : G) :=
      setLike_mul_comm x.property (Vv_le_V H.chosen.normalizes _ hz)
    rw [hc,mul_inv_cancel_right]
  · obtain ⟨x,hx,ho⟩ := H.nonsingular_hs_exists_original_outer D v hv hK e
    have houter : r x ∉ MulAut.innerSubgroup Theory.SpecificGroups.J2HSMultipliers.HS.DoubleCover := by
      rintro ⟨z,hz⟩
      apply ho
      refine ⟨Theory.SpecificGroups.J2HSMultipliers.HS.projection z,?_⟩
      ext y
      obtain ⟨w,rfl⟩ := Theory.SpecificGroups.J2HSMultipliers.HS.projection_surjective y
      rw [←hq x w,←hz]
      simp only [MulAut.conj_apply,map_mul,map_inv]
    refine ⟨x,orderOf_eq_prime ?_ ?_,houter⟩
    · have hx2 : x ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian _ x.property)
      rw [←map_pow,hx2,map_one]
    · intro he
      exact houter (he ▸ (MulAut.innerSubgroup _).one_mem)

/-- The original V acts on the full HS cover, with precisely the original
centralizer kernel and the original quotient action. Every moved lift is fixed. -/
theorem SourceHypothesis.nonsingular_hs_full_cover_action
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier) :
    letI : IsQuasisimple (Kv (v : G)) := hK
    letI : Group.IsPerfect Sporadic.LeechRelated.HS.Carrier :=
      Group.IsPerfect.ofSurjective
        (f := e.toMonoidHom.comp (QuotientGroup.mk' (center (Kv (v : G)))))
        (e.surjective.comp (QuotientGroup.mk'_surjective _))
    ∃ f : Kv (v : G) ≃* Theory.SpecificGroups.J2HSMultipliers.HS.DoubleCover,
      (∀ y, Theory.SpecificGroups.J2HSMultipliers.HS.projection (f y) =
        e (QuotientGroup.mk' (center (Kv (v : G))) y)) ∧
      let U := ((Vv L V (v : G)).subgroupOf (Kv (v : G))).map f.toMonoidHom
      let r := (nonsingularCoverAction (v : G) f).comp (inclusion (V_le_Gv v))
      IsElementaryAbelian 2 U ∧ Nat.card U = 32 ∧
      Theory.SpecificGroups.J2HSMultipliers.HS.projection.ker ≤ U ∧
      (U.map Theory.SpecificGroups.J2HSMultipliers.HS.projection).comap
        Theory.SpecificGroups.J2HSMultipliers.HS.projection = U ∧
      Nat.card (U.map Theory.SpecificGroups.J2HSMultipliers.HS.projection) = 16 ∧
      (∃ p : Fin 100, ∀ y ∈ U,
        (Theory.SpecificGroups.J2HSMultipliers.HS.projection y : Equiv.Perm (Fin 100)) p = p) ∧
      IsElementaryAbelian 2 r.range ∧
      r.ker = (centralizer (Kv (v : G) : Set G)).subgroupOf V ∧
      Nat.card r.range = 32 ∧
      (∀ (x : V) y, Theory.SpecificGroups.J2HSMultipliers.HS.projection (r x y) =
        nonsingularModelAction (v : G) e (inclusion (V_le_Gv v) x)
          (Theory.SpecificGroups.J2HSMultipliers.HS.projection y)) ∧
      (∀ (x : V) y, y ∈ U → r x y = y) ∧
      ∃ x : V, orderOf (r x) = 2 ∧
        r x ∉ MulAut.innerSubgroup Theory.SpecificGroups.J2HSMultipliers.HS.DoubleCover := by
  let := hK
  let : Group.IsPerfect Sporadic.LeechRelated.HS.Carrier :=
    Group.IsPerfect.ofSurjective
      (f := e.toMonoidHom.comp (QuotientGroup.mk' (center (Kv (v : G)))))
      (e.surjective.comp (QuotientGroup.mk'_surjective _))
  obtain ⟨f,hf,hu,hcard,hk,hr,hq,hfix,houter⟩ := hs_full_cover_action_base H D v hv hK e
  obtain ⟨hker,hfull,himage,hpoint⟩ := H.nonsingular_hs_cover_moved_geometry D v hv hK e f hf
  let r := (nonsingularCoverAction (v : G) f).comp (inclusion (V_le_Gv v))
  exact ⟨f,hf,hu,hcard,hker,hfull,himage,hpoint,
    IsElementaryAbelian.of_surjective r.rangeRestrict r.rangeRestrict_surjective,
    hk,hr,hq,hfix,houter⟩


end CFSG.Quasithin.Chapter12.Section06
