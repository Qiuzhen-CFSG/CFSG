module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.FusionControl
public import Theory.SpecificGroups.Triality.ShortRootCentralizer.BinaryNonsplit
public import Theory.ElementaryAbelian.Injective

/-!
# The original local short-root centralizer and its nonsplitting plane

Pull the native highest short root back through the original right endpoint
isomorphism. Both commuting squares identify the original T with the positive
Sylow. The native centralizer containment at q = 2 therefore identifies the
whole native short centralizer with this actual local centralizer and gives
its exact Sylow intersection. Transport the normal elementary four-group;
it lies in the derived subgroup of the local centralizer's two-core.

These are local inputs to Aschbacher--Smith F.4.40--42, printed pp.294--295,
applied in 14.2.18--19 and 14.3.15, printed pp.987,994. The original ambient
centralizer containment and recognition remain open. The marked inclusion
amalgam remains the explicit earlier input, with both endpoint maps intact.
The literal component application is TerminalSolvable/EightBorelShortCentralizer.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
open _root_.Triality.Standard.RadicalCoordinates
open _root_.Triality.Standard.RadicalCoordinates.LeviCommutators
open _root_.Triality.Standard.ShortRootCentralizer
local notation "P" => binaryParameters 1 Nat.zero_lt_one
local notation "hp2" => binaryParameters_prime 1 Nat.zero_lt_one
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H : Subgroup G}

/-- The second endpoint identifies the literal original Sylow, in both directions. -/
theorem marked_second_sylow_iff (r : MarkedTriality T M Mc H)
    (hTH : (T : Subgroup G) ≤ H) (x : secondParabolic T M Mc H) :
    (r.right x).val ∈ unipotent P ↔ (x : G) ∈ (T : Subgroup G) := by
  have hTP : (T : Subgroup G) ≤ secondParabolic T M Mc H :=
    le_sup_right.trans le_sup_left
  constructor
  · intro hx
    obtain ⟨y,hy,he⟩ := marked_sylow_lift r hTH (r.right x).val hx
    have hyx : (⟨y,hTP hy⟩ : secondParabolic T M Mc H) = x := by
      apply r.right.injective
      apply Subtype.ext
      exact (marked_endpoint_value r ⟨y.property,hTP hy⟩).symm.trans he
    exact (congrArg Subtype.val hyx) ▸ hy
  · intro hx
    rw [←marked_endpoint_value r ⟨hTH hx,x.property⟩]
    exact marked_sylow_image r hTH hx

/-- The pinned short-root element in the original second endpoint. -/
def markedShortRoot (r : MarkedTriality T M Mc H) (a : ExtensionField P) :
    secondParabolic T M Mc H := r.right.symm
      ⟨short P hp2 2 a,radical_le_parabolic P .central
        (descendedRootSubgroup_le_radical P hp2 .central
          (short_mem P hp2 .central 2 trivial a))⟩

omit [Finite G] in
theorem markedShortRoot_image (r : MarkedTriality T M Mc H) (a : ExtensionField P) :
    (r.right (markedShortRoot r a)).val = short P hp2 2 a := by
  exact congrArg Subtype.val (r.right.apply_symm_apply _)

theorem markedShortRoot_mem_sylow (r : MarkedTriality T M Mc H)
    (hTH : (T : Subgroup G) ≤ H) (a : ExtensionField P) :
    (markedShortRoot r a : G) ∈ (T : Subgroup G) := by
  apply (marked_second_sylow_iff r hTH _).mp
  rw [markedShortRoot_image]
  exact descendSubgroup_mono P
    (RadicalCoordinates.rootSubgroup_le_positiveSubgroup P hp2 .central)
    (short_mem P hp2 .central 2 trivial a)

omit [Finite G] in
theorem markedShortRoot_order (r : MarkedTriality T M Mc H)
    (a : ExtensionField P) (ha : a ≠ 0) :
    orderOf (markedShortRoot r a : G) = 2 := by
  rw [Subgroup.orderOf_coe,←r.right.orderOf_eq,←Subgroup.orderOf_coe,markedShortRoot_image]
  exact short_order P hp2 a ha

/-- The local centralizer maps onto the full native centralizer, not just
its intersection with a model endpoint. -/
def markedShortCentralizerEquiv (r : MarkedTriality T M Mc H)
    (a : ExtensionField P) (ha : a ≠ 0) :
    centralizer ({markedShortRoot r a} : Set (secondParabolic T M Mc H)) ≃*
      centralizer ({short P hp2 2 a} : Set (Carrier P)) := by
  let C := centralizer ({markedShortRoot r a} : Set (secondParabolic T M Mc H))
  let f : C →* centralizer ({short P hp2 2 a} : Set (Carrier P)) :=
    ((parabolic P .central).subtype.comp (r.right.toMonoidHom.comp C.subtype)).codRestrict _
      (fun x => by
        apply mem_centralizer_singleton_iff.mpr
        change (r.right x.val).val * short P hp2 2 a = short P hp2 2 a * (r.right x.val).val
        have h := congrArg (fun y : secondParabolic T M Mc H => (r.right y).val)
          (mem_centralizer_singleton_iff.mp x.property)
        simpa only [MonoidHom.comp_apply,map_mul,Subgroup.coe_mul,markedShortRoot_image] using h)
  apply MulEquiv.ofBijective f
  constructor
  · intro x y h
    apply Subtype.ext
    apply r.right.injective
    exact Subtype.ext (congrArg (fun z : centralizer ({short P hp2 2 a} : Set (Carrier P)) => z.val) h)
  · intro y
    let u : parabolic P .central := ⟨y,centralizer_le_central_two a ha y.property⟩
    have hc : r.right.symm u ∈ C := by
      apply mem_centralizer_singleton_iff.mpr
      apply r.right.injective
      apply Subtype.ext
      simp only [map_mul,Subgroup.coe_mul,r.right.apply_symm_apply,markedShortRoot_image]
      exact mem_centralizer_singleton_iff.mp y.property
    refine ⟨⟨r.right.symm u,hc⟩,?_⟩
    apply Subtype.ext
    change (r.right (r.right.symm u)).val = y.val
    exact congrArg Subtype.val (r.right.apply_symm_apply u)

omit [Finite G] in
theorem markedShortCentralizerEquiv_val (r : MarkedTriality T M Mc H)
    (a : ExtensionField P) (ha : a ≠ 0)
    (x : centralizer ({markedShortRoot r a} : Set (secondParabolic T M Mc H))) :
    (markedShortCentralizerEquiv r a ha x).val = (r.right x.val).val := rfl

/-- The intersection with the original T is Sylow in the actual local
short centralizer. Ambient extremality is a separate source obligation. -/
theorem marked_short_local_sylow (r : MarkedTriality T M Mc H)
    (hTH : (T : Subgroup G) ≤ H) (a : ExtensionField P) (ha : a ≠ 0) :
    let C := centralizer ({markedShortRoot r a} : Set (secondParabolic T M Mc H))
    ∃ S : Sylow 2 C, (S : Subgroup C) =
      ((T : Subgroup G).subgroupOf (secondParabolic T M Mc H)).subgroupOf C := by
  let C := centralizer ({markedShortRoot r a} : Set (secondParabolic T M Mc H))
  let e := markedShortCentralizerEquiv r a ha
  obtain ⟨R,hR⟩ := centralizer_sylow_two a ha
  let S := R.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  refine ⟨S,?_⟩
  change (R : Subgroup _).map e.symm.toMonoidHom = _
  rw [hR]
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    apply (marked_second_sylow_iff r hTH _).mp
    have he := markedShortCentralizerEquiv_val r a ha (e.symm y)
    change (e (e.symm y)).val = _ at he
    rw [e.apply_symm_apply] at he
    exact he ▸ hy
  · intro hx
    refine ⟨e x,?_,e.symm_apply_apply x⟩
    change (e x).val ∈ unipotent P
    rw [markedShortCentralizerEquiv_val]
    exact (marked_second_sylow_iff r hTH _).mpr hx

/-- The actual plane in the original local short centralizer, under its
literal endpoint equivalence with the native full centralizer. -/
def markedShortPlane (r : MarkedTriality T M Mc H)
    (a : ExtensionField P) (ha : a ≠ 0) :
    Subgroup (centralizer ({markedShortRoot r a} : Set (secondParabolic T M Mc H))) :=
    ((plane P).subgroupOf (centralizer ({short P hp2 2 a} : Set (Carrier P)))).comap
      (markedShortCentralizerEquiv r a ha).toMonoidHom

omit [Finite G] in
/-- The normal elementary four-group used in F.4.42 lies in the derived
subgroup of the actual local centralizer's two-core. -/
theorem marked_short_plane_structure (r : MarkedTriality T M Mc H)
    (a : ExtensionField P) (ha : a ≠ 0) :
    let C := centralizer ({markedShortRoot r a} : Set (secondParabolic T M Mc H))
    let V := markedShortPlane r a ha
    V.Normal ∧ IsElementaryAbelian 2 V ∧ Nat.card V = 4 ∧ V ≤ ⁅pCore 2 C,pCore 2 C⁆ := by
  let C := centralizer ({markedShortRoot r a} : Set (secondParabolic T M Mc H))
  let D := centralizer ({short P hp2 2 a} : Set (Carrier P))
  let W := (plane P).subgroupOf D
  let e := markedShortCentralizerEquiv r a ha
  let V := markedShortPlane r a ha
  have hWD : plane P ≤ D := plane_le_centralizer P hp2 a
  let : W.Normal := normal_subgroupOf_of_le_normalizer
    ((centralizer_le_central_two a ha).trans (plane_normalized P))
  let : IsElementaryAbelian 2 (plane P) := plane_elementary P hp2
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hWD
  have hmap : V.map e.toMonoidHom = W := map_comap_eq_self_of_surjective e.surjective W
  change V.Normal ∧ IsElementaryAbelian 2 V ∧ Nat.card V = 4 ∧ V ≤ ⁅pCore 2 C,pCore 2 C⁆
  refine ⟨Subgroup.Normal.comap (inferInstanceAs W.Normal) e.toMonoidHom,
    IsElementaryAbelian.comap_of_injective e.toMonoidHom e.injective W,?_,?_⟩
  · have hcard : Nat.card W = 4 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hWD).toEquiv,plane_card P hp2]
      norm_num [Parameters.q,binaryParameters]
    have heq : Nat.card V = Nat.card W := by
      rw [←card_map_of_injective (K := V) (f := e.toMonoidHom) e.injective,hmap]
    exact heq.trans hcard
  · apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rw [hmap,map_commutator,pCore_map_iso]
    exact plane_le_shortCentralizer_core_commutator a ha

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
