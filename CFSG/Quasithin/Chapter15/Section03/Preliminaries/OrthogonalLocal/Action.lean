module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.NaturalAction

/-!
# Transport for the natural orthogonal action in Section 15.3

The supplied coordinates make `V` elementary abelian and each supported plane
has order four. Normality then places `V` in the specified Sylow subgroup.
The image of an ambient subgroup is taken through the actual actor of
`NaturalOrthogonalAction`; a full image gives the A.5 product factorization.
No abstract group-family identification replaces the conjugation action.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.2(1)
and the plane decomposition preceding 15.3.5, printed pp.1121–1122.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03
open Subgroup
open scoped IsMulCommutative
variable {G : Type*} [Group G]

/-- The image in the specified natural orthogonal action. -/
def NaturalOrthogonalAction.image {M V : Subgroup G}
    (d : NaturalOrthogonalAction M V) (X : Subgroup G) : Subgroup OrthogonalActor :=
  (X.subgroupOf M).map d.actor

theorem NaturalOrthogonalAction.image_self {M V : Subgroup G}
    (d : NaturalOrthogonalAction M V) : d.image M = ⊤ := by
  simp only [image, subgroupOf_self, map_top_of_surjective _ d.onto]

theorem NaturalOrthogonalAction.image_eq_bot_iff {M V X : Subgroup G}
    (d : NaturalOrthogonalAction M V) (hXM : X ≤ M) :
    d.image X = ⊥ ↔ X ≤ centralizer (V : Set G) := by
  rw [image, Subgroup.map_eq_bot_iff, d.ker_actor]
  exact ⟨fun h x hx => h (show (⟨x, hXM hx⟩ : M) ∈ X.subgroupOf M from hx),
    fun h _ hx => h hx⟩

theorem NaturalOrthogonalAction.elementary {M V : Subgroup G}
    (d : NaturalOrthogonalAction M V) : IsElementaryAbelian 2 V where
  toIsMulCommutative := ⟨⟨fun a b => d.coordinates.injective (by simp only [map_mul, mul_comm])⟩⟩
  exponent_dvd_p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro v
    apply d.coordinates.injective
    rw [map_pow, map_one]
    have h : ∀ w : OrthogonalVector, w ^ 2 = 1 := by decide +kernel
    exact h _

theorem NaturalOrthogonalAction.plane_le {M V : Subgroup G}
    (d : NaturalOrthogonalAction M V) (i : OrthogonalPlaneIndex) : d.plane i ≤ V :=
  map_subtype_le _

/-- Each supported coordinate plane has four elements. -/
theorem orthogonalCoordinatePlane_card (i : OrthogonalPlaneIndex) :
    Nat.card (orthogonalCoordinatePlane i) = 4 := by
  let e : orthogonalCoordinatePlane i ≃ OrthogonalPlaneVector := {
    toFun := fun v => v.val i
    invFun := fun w => ⟨fun j => if j = i then w else 1, by
      intro j hj; exact if_neg hj⟩
    left_inv := fun v => by
      apply Subtype.ext
      funext j
      by_cases hj : j = i
      · simp [hj]
      · simp [hj, v.property j hj]
    right_inv := fun w => if_pos rfl }
  rw [Nat.card_congr e]
  norm_num [OrthogonalPlaneVector, Nat.card_eq_fintype_card]

theorem NaturalOrthogonalAction.card_plane {M V : Subgroup G}
    (d : NaturalOrthogonalAction M V) (i : OrthogonalPlaneIndex) :
    Nat.card (d.plane i) = 4 := by
  rw [plane, card_map_of_injective V.subtype_injective]
  let e : ((orthogonalCoordinatePlane i).comap d.coordinates.toMonoidHom) ≃
      orthogonalCoordinatePlane i :=
    Equiv.subtypeEquiv d.coordinates.toEquiv (fun _ => Iff.rfl)
  exact (Nat.card_congr e).trans (orthogonalCoordinatePlane_card i)

theorem centralInvolutions_le_sylow (T : Sylow 2 G) :
    centralInvolutions T ≤ (T : Subgroup G) := map_subtype_le _

theorem centralInvolutions_le_centralizer_sylow (T : Sylow 2 G) :
    centralInvolutions T ≤ centralizer (T : Set G) := by
  rintro z ⟨z₀, ⟨z₁, hz₁, rfl⟩, rfl⟩ t ht
  exact congrArg Subtype.val ((mem_center_iff.mp z₁.property) ⟨t, ht⟩)

theorem localModule_le (T : Sylow 2 G) {M : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M) : localModule T M ≤ M :=
  conjugateSpanBy_le_self ((centralInvolutions_le_sylow T).trans hTM)

/-- A normal elementary module in `M` lies in its specified Sylow subgroup. -/
theorem NaturalOrthogonalAction.le_sylow [Finite G] {M V : Subgroup G}
    (d : NaturalOrthogonalAction M V) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (hVM : V ≤ M) : V ≤ (T : Subgroup G) := by
  let _ := d.elementary
  let _ : (V.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer d.normalizes
  have hVtwo : IsPGroup 2 (V.subgroupOf M) :=
    (IsElementaryAbelian.isPGroup 2 V).comap_subtype
  have h := hVtwo.le_sylow_of_normal (T.subtype hTM)
  intro v hv
  exact h (show (⟨v, hVM hv⟩ : M) ∈ V.subgroupOf M from hv)

/-- Full action image is precisely the product factorization used by A.5.7(1). -/
theorem NaturalOrthogonalAction.orderingLE_of_image_eq_top
    (T : Sylow 2 G) {M X : Subgroup G}
    (d : NaturalOrthogonalAction M (localModule T M))
    (himage : d.image X = ⊤) : ChapterA.Section05To06.OrderingLE T M X := by
  intro m hm
  have hmem : d.actor ⟨m, hm⟩ ∈ d.image X := himage ▸ mem_top _
  obtain ⟨x, hx, he⟩ := hmem
  refine ⟨x, ⟨x.property, hx⟩, (x : G)⁻¹ * m, ⟨M.mul_mem (M.inv_mem x.property) hm, ?_⟩,
    mul_inv_cancel_left _ _⟩
  have hker : x⁻¹ * ⟨m, hm⟩ ∈ d.actor.ker := by
    change d.actor (x⁻¹ * ⟨m, hm⟩) = 1
    rw [map_mul, map_inv, he, inv_mul_cancel]
  rw [d.ker_actor] at hker
  exact hker

/-- Every subgroup of the coordinate module is elementary abelian. -/
theorem NaturalOrthogonalAction.elementary_of_le {M V H : Subgroup G}
    (d : NaturalOrthogonalAction M V) (hHV : H ≤ V) : IsElementaryAbelian 2 H where
  toIsMulCommutative := by
    let _ := d.elementary
    exact ⟨⟨fun a b => Subtype.ext (congrArg (fun v : V => (v : G))
      (mul_comm (⟨a, hHV a.property⟩ : V) ⟨b, hHV b.property⟩))⟩⟩
  exponent_dvd_p := by
    let _ := d.elementary
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro h
    exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) (h : G) (hHV h.property))

/-- The entire module lies in each plane stabilizer in the Sylow group. -/
theorem NaturalOrthogonalAction.le_planeStabilizer [Finite G] {M V : Subgroup G}
    (d : NaturalOrthogonalAction M V) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (hVM : V ≤ M) (i : OrthogonalPlaneIndex) :
    V ≤ planeStabilizer T (d.plane i) := by
  let _ := d.elementary
  have hVV : V ≤ centralizer (V : Set G) := by
    intro v hv w hw
    exact congrArg Subtype.val (mul_comm (⟨w, hw⟩ : V) ⟨v, hv⟩)
  exact le_inf (d.le_sylow T hTM hVM)
    ((hVV.trans (centralizer_le (d.plane_le i))).trans (Subgroup.centralizer_le_normalizer _))

/-- Elementary abelianness of the fixed plane required in 15.3.8. -/
theorem NaturalOrthogonalAction.elementary_fixedPlane {M V : Subgroup G}
    (d : NaturalOrthogonalAction M V) (S : Subgroup G) :
    IsElementaryAbelian 2 (fixedPlane V S) := d.elementary_of_le inf_le_left

/-- Containment of the fixed plane in `S`, independently of its order calculation. -/
theorem NaturalOrthogonalAction.fixedPlane_le_stabilizer [Finite G] {M V : Subgroup G}
    (d : NaturalOrthogonalAction M V) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (hVM : V ≤ M) (i : OrthogonalPlaneIndex) :
    fixedPlane V (planeStabilizer T (d.plane i)) ≤ planeStabilizer T (d.plane i) :=
  inf_le_left.trans (d.le_planeStabilizer T hTM hVM i)

end CFSG.Quasithin.Chapter15.Section03
end
