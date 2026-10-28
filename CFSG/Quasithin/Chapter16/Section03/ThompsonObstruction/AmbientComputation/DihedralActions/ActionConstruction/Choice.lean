module

public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.AmbientComputation.DihedralActions.Rotations
public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.AmbientComputation.DihedralActions.ActionData
public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.AmbientComputation.DihedralActions.Products
public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.Geometry
public import Theory.GroupTheory.CyclicIndexTwoInvolutionAction
public import Theory.GroupTheory.DihedralPresentation
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# Choosing rotations and the maximizing source involution

The actual dihedral or semidihedral model supplies characteristic rotations of
index two. The two candidates `u` and `t*u` give a maximum for the order of their
fixed subgroup. Sylow normalization preserves these rotations.

The elementary four-centralizer of `t` excludes commuting with the rotation
generator. Index two then places the original central involution `z` in the
rotations, where uniqueness identifies it with the half-turn. The intrinsic
index-two involution-action theorem and presentation recognition give the exact
reflection action and model. The same four-centralizer identifies the ambient
center with `zpowers z`.

This constructs the shared input for the maximizing-action and dihedral-factor
calculations in the proof of 16.3.12. Source: Aschbacher--Smith, combined
manuscript of 1 March 2004, printed pp.1181--1182 / PDF pp.1198--1199.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.ThompsonObstruction.AmbientComputation.ActionConstruction
open Subgroup
variable {G : Type*} [Group G] {T : Sylow 2 G} {z t : G} {L : Subgroup G}

/-- The chosen source generator and the candidate maximizing its fixed subgroup. -/
structure RotationChoice (d : Prepared T z t L) where
  y : G
  exponent : ℕ
  exponent_ge : 2 ≤ exponent
  order : orderOf y = 2 ^ exponent
  rotation_le : zpowers y ≤ commutingSylow T L
  characteristic : ((zpowers y).subgroupOf (commutingSylow T L)).Characteristic
  index : (zpowers y).relIndex (commutingSylow T L) = 2
  generation : zpowers y ⊔ zpowers t = commutingSylow T L
  w : G
  candidate : w = d.marked.u ∨ w = t * d.marked.u
  maximizing : ∀ x : G, x = d.marked.u ∨ x = t * d.marked.u →
    Nat.card ↥(zpowers y ⊓ involutionCentralizer x) ≤
      Nat.card ↥(zpowers y ⊓ involutionCentralizer w)

/-- Choose the characteristic rotations and maximize over the two genuine candidates. -/
theorem exists_rotationChoice (d : Prepared T z t L) : Nonempty (RotationChoice d) := by
  obtain ⟨y, hY, hc, hi, n, hn, ho⟩ := exists_characteristic_index_two_generator d
  obtain ⟨w, hw, hmax⟩ := exists_maximizing_candidate d (zpowers y)
  exact ⟨⟨y, n, hn, ho, hY, hc, hi, rotation_sup_reflection d hY hi ⟨n, hn, ho⟩,
    w, hw, hmax⟩⟩

variable (d : Prepared T z t L) (a : RotationChoice d)

theorem RotationChoice.reflection_outside : t ∉ zpowers a.y :=
  reflection_not_mem_rotation d a.rotation_le ⟨a.exponent, a.exponent_ge, a.order⟩

theorem RotationChoice.sylow_normalizes :
    (T : Subgroup G) ≤ normalizer (zpowers a.y : Set G) := by
  let := a.characteristic
  have h := normalizer_le_normalizer_characteristic_image (commutingSylow T L)
    ((zpowers a.y).subgroupOf (commutingSylow T L))
  rw [map_subgroupOf_eq_of_le a.rotation_le] at h
  exact (sylow_normalizes_commutingSylow d).trans h

theorem RotationChoice.candidate_normalizes {x : G}
    (hx : x = d.marked.u ∨ x = t * d.marked.u) :
    x ∈ normalizer (zpowers a.y : Set G) :=
  a.sylow_normalizes d (candidate_mem_and_centralizes d hx).1

theorem RotationChoice.involution : orderOf a.w = 2 := candidate_order d a.candidate

theorem RotationChoice.commutes_reflection : Commute a.w t :=
  candidate_commutes_reflection d a.candidate

variable [Finite G]

private theorem generator_not_commute : ¬ Commute a.y t := by
  intro hc
  let := (EnlargementSieve.four_group d.counterexample).1
  have hym : a.y ∈ zpowers z ⊔ zpowers t := d.shape.centralizer_eq ▸
    ⟨a.rotation_le (mem_zpowers _), mem_centralizer_singleton_iff.mpr hc⟩
  have ho := orderOf_le_of_pow_eq_one (by decide : 0 < 2)
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) a.y hym)
  have hfour : 4 ≤ orderOf a.y := a.order ▸
    Nat.pow_le_pow_right (by decide : 0 < 2) a.exponent_ge
  omega

private theorem mem_rotation_of_commutes_generator {x : G}
    (hxC : x ∈ commutingSylow T L) (hyx : Commute a.y x) : x ∈ zpowers a.y := by
  by_contra hx
  have htx : t * x ∈ zpowers a.y :=
    (mul_mem_iff_of_index_two (show
      ((zpowers a.y).subgroupOf (commutingSylow T L)).index = 2 from a.index)
      (a := ⟨t, d.counterexample.mem_commutingSylow⟩) (b := ⟨x, hxC⟩)).mpr
        ⟨fun h => (a.reflection_outside d h).elim, fun h => (hx h).elim⟩
  have hytx : Commute a.y (t * x) := by
    obtain ⟨k, hk⟩ := htx
    rw [← hk]
    exact Commute.self_zpow _ _
  have hyt : Commute a.y t := by
    have h := hytx.mul_right hyx.inv_right
    simpa only [mul_inv_cancel_right] using h
  exact generator_not_commute d a hyt

/-- The original central involution lies in the actual rotations. -/
theorem RotationChoice.z_mem : z ∈ zpowers a.y :=
  mem_rotation_of_commutes_generator d a
    ⟨d.counterexample.localSetup.mem_sylow,
      d.counterexample.localSetup.involution_mem_componentCentralizer⟩
    (mem_centralizer_singleton_iff.mp
      (d.counterexample.localSetup.sylow_centralizes (a.rotation_le (mem_zpowers _)).1))

/-- The half-turn is the given ambient central involution. -/
theorem RotationChoice.halfTurn : a.y ^ (2 ^ (a.exponent - 1)) = z := by
  have hs : 2 ^ a.exponent = 2 ^ (a.exponent - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    have := a.exponent_ge
    omega
  have ho : orderOf (a.y ^ (2 ^ (a.exponent - 1))) = 2 := by
    rw [orderOf_pow_of_dvd (by positivity) (by rw [a.order, hs]; exact dvd_mul_right _ _),
      a.order, hs, Nat.mul_div_right _ (by positivity)]
  exact congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two
    (x := (⟨a.y ^ (2 ^ (a.exponent - 1)), pow_mem (mem_zpowers _) _⟩ : zpowers a.y))
    (y := (⟨z, a.z_mem d⟩ : zpowers a.y))
    ((orderOf_coe _).symm.trans ho)
    ((orderOf_coe _).symm.trans d.counterexample.localSetup.involution))


/-- The source reflection action, with the model determined by its actual presentation. -/
theorem RotationChoice.reflection_action :
    ((∃ n : ℕ, 2 ≤ n ∧ Nonempty (commutingSylow T L ≃* DihedralGroup (2 ^ n))) ∧
      t⁻¹ * a.y * t = a.y⁻¹) ∨
    ((∃ (n : ℕ) (hn : 4 ≤ n),
      Nonempty (commutingSylow T L ≃* Semidihedral.StandardModel n hn)) ∧
      t⁻¹ * a.y * t = a.y⁻¹ * z) := by
  let C := commutingSylow T L
  let yc : C := ⟨a.y, a.rotation_le (mem_zpowers _)⟩
  let tc : C := ⟨t, d.counterexample.mem_commutingSylow⟩
  have hY : zpowers yc = (zpowers a.y).subgroupOf C := by
    apply map_injective C.subtype_injective
    rw [MonoidHom.map_zpowers, map_subgroupOf_eq_of_le a.rotation_le]
    rfl
  have hyo : orderOf yc = 2 ^ a.exponent := (orderOf_coe yc).symm.trans a.order
  have hto : orderOf tc = 2 := (orderOf_coe tc).symm.trans d.counterexample.involution
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by
    simpa only [pow_two, d.counterexample.involution] using pow_orderOf_eq_one t)
  have hCmap : (centralizer ({tc} : Set C)).map C.subtype = C ⊓ involutionCentralizer t := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v.property, mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hv))⟩
    · rintro ⟨hx, hc⟩
      refine ⟨⟨x, hx⟩, mem_centralizer_singleton_iff.mpr ?_, rfl⟩
      exact Subtype.ext (mem_centralizer_singleton_iff.mp hc)
  have hCcard : Nat.card (centralizer ({tc} : Set C)) = 4 := by
    rw [Nat.card_congr ((centralizer ({tc} : Set C)).equivMapOfInjective
      C.subtype C.subtype_injective).toEquiv, hCmap, d.shape.centralizer_eq]
    exact (EnlargementSieve.four_group d.counterexample).2
  have hgen : closure ({yc, tc} : Set C) = ⊤ := by
    apply map_injective C.subtype_injective
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, C.range_subtype]
    rw [Set.image_insert_eq, Set.image_singleton]
    change closure ({a.y, t} : Set G) = C
    rw [← Set.singleton_union, Subgroup.closure_union, ← zpowers_eq_closure,
      ← zpowers_eq_closure]
    exact a.generation
  have hcard : Nat.card C = 2 * 2 ^ a.exponent := by
    have h := ((zpowers a.y).subgroupOf C).index_mul_card
    rw [show ((zpowers a.y).subgroupOf C).index = 2 from a.index,
      Nat.card_congr (subgroupOfEquivOfLe a.rotation_le).toEquiv,
      Nat.card_zpowers, a.order] at h
    exact h.symm
  rcases involution_conj_eq_inv_or_semidihedral_of_zpowers_index_two yc tc a.exponent
    hyo (hY.symm ▸ a.index) (by rw [hY]; exact a.reflection_outside d) hto hCcard
      with hinv | ⟨hn, hsemi⟩
  · refine Or.inl ⟨⟨a.exponent, a.exponent_ge, ?_⟩, ?_⟩
    · exact dihedralGroup_equiv_of_presentation (by positivity) yc tc hyo
        (hto ▸ pow_orderOf_eq_one tc) hinv hgen hcard
    · simpa only [coe_mul, coe_inv, yc, tc, hti] using congrArg Subtype.val hinv
  · have hn' : 4 ≤ a.exponent + 1 := by omega
    refine Or.inr ⟨⟨a.exponent + 1, hn', ?_⟩, ?_⟩
    · apply Semidihedral.standardModel_equiv_of_presentation hn' yc tc
        (by simpa using hyo) hto (by simpa using hsemi) hgen
      simpa only [pow_succ, Nat.mul_comm] using hcard
    · have he : t⁻¹ * a.y * t = a.y ^ (2 ^ (a.exponent - 1) - 1) := by
        simpa only [coe_mul, coe_inv, coe_pow, yc, tc, hti] using congrArg Subtype.val hsemi
      calc
        _ = a.y ^ (2 ^ (a.exponent - 1) - 1) := he
        _ = a.y⁻¹ * a.y ^ (2 ^ (a.exponent - 1)) := by
          apply mul_left_cancel (a := a.y)
          rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_pow _ _ (by decide : 0 < 2)),
            mul_inv_cancel_left]
        _ = a.y⁻¹ * z := congrArg (a.y⁻¹ * ·) (a.halfTurn d)


omit [Finite G] in
/-- Multiplication by t interchanges the two source candidates. -/
theorem RotationChoice.other_candidate :
    t * a.w = d.marked.u ∨ t * a.w = t * d.marked.u := by
  rcases a.candidate with hw | hw
  · exact Or.inr (congrArg (t * ·) hw)
  · left
    rw [hw, ← mul_assoc, ← pow_two,
      ← d.counterexample.involution, pow_orderOf_eq_one, one_mul]

omit [Finite G] in
/-- Fixing the cyclic generator suffices because both candidates also fix t. -/
theorem RotationChoice.centralizes_of_fixes
    (h : a.w⁻¹ * a.y * a.w = a.y) :
    a.w ∈ centralizer (commutingSylow T L : Set G) := by
  have hcomm : Commute a.y a.w := by
    change a.y * a.w = a.w * a.y
    have he := congrArg (fun x => a.w * x) h
    simpa only [← mul_assoc, mul_inv_cancel, one_mul] using he
  have hle : commutingSylow T L ≤ centralizer ({a.w} : Set G) := by
    rw [← a.generation]
    exact sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hcomm))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (a.commutes_reflection d).symm))
  intro x hx
  exact mem_centralizer_singleton_iff.mp (hle hx)


include d a in
/-- The center is identified with the original ambient involution, not just an abstract C₂. -/
theorem RotationChoice.center_eq : ambientCenter (commutingSylow T L) = zpowers z := by
  apply le_antisymm
  · rintro x ⟨v, hv, rfl⟩
    change (v : G) ∈ zpowers z
    have hvm : (v : G) ∈ zpowers a.y := mem_rotation_of_commutes_generator d a v.property
      (congrArg Subtype.val (mem_center_iff.mp hv ⟨a.y, a.rotation_le (mem_zpowers _)⟩))
    have hvt : (v : G) ∈ involutionCentralizer t := mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_center_iff.mp hv ⟨t, d.counterexample.mem_commutingSylow⟩)).symm
    let := (EnlargementSieve.four_group d.counterexample).1
    have hvE : (v : G) ∈ zpowers z ⊔ zpowers t :=
      d.shape.centralizer_eq ▸ ⟨v.property, hvt⟩
    have hd := orderOf_dvd_of_pow_eq_one
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) (v : G) hvE)
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · rw [orderOf_eq_one_iff.mp h1]
      exact one_mem _
    · have he : (v : G) = z := congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two
        (x := (⟨v, hvm⟩ : zpowers a.y)) (y := (⟨z, a.z_mem d⟩ : zpowers a.y))
        ((orderOf_coe _).symm.trans h2)
        ((orderOf_coe _).symm.trans d.counterexample.localSetup.involution))
      exact he ▸ mem_zpowers z
  · apply zpowers_le.mpr
    refine ⟨⟨z, a.rotation_le (a.z_mem d)⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro v
    exact Subtype.ext (mem_centralizer_singleton_iff.mp
      (d.counterexample.localSetup.sylow_centralizes v.property.1))

end CFSG.Quasithin.Chapter16.ThompsonObstruction.AmbientComputation.ActionConstruction
