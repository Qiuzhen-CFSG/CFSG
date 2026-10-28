module

public import Theory.Representation.SL2FourNaturalOrbits.PlaneOrbits
public import Theory.Representation.SL2FourNaturalOrbits.SemilinearNormalizer
/-!
# Semilinear fusion of the actual SL₂(4) plane orbits

The binary-basis determinant intertwines the literal normalizer action with
its permutation action on the three nonzero field elements. Correcting a
transporter by SL₂ turns the label calculation into an exhaustive plane-orbit
calculation. The induced permutation of the three actual SL₂-orbits is the
full symmetric group, with kernel the original SL₂ image.

The coordinate Frobenius plane has determinant one. Field-involution descent
therefore identifies field type in the specified S₅ with that ten-plane fiber;
the other twenty noncentral planes form its single type-3 orbit. In the full
normalizer all thirty noncentral planes are field type, so there is no type-3
orbit. Field type is also characterized using literal GL₂-conjugates of
Frobenius inside the overgroup, and central type is the Sylow-centralization
condition already identified in `PlaneOrbits`.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, §6.2.5(1),(2),
printed pp.680--681 (PDF pp.697--698). The overgroups here are actual subgroups
of the binary linear group. Ambient-group fusion in §6.2.5(3)--(6) is separate.
-/

@[expose] public section
noncomputable section
namespace Representation.SL2FourNatural.PlaneGeometry
open SemilinearNormalizer Classical

lemma mapPlane_mul (e f : BinaryGL) (U : Plane) :
    mapPlane (e * f) U = mapPlane e (mapPlane f U) := by
  apply Subtype.ext
  exact Submodule.map_comp f.toLinearMap e.toLinearMap U.val

lemma determinant_natural (g : Gamma) (U : Plane) :
    determinant (mapPlane (natural g) U) = g.left.val.det * g.right (determinant U) := by
  rw [determinant_eq _ (mapFrame (natural g) U (chosenFrame U))]
  exact wedge_natural g _ _

lemma determinant_normalizer (x : normalizer) (U : Plane) (a : Fˣ)
    (ha : determinant U = (a : F)) :
    determinant (mapPlane x.val U) = (normalizerLabels x a : F) := by
  rw [determinant_eq _ (mapFrame x.val U (chosenFrame U))]
  exact normalizerLabels_wedge x _ _ a ha

lemma determinant_specialField (x : specialField) (U : Plane) (a : Fˣ)
    (ha : determinant U = (a : F)) :
    determinant (mapPlane x.val U) = (specialFieldLabels x a : F) := by
  obtain ⟨g, rfl⟩ := specialFieldEquiv.surjective x
  rw [specialFieldEquiv_apply, determinant_natural, ha]
  change _ = (labels (specialFieldEquiv.symm (specialFieldEquiv g)).val a : F)
  rw [specialFieldEquiv.symm_apply_apply]
  rfl

lemma specialField_le_normalizer : specialField ≤ normalizer := by
  rw [← specialFieldGamma_map_natural, ← semilinear_eq_normalizer]
  exact Subgroup.map_le_range _ _

lemma fieldLine_map_normalizer (x : normalizer) (U : Plane) :
    IsFieldLine (mapPlane x.val U).val ↔ IsFieldLine U.val := by
  obtain ⟨g,rfl⟩ := normalizerEquiv.surjective x
  rw [← determinant_zero_iff, ← determinant_zero_iff, normalizerEquiv_apply,
    determinant_natural, mul_eq_zero, or_iff_right (Matrix.GeneralLinearGroup.det_ne_zero g.left),
    map_eq_zero_iff _ g.right.injective]

/-- An actor with the required determinant can be corrected by SL₂ to map the planes. -/
private lemma correct_by_special (H : Subgroup BinaryGL) (hH : action.range ≤ H)
    (U W : Plane) (x : BinaryGL) (hx : x ∈ H)
    (hd : determinant (mapPlane x U) = determinant W) :
    ∃ y ∈ H, U.val.map y.toLinearMap = W.val := by
  obtain ⟨A,hA⟩ := (orbit_iff_determinant (mapPlane x U) W).mpr hd
  refine ⟨action A * x, H.mul_mem (hH ⟨A,rfl⟩) hx, ?_⟩
  have he : mapPlane (action A) (mapPlane x U) = W := Subtype.ext hA
  exact congrArg Subtype.val ((mapPlane_mul _ _ _).trans he)

/-- The normalizer has exactly the central and noncentral plane orbits. -/
lemma normalizer_plane_orbit (U W : Plane) :
    (∃ x ∈ normalizer, U.val.map x.toLinearMap = W.val) ↔
      (IsFieldLine U.val ↔ IsFieldLine W.val) := by
  constructor
  · rintro ⟨x,hx,h⟩
    have he : mapPlane x U = W := Subtype.ext h
    exact (fieldLine_map_normalizer ⟨x,hx⟩ U).symm.trans (by rw [he])
  · intro h
    by_cases hu : IsFieldLine U.val
    · obtain ⟨A,hA⟩ := field_line_transitive U W hu (h.mp hu)
      exact ⟨action A, Subgroup.le_normalizer ⟨A,rfl⟩,hA⟩
    · have hw : ¬ IsFieldLine W.val := fun hw => hu (h.mpr hw)
      let a := Units.mk0 (determinant U) (fun hz => hu ((determinant_zero_iff U).mp hz))
      let b := Units.mk0 (determinant W) (fun hz => hw ((determinant_zero_iff W).mp hz))
      obtain ⟨x,hx⟩ := normalizerLabels_transitive a b
      apply correct_by_special normalizer Subgroup.le_normalizer U W x.val x.property
      rw [determinant_normalizer x U a rfl, hx]
      rfl

/-- In the specified S₅, noncentral planes split by whether their determinant is one. -/
lemma specialField_noncentral_orbit (U W : Plane)
    (hu : ¬ IsFieldLine U.val) (hw : ¬ IsFieldLine W.val) :
    (∃ x ∈ specialField, U.val.map x.toLinearMap = W.val) ↔
      (determinant U = 1 ↔ determinant W = 1) := by
  let a := Units.mk0 (determinant U) (fun hz => hu ((determinant_zero_iff U).mp hz))
  let b := Units.mk0 (determinant W) (fun hz => hw ((determinant_zero_iff W).mp hz))
  have ha : a = 1 ↔ determinant U = 1 := Units.ext_iff
  have hb : b = 1 ↔ determinant W = 1 := Units.ext_iff
  rw [← ha, ← hb, ← specialField_label_orbit]
  constructor
  · rintro ⟨x,hx,h⟩
    refine ⟨⟨x,hx⟩, Units.ext ?_⟩
    have he : mapPlane x U = W := Subtype.ext h
    have hd := determinant_specialField ⟨x,hx⟩ U a rfl
    rw [he] at hd
    exact hd.symm
  · rintro ⟨x,hx⟩
    apply correct_by_special specialField le_sup_left U W x.val x.property
    rw [determinant_specialField x U a rfl, hx]
    rfl

/-- All three S₅ plane orbits are recognized by the two distinguished determinant values. -/
lemma specialField_plane_orbit (U W : Plane) :
    (∃ x ∈ specialField, U.val.map x.toLinearMap = W.val) ↔
      (determinant U = 0 ↔ determinant W = 0) ∧
      (determinant U = 1 ↔ determinant W = 1) := by
  constructor
  · rintro ⟨x,hx,h⟩
    have hc := (normalizer_plane_orbit U W).mp ⟨x,specialField_le_normalizer hx,h⟩
    refine ⟨by simpa only [determinant_zero_iff] using hc, ?_⟩
    by_cases hu : IsFieldLine U.val
    · simp [(determinant_zero_iff U).mpr hu, (determinant_zero_iff W).mpr (hc.mp hu)]
    · exact (specialField_noncentral_orbit U W hu (fun hw => hu (hc.mpr hw))).mp ⟨x,hx,h⟩
  · rintro ⟨h0,h1⟩
    by_cases hu : IsFieldLine U.val
    · obtain ⟨A,hA⟩ := field_line_transitive U W hu
        ((determinant_zero_iff W).mp (h0.mp ((determinant_zero_iff U).mpr hu)))
      exact ⟨action A, (show action.range ≤ specialField from le_sup_left) ⟨A,rfl⟩, hA⟩
    · exact (specialField_noncentral_orbit U W hu
        (fun hw => hu ((determinant_zero_iff U).mp (h0.mpr ((determinant_zero_iff W).mpr hw))))).mpr h1

/-- The coordinate Frobenius fixes the determinant-one plane. -/
lemma determinant_fieldFixed : determinant ⟨fieldFixed,card_fieldFixed⟩ = 1 := by
  let u : fieldFixed := ⟨![1,0], by rw [mem_fieldFixed]; intro i; fin_cases i <;> simp⟩
  let v : fieldFixed := ⟨![0,1], by rw [mem_fieldFixed]; intro i; fin_cases i <;> simp⟩
  let p : Frame fieldFixed := ⟨(u,v), by decide, by decide, by decide⟩
  rw [determinant_eq _ p]
  norm_num [p,u,v,wedge]

/-- Field type is pointwise centralization by an actual outer involution in the overgroup. -/
def IsFieldType (H : Subgroup BinaryGL) (U : Plane) : Prop :=
  ∃ x ∈ H, x ^ 2 = 1 ∧ x ∉ action.range ∧ ∀ v ∈ U.val, x v = v

/-- Type 3 means neither Sylow-central nor field type, as in the source. -/
def IsTypeThree (H : Subgroup BinaryGL) (U : Plane) : Prop :=
  ¬ IsFieldLine U.val ∧ ¬ IsFieldType H U

lemma frobenius_not_special : frobeniusLinear ∉ action.range := by
  rintro ⟨A,hA⟩
  have he : special A = fieldElement := natural_injective (by simpa using hA)
  have hr := congrArg SemidirectProduct.right he
  exact fieldFrobenius_ne_one hr.symm

lemma frobenius_sq : frobeniusLinear ^ 2 = 1 := by
  apply LinearEquiv.ext
  intro v
  exact frobeniusLinear_involutive v

lemma fieldType_of_translate (H : Subgroup BinaryGL) (hH : H ≤ normalizer)
    (hf : frobeniusLinear ∈ H) (x : BinaryGL) (hx : x ∈ H) (U : Plane)
    (hU : fieldFixed.map x.toLinearMap = U.val) : IsFieldType H U := by
  refine ⟨x * frobeniusLinear * x⁻¹, H.mul_mem (H.mul_mem hx hf) (H.inv_mem hx), ?_, ?_, ?_⟩
  · simp only [sq, mul_assoc, inv_mul_cancel_left]
    rw [← mul_assoc frobeniusLinear, ← pow_two, frobenius_sq]
    simp
  · intro hs
    have hn := hH hx
    exact frobenius_not_special ((Subgroup.mem_normalizer_iff.mp hn frobeniusLinear).mpr hs)
  · intro v hv
    have he := conjugate_fieldFixed x
    rw [hU] at he
    have hm : v ∈ (x * frobeniusLinear * x⁻¹).toLinearMap.fixedSubmodule := by rwa [he]
    exact hm

lemma fieldType_specialField_iff (U : Plane) :
    IsFieldType specialField U ↔ determinant U = 1 := by
  constructor
  · rintro ⟨x,hx,h2,hs,hfix⟩
    obtain ⟨A,hA⟩ := specialField_involution_fixed_space x hx h2 hs
    have he : U.val = fieldFixed.map (action A).toLinearMap := by
      apply submodule_eq_of_card _ _
      · rw [← hA]; exact hfix
      · exact U.property.trans (mapPlane (action A) ⟨fieldFixed,card_fieldFixed⟩).property.symm
    have hp : mapPlane (action A) ⟨fieldFixed,card_fieldFixed⟩ = U := Subtype.ext he.symm
    rw [← hp, determinant_action, determinant_fieldFixed]
  · intro hd
    obtain ⟨A,hA⟩ := (orbit_iff_determinant ⟨fieldFixed,card_fieldFixed⟩ U).mpr
      (determinant_fieldFixed.trans hd.symm)
    exact fieldType_of_translate specialField specialField_le_normalizer
      ((show Subgroup.zpowers frobeniusLinear ≤ specialField from le_sup_right)
        (Subgroup.mem_zpowers _)) (action A)
      ((show action.range ≤ specialField from le_sup_left) ⟨A,rfl⟩) U hA

lemma fieldType_normalizer_iff (U : Plane) :
    IsFieldType normalizer U ↔ ¬ IsFieldLine U.val := by
  constructor
  · rintro ⟨x,hx,h2,hs,hfix⟩
    obtain ⟨B,hB⟩ := normalizer_involution_fixed_space x hx h2 hs
    have he : U.val = fieldFixed.map (linear B).toLinearMap := by
      apply submodule_eq_of_card _ _
      · rw [← hB]; exact hfix
      · exact U.property.trans (mapPlane (linear B) ⟨fieldFixed,card_fieldFixed⟩).property.symm
    have hn : linear B ∈ normalizer := semilinear_le_normalizer ⟨SemidirectProduct.inl B,rfl⟩
    have hp : mapPlane (linear B) ⟨fieldFixed,card_fieldFixed⟩ = U := Subtype.ext he.symm
    intro hu
    have hf := (fieldLine_map_normalizer ⟨linear B,hn⟩ ⟨fieldFixed,card_fieldFixed⟩).mp (hp ▸ hu)
    have hz := (determinant_zero_iff _).mpr hf
    rw [determinant_fieldFixed] at hz
    exact one_ne_zero hz
  · intro hu
    have hf : ¬ IsFieldLine fieldFixed := by
      intro hf
      have hz := (determinant_zero_iff ⟨fieldFixed,card_fieldFixed⟩).mpr hf
      rw [determinant_fieldFixed] at hz
      exact one_ne_zero hz
    obtain ⟨x,hx,he⟩ := (normalizer_plane_orbit ⟨fieldFixed,card_fieldFixed⟩ U).mpr (by simp [hf,hu])
    exact fieldType_of_translate normalizer le_rfl
      (semilinear_le_normalizer ⟨fieldElement,natural_fieldElement⟩) x hx U he

/-- Field type can equivalently be expressed using literal linear conjugates of
coordinate Frobenius, with their actual fixed planes. -/
lemma fieldType_iff_conjugate (H : Subgroup BinaryGL) (hH : H ≤ normalizer) (U : Plane) :
    IsFieldType H U ↔ ∃ B : LinearGroup,
      linear B * frobeniusLinear * (linear B)⁻¹ ∈ H ∧
      fieldFixed.map (linear B).toLinearMap = U.val := by
  constructor
  · rintro ⟨x,hx,h2,hs,hfix⟩
    obtain ⟨B,rfl⟩ := normalizer_involution_conjugate x (hH hx) h2 hs
    refine ⟨B,hx,?_⟩
    apply (submodule_eq_of_card U.val _ ?_ (U.property.trans
      (mapPlane (linear B) ⟨fieldFixed,card_fieldFixed⟩).property.symm)).symm
    change U.val ≤ fieldFixed.map (linear B).toLinearMap
    rw [← conjugate_fieldFixed]
    exact hfix
  · rintro ⟨B,hB,hU⟩
    refine ⟨linear B * frobeniusLinear * (linear B)⁻¹,hB,?_,?_,?_⟩
    · simp only [sq, mul_assoc, inv_mul_cancel_left]
      rw [← mul_assoc frobeniusLinear, ← pow_two, frobenius_sq]
      simp
    · intro hs
      have hn : linear B ∈ normalizer :=
        semilinear_le_normalizer ⟨SemidirectProduct.inl B,rfl⟩
      exact frobenius_not_special ((Subgroup.mem_normalizer_iff.mp hn frobeniusLinear).mpr hs)
    · intro v hv
      have hm : v ∈ (linear B * frobeniusLinear * (linear B)⁻¹).toLinearMap.fixedSubmodule := by
        rwa [conjugate_fieldFixed, hU]
      exact hm

lemma typeThree_specialField_iff (U : Plane) :
    IsTypeThree specialField U ↔ determinant U ≠ 0 ∧ determinant U ≠ 1 := by
  rw [IsTypeThree, fieldType_specialField_iff, ← determinant_zero_iff]

lemma not_typeThree_normalizer (U : Plane) : ¬ IsTypeThree normalizer U := by
  simp only [IsTypeThree, fieldType_normalizer_iff, not_and, not_not, imp_self]

lemma card_fieldType_specialField : Nat.card {U : Plane // IsFieldType specialField U} = 10 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight fieldType_specialField_iff), card_determinant_fiber]
  exact if_neg one_ne_zero

lemma card_fieldType_normalizer : Nat.card {U : Plane // IsFieldType normalizer U} = 30 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight fieldType_normalizer_iff), card_noncentral_planes]

lemma card_typeThree_specialField : Nat.card {U : Plane // IsTypeThree specialField U} = 20 := by
  classical
  let := Fintype.ofFinite Plane
  have he : {U : Plane // IsTypeThree specialField U} ≃
      {U : Plane // ¬ (determinant U = 0 ∨ determinant U = 1)} :=
    Equiv.subtypeEquivRight (fun U => by rw [typeThree_specialField_iff]; tauto)
  rw [Nat.card_congr he, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_or_disjoint]
  · simp [← Nat.card_eq_fintype_card, card_planes, card_determinant_fiber]
  · intro p hp0 hp1 U hU
    exact zero_ne_one ((hp0 U hU).symm.trans (hp1 U hU))

lemma card_typeThree_normalizer : Nat.card {U : Plane // IsTypeThree normalizer U} = 0 := by
  have : IsEmpty {U : Plane // IsTypeThree normalizer U} :=
    ⟨fun U => not_typeThree_normalizer U.val U.property⟩
  simp

/-- The full normalizer's plane orbits have lengths five and thirty. -/
lemma card_normalizer_plane_orbit (U : Plane) :
    Nat.card {W : Plane // ∃ x ∈ normalizer, U.val.map x.toLinearMap = W.val} =
      if IsFieldLine U.val then 5 else 30 := by
  classical
  rw [Nat.card_congr (Equiv.subtypeEquivRight (normalizer_plane_orbit U))]
  by_cases hu : IsFieldLine U.val
  · rw [if_pos hu]
    exact (Nat.card_congr (Equiv.subtypeEquivRight (fun W => by simp [hu]))).trans card_field_lines
  · rw [if_neg hu]
    exact (Nat.card_congr (Equiv.subtypeEquivRight (fun W => by simp [hu]))).trans card_noncentral_planes

/-- The specified S₅'s plane orbits have lengths five, ten, and twenty. -/
lemma card_specialField_plane_orbit (U : Plane) :
    Nat.card {W : Plane // ∃ x ∈ specialField, U.val.map x.toLinearMap = W.val} =
      if IsFieldLine U.val then 5 else if IsFieldType specialField U then 10 else 20 := by
  classical
  rw [Nat.card_congr (Equiv.subtypeEquivRight (specialField_plane_orbit U))]
  by_cases h0 : determinant U = 0
  · rw [if_pos ((determinant_zero_iff U).mp h0)]
    have he : {W : Plane // (determinant U = 0 ↔ determinant W = 0) ∧
        (determinant U = 1 ↔ determinant W = 1)} ≃ {W : Plane // determinant W = 0} :=
      Equiv.subtypeEquivRight (fun W => by
        simp only [h0, true_iff, zero_ne_one, false_iff]
        constructor
        · exact fun h => h.1
        · intro hz; exact ⟨hz, by rw [hz]; exact zero_ne_one⟩)
    rw [Nat.card_congr he, card_determinant_fiber, if_pos rfl]
  · rw [if_neg (fun hu => h0 ((determinant_zero_iff U).mpr hu))]
    by_cases h1 : determinant U = 1
    · rw [if_pos ((fieldType_specialField_iff U).mpr h1)]
      have he : {W : Plane // (determinant U = 0 ↔ determinant W = 0) ∧
          (determinant U = 1 ↔ determinant W = 1)} ≃ {W : Plane // determinant W = 1} :=
        Equiv.subtypeEquivRight (fun W => by
          simp only [h1, false_iff, true_iff, one_ne_zero]
          constructor
          · exact fun h => h.2
          · intro hz; exact ⟨by rw [hz]; exact one_ne_zero, hz⟩)
      rw [Nat.card_congr he, card_determinant_fiber, if_neg one_ne_zero]
    · rw [if_neg (fun hf => h1 ((fieldType_specialField_iff U).mp hf))]
      have he : {W : Plane // (determinant U = 0 ↔ determinant W = 0) ∧
          (determinant U = 1 ↔ determinant W = 1)} ≃ {W : Plane // IsTypeThree specialField W} :=
        Equiv.subtypeEquivRight (fun W => by simp [h0,h1,typeThree_specialField_iff])
      rw [Nat.card_congr he, card_typeThree_specialField]

lemma fieldType_transitive_specialField (U W : Plane)
    (hu : IsFieldType specialField U) (hw : IsFieldType specialField W) :
    ∃ x ∈ specialField, U.val.map x.toLinearMap = W.val := by
  apply (specialField_plane_orbit U W).mpr
  simp [(fieldType_specialField_iff U).mp hu, (fieldType_specialField_iff W).mp hw]

lemma fieldType_transitive_normalizer (U W : Plane)
    (hu : IsFieldType normalizer U) (hw : IsFieldType normalizer W) :
    ∃ x ∈ normalizer, U.val.map x.toLinearMap = W.val := by
  apply (normalizer_plane_orbit U W).mpr
  simp [(fieldType_normalizer_iff U).mp hu, (fieldType_normalizer_iff W).mp hw]

lemma typeThree_transitive_specialField (U W : Plane)
    (hu : IsTypeThree specialField U) (hw : IsTypeThree specialField W) :
    ∃ x ∈ specialField, U.val.map x.toLinearMap = W.val := by
  apply (specialField_plane_orbit U W).mpr
  obtain ⟨hu0,hu1⟩ := (typeThree_specialField_iff U).mp hu
  obtain ⟨hw0,hw1⟩ := (typeThree_specialField_iff W).mp hw
  simp [hu0,hu1,hw0,hw1]

/-- The three actual SL₂-orbits, with their determinant labels as field units. -/
def noncentralOrbitLabelEquiv : Quotient noncentralOrbitSetoid ≃ Fˣ :=
  noncentralOrbitEquiv.trans unitsEquivNeZero.symm

lemma noncentralOrbitLabelEquiv_mk (U : NoncentralPlane) :
    (noncentralOrbitLabelEquiv (Quotient.mk noncentralOrbitSetoid U) : F) = determinant U.val := rfl

def mapNoncentralPlane (x : normalizer) (U : NoncentralPlane) : NoncentralPlane :=
  ⟨mapPlane x.val U.val, fun h => U.property ((fieldLine_map_normalizer x U.val).mp h)⟩

/-- The permutation of the three actual SL₂-orbits induced by the binary normalizer. -/
def normalizerOrbitAction : normalizer →* Equiv.Perm (Quotient noncentralOrbitSetoid) :=
  (Equiv.permCongrHom noncentralOrbitLabelEquiv.symm).toMonoidHom.comp normalizerLabels

/-- This permutation sends the class of a plane to the class of its literal image. -/
lemma normalizerOrbitAction_mk (x : normalizer) (U : NoncentralPlane) :
    normalizerOrbitAction x (Quotient.mk noncentralOrbitSetoid U) =
      Quotient.mk noncentralOrbitSetoid (mapNoncentralPlane x U) := by
  apply noncentralOrbitLabelEquiv.injective
  apply Units.ext
  change (noncentralOrbitLabelEquiv (noncentralOrbitLabelEquiv.symm
    (normalizerLabels x (noncentralOrbitLabelEquiv (Quotient.mk noncentralOrbitSetoid U)))) : F) = _
  rw [noncentralOrbitLabelEquiv.apply_symm_apply, noncentralOrbitLabelEquiv_mk]
  exact (determinant_normalizer x U.val _ (noncentralOrbitLabelEquiv_mk U).symm).symm

lemma normalizerOrbitAction_surjective : Function.Surjective normalizerOrbitAction :=
  (Equiv.permCongrHom noncentralOrbitLabelEquiv.symm).surjective.comp normalizerLabels_surjective

lemma normalizerOrbitAction_ker :
    normalizerOrbitAction.ker = action.range.subgroupOf normalizer := by
  rw [← normalizerLabels_ker]
  ext x
  change (Equiv.permCongrHom noncentralOrbitLabelEquiv.symm) (normalizerLabels x) = 1 ↔ normalizerLabels x = 1
  exact (Equiv.permCongrHom noncentralOrbitLabelEquiv.symm).map_eq_one_iff

lemma mapPlane_one (U : Plane) : mapPlane 1 U = U := by
  apply Subtype.ext
  exact Submodule.map_id _

/-- Orbit equivalence uses the original binary maps in the indicated subgroup. -/
def planeOrbitSetoid (H : Subgroup BinaryGL) : Setoid Plane where
  r U W := ∃ x ∈ H, U.val.map x.toLinearMap = W.val
  iseqv := {
    refl := fun U => ⟨1,H.one_mem,congrArg Subtype.val (mapPlane_one U)⟩
    symm := by
      rintro U W ⟨x,hx,he⟩
      have hm : mapPlane x U = W := Subtype.ext he
      refine ⟨x⁻¹,H.inv_mem hx,congrArg Subtype.val (show mapPlane x⁻¹ W = U from ?_)⟩
      rw [← hm, ← mapPlane_mul, inv_mul_cancel, mapPlane_one]
    trans := by
      rintro U W Z ⟨x,hx,he⟩ ⟨y,hy,hf⟩
      have hm : mapPlane x U = W := Subtype.ext he
      have hn : mapPlane y W = Z := Subtype.ext hf
      refine ⟨y*x,H.mul_mem hy hx,congrArg Subtype.val (show mapPlane (y*x) U = Z from ?_)⟩
      rw [mapPlane_mul, hm, hn] }

/-- The literal set of orbits on source type-3 four-subgroups. -/
def TypeThreeOrbits (H : Subgroup BinaryGL) :=
  Quotient ((planeOrbitSetoid H).comap (Subtype.val : {U : Plane // IsTypeThree H U} → Plane))

lemma card_typeThree_orbits_specialField : Nat.card (TypeThreeOrbits specialField) = 1 := by
  apply Nat.card_eq_one_iff_unique.mpr
  constructor
  · refine ⟨?_⟩
    intro q r
    induction q using Quotient.inductionOn with
    | h U =>
      induction r using Quotient.inductionOn with
      | h W => exact Quotient.sound (typeThree_transitive_specialField U.val W.val U.property W.property)
  · obtain ⟨U⟩ := (Nat.card_pos_iff.mp (show 0 < Nat.card {U : Plane // IsTypeThree specialField U} by
      rw [card_typeThree_specialField]; decide)).1
    exact ⟨Quotient.mk _ U⟩

lemma card_typeThree_orbits_normalizer : Nat.card (TypeThreeOrbits normalizer) = 0 := by
  have : IsEmpty (TypeThreeOrbits normalizer) := ⟨fun q => by
    induction q using Quotient.inductionOn with
    | h U => exact not_typeThree_normalizer U.val U.property⟩
  exact Nat.card_of_isEmpty

end Representation.SL2FourNatural.PlaneGeometry
