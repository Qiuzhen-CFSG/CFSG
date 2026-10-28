module

public import Theory.Representation.BinaryPermutation.OffenderFixedSpace

/-!
# Constant displacements and quotient fixed spaces

The inverse image of the deleted fixed space consists of vectors with constant
displacement under each group element. Evaluation at a base point makes these
displacements linear in the vector and additive in the group element. They
vanish on every point stabilizer. Their kernel is the full fixed space, so
rank-nullity measures exactly the extra fixed vectors introduced by quotienting.

This is the quotient linear algebra used in the necessity argument for
Aschbacher–Smith, *The Classification of Quasithin Groups*, B.3.2(4),(6),
printed pp. 83–84. No commutation of invariants with quotients is assumed.
-/

@[expose] public section

namespace BinaryPermutation.QuotientFixedSpace

open Representation.BinaryOffender

variable {Ω : Type*}

/-- Full vectors representing fixed vectors in the deleted module. -/
noncomputable def fixedPreimage (A : Subgroup (Equiv.Perm Ω)) :
    Submodule (ZMod 2) (Full Ω) :=
  (fixedSpace (deletedRepresentation Ω) A).comap (constants Ω).mkQ

theorem mem_fixedPreimage_iff (A : Subgroup (Equiv.Perm Ω)) (v : Full Ω) :
    v ∈ fixedPreimage A ↔
      ∀ a ∈ A, ∃ c : ZMod 2, ∀ i, v (a.symm i) - v i = c :=
  mem_deleted_fixedSpace_iff A v

theorem full_fixed_le_fixedPreimage (A : Subgroup (Equiv.Perm Ω)) :
    fixedSpace (representation Ω) A ≤ fixedPreimage A := by
  intro v hv
  rw [mem_fixedPreimage_iff]
  intro a ha
  exact ⟨0, fun i => sub_eq_zero.mpr ((mem_full_fixedSpace_iff A v).mp hv a ha i)⟩

theorem constants_le_full_fixed (A : Subgroup (Equiv.Perm Ω)) :
    constants Ω ≤ fixedSpace (representation Ω) A := by
  intro v hv
  obtain ⟨c, hc⟩ := (mem_constants_iff v).mp hv
  exact (mem_full_fixedSpace_iff A v).mpr (fun _ _ i => (hc _).trans (hc i).symm)

/-- Displacement at a chosen coordinate, viewed as a function on the group. -/
noncomputable def displacement (A : Subgroup (Equiv.Perm Ω)) (x : Ω) :
    fixedPreimage A →ₗ[ZMod 2] (A → ZMod 2) where
  toFun v a := v.val (a.val.symm x) - v.val x
  map_add' := by intros; ext a; simp only [Submodule.coe_add, Pi.add_apply]; abel
  map_smul' := by intros; ext a; simp [mul_sub]

/-- The displacement is independent of the coordinate used to compute it. -/
theorem displacement_eq (A : Subgroup (Equiv.Perm Ω)) (x : Ω)
    (v : fixedPreimage A) (a : A) (y : Ω) :
    displacement A x v a = v.val (a.val.symm y) - v.val y := by
  obtain ⟨c, hc⟩ := (mem_fixedPreimage_iff A v.val).mp v.property a.val a.property
  exact (hc x).trans (hc y).symm

/-- Constant displacements define additive characters of the acting group. -/
theorem displacement_mul (A : Subgroup (Equiv.Perm Ω)) (x : Ω)
    (v : fixedPreimage A) (a b : A) :
    displacement A x v (a * b) = displacement A x v a + displacement A x v b := by
  rw [displacement_eq A x v b (a.val.symm x)]
  change v.val (b.val.symm (a.val.symm x)) - v.val x =
    (v.val (a.val.symm x) - v.val x) +
      (v.val (b.val.symm (a.val.symm x)) - v.val (a.val.symm x))
  abel

/-- Every point stabilizer is in the kernel of every displacement character. -/
theorem displacement_eq_zero_of_fixes (A : Subgroup (Equiv.Perm Ω)) (x : Ω)
    (v : fixedPreimage A) (a : A) {y : Ω} (hy : a.val y = y) :
    displacement A x v a = 0 := by
  rw [displacement_eq A x v a y, a.val.symm_apply_eq.mpr hy.symm, sub_self]

/-- The displacement kernel consists exactly of full fixed vectors. -/
theorem ker_displacement (A : Subgroup (Equiv.Perm Ω)) (x : Ω) :
    LinearMap.ker (displacement A x) =
      (fixedSpace (representation Ω) A).comap (fixedPreimage A).subtype := by
  ext v
  change displacement A x v = 0 ↔ v.val ∈ fixedSpace (representation Ω) A
  rw [mem_full_fixedSpace_iff]
  constructor
  · intro h a ha y
    apply sub_eq_zero.mp
    rw [← displacement_eq A x v ⟨a, ha⟩ y]
    exact congrFun h ⟨a, ha⟩
  · intro h
    ext a
    exact sub_eq_zero.mpr (h a.val a.property x)

variable [Fintype Ω]

/-- The number of independent displacement characters. -/
noncomputable def displacementRank (A : Subgroup (Equiv.Perm Ω)) (x : Ω) : ℕ :=
  Module.finrank (ZMod 2) (LinearMap.range (displacement A x))

theorem finrank_fixedPreimage (A : Subgroup (Equiv.Perm Ω)) (x : Ω) :
    Module.finrank (ZMod 2) (fixedPreimage A) =
      displacementRank A x + Module.finrank (ZMod 2) (fixedSpace (representation Ω) A) := by
  have h := (displacement A x).finrank_range_add_finrank_ker
  rw [ker_displacement,
    (Submodule.comapSubtypeEquivOfLe (full_fixed_le_fixedPreimage A)).finrank_eq] at h
  exact h.symm

theorem finrank_fixedPreimage_eq_deleted_add_one [Nonempty Ω]
    (A : Subgroup (Equiv.Perm Ω)) :
    Module.finrank (ZMod 2) (fixedPreimage A) =
      Module.finrank (ZMod 2) (fixedSpace (deletedRepresentation Ω) A) + 1 := by
  let f := (constants Ω).mkQ.domRestrict (fixedPreimage A)
  have hr : LinearMap.range f = fixedSpace (deletedRepresentation Ω) A := by
    rw [LinearMap.range_domRestrict]
    exact Submodule.map_comap_eq_of_surjective (constants Ω).mkQ_surjective _
  have hk : LinearMap.ker f = (constants Ω).comap (fixedPreimage A).subtype := by
    rw [LinearMap.ker_domRestrict, Submodule.ker_mkQ]
  have h := f.finrank_range_add_finrank_ker
  rw [hr, hk, (Submodule.comapSubtypeEquivOfLe
    ((constants_le_full_fixed A).trans (full_fixed_le_fixedPreimage A))).finrank_eq,
    finrank_constants] at h
  exact h.symm

/-- Exact correction to the full fixed codimension on quotienting by constants. -/
theorem fixedCodim_deleted_add_displacementRank [Nonempty Ω]
    (A : Subgroup (Equiv.Perm Ω)) (x : Ω) :
    fixedCodim (deletedRepresentation Ω) A + displacementRank A x =
      fixedCodim (representation Ω) A := by
  have h := finrank_fixedPreimage A x
  rw [finrank_fixedPreimage_eq_deleted_add_one] at h
  have hD := fixedCodim_add_finrank (deletedRepresentation Ω) A
  have hF := fixedCodim_add_finrank (representation Ω) A
  rw [finrank_deleted] at hD
  rw [finrank_full] at hF
  have hp : 0 < Fintype.card Ω := Fintype.card_pos
  omega

omit [Fintype Ω] in
theorem fixedPreimage_eq_full_of_fixed_point {A : Subgroup (Equiv.Perm Ω)} {x : Ω}
    (hx : ∀ a ∈ A, a x = x) : fixedPreimage A = fixedSpace (representation Ω) A := by
  apply le_antisymm ?_ (full_fixed_le_fixedPreimage A)
  intro v hv
  rw [mem_fixedSpace_iff]
  intro a ha
  exact (deleted_fixed_iff_of_fixed_point a v x (hx a ha)).mp
    ((mem_fixedSpace_iff _ A _).mp hv a ha)

theorem displacementRank_eq_zero_of_fixed_point {A : Subgroup (Equiv.Perm Ω)}
    {x : Ω} (hx : ∀ a ∈ A, a x = x) (y : Ω) : displacementRank A y = 0 := by
  have hd : displacement A y = 0 := by
    ext v a
    exact displacement_eq_zero_of_fixes A y v a (hx a.val a.property)
  simp [displacementRank, hd]

theorem fixedCodim_deleted_eq_full_of_fixed_point [Nonempty Ω]
    {A : Subgroup (Equiv.Perm Ω)} {x : Ω} (hx : ∀ a ∈ A, a x = x) :
    fixedCodim (deletedRepresentation Ω) A = fixedCodim (representation Ω) A := by
  have h := fixedCodim_deleted_add_displacementRank A x
  simpa only [displacementRank_eq_zero_of_fixed_point hx x, Nat.add_zero] using h

/-- Restriction to the natural submodule intersects the deleted fixed space. -/
noncomputable def naturalFixedEquivInf (A : Subgroup (Equiv.Perm Ω)) :
    fixedSpace (naturalRepresentation Ω) A ≃ₗ[ZMod 2]
      (fixedSpace (deletedRepresentation Ω) A ⊓ natural Ω :
        Submodule (ZMod 2) (Deleted Ω)) where
  toFun v := ⟨v.val.val, ⟨(mem_fixedSpace_iff _ _ _).mpr (fun a ha =>
    congrArg Subtype.val ((mem_fixedSpace_iff _ _ _).mp v.property a ha)),
    v.val.property⟩⟩
  invFun v := ⟨⟨v.val, v.property.2⟩,
    (mem_fixedSpace_iff _ _ _).mpr (fun a ha =>
      Subtype.ext ((mem_fixedSpace_iff _ _ _).mp v.property.1 a ha))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restricting to the natural submodule cannot increase fixed codimension. -/
theorem fixedCodim_natural_le_deleted (A : Subgroup (Equiv.Perm Ω)) :
    fixedCodim (naturalRepresentation Ω) A ≤ fixedCodim (deletedRepresentation Ω) A := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (fixedSpace (deletedRepresentation Ω) A) (natural Ω)
  rw [← (naturalFixedEquivInf A).finrank_eq] at h
  have hs := Submodule.finrank_le (fixedSpace (deletedRepresentation Ω) A ⊔ natural Ω)
  have hN := fixedCodim_add_finrank (naturalRepresentation Ω) A
  have hD := fixedCodim_add_finrank (deletedRepresentation Ω) A
  omega

/-- In even degree, natural and deleted fixed codimensions differ by at most one. -/
theorem fixedCodim_deleted_le_natural_add_one [Nonempty Ω]
    (heven : Even (Fintype.card Ω)) (A : Subgroup (Equiv.Perm Ω)) :
    fixedCodim (deletedRepresentation Ω) A ≤
      fixedCodim (naturalRepresentation Ω) A + 1 := by
  have h := Submodule.finrank_mono (show
    fixedSpace (deletedRepresentation Ω) A ⊓ natural Ω ≤
      fixedSpace (deletedRepresentation Ω) A from inf_le_left)
  rw [← (naturalFixedEquivInf A).finrank_eq] at h
  have hN := fixedCodim_add_finrank (naturalRepresentation Ω) A
  have hD := fixedCodim_add_finrank (deletedRepresentation Ω) A
  rw [finrank_natural_even Ω heven] at hN
  rw [finrank_deleted] at hD
  omega

theorem fixedPreimage_eq_full_of_displacementRank_eq_zero
    (A : Subgroup (Equiv.Perm Ω)) (x : Ω) (h : displacementRank A x = 0) :
    fixedPreimage A = fixedSpace (representation Ω) A := by
  apply (Submodule.eq_of_le_of_finrank_eq (full_fixed_le_fixedPreimage A) ?_).symm
  simpa only [h, zero_add] using (finrank_fixedPreimage A x).symm

/-- If quotient-fixed representatives are already fixed, the same is true on the core. -/
theorem natural_fixed_finrank_add_one [Nonempty Ω]
    (heven : Even (Fintype.card Ω)) (A : Subgroup (Equiv.Perm Ω))
    (hlift : fixedPreimage A = fixedSpace (representation Ω) A) :
    Module.finrank (ZMod 2) (fixedSpace (naturalRepresentation Ω) A) + 1 =
      Module.finrank (ZMod 2) (fixedSpace (coreRepresentation Ω) A) := by
  let C := core Ω ⊓ fixedSpace (representation Ω) A
  let f := (constants Ω).mkQ.domRestrict C
  have hr : LinearMap.range f = fixedSpace (deletedRepresentation Ω) A ⊓ natural Ω := by
    ext w
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨full_fixed_le_fixedPreimage A v.property.2,
        ⟨v.val, v.property.1, rfl⟩⟩
    · rintro ⟨hw, v, hv, rfl⟩
      refine ⟨⟨v, hv, ?_⟩, rfl⟩
      exact hlift ▸ hw
  have hk : LinearMap.ker f = (constants Ω).comap C.subtype := by
    rw [LinearMap.ker_domRestrict, Submodule.ker_mkQ]
  have hc : constants Ω ≤ C :=
    le_inf ((constants_le_core_iff Ω).mpr heven) (constants_le_full_fixed A)
  let e : C ≃ₗ[ZMod 2] fixedSpace (coreRepresentation Ω) A :=
    { toFun := fun v => ⟨⟨v.val, v.property.1⟩,
        (mem_core_fixedSpace_iff A _).mpr
          ((mem_full_fixedSpace_iff A _).mp v.property.2)⟩
      invFun := fun v => ⟨v.val.val, v.val.property,
        (mem_full_fixedSpace_iff A _).mpr
          ((mem_core_fixedSpace_iff A _).mp v.property)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have h := f.finrank_range_add_finrank_ker
  rw [hr, ← (naturalFixedEquivInf A).finrank_eq, hk,
    (Submodule.comapSubtypeEquivOfLe hc).finrank_eq, finrank_constants, e.finrank_eq] at h
  exact h

/-- When the deleted quotient creates no new fixed representatives, natural
and core fixed codimensions agree. -/
theorem fixedCodim_natural_eq_core_of_lift [Nonempty Ω]
    (heven : Even (Fintype.card Ω)) (A : Subgroup (Equiv.Perm Ω))
    (hlift : fixedPreimage A = fixedSpace (representation Ω) A) :
    fixedCodim (naturalRepresentation Ω) A = fixedCodim (coreRepresentation Ω) A := by
  have h := natural_fixed_finrank_add_one heven A hlift
  have hN := fixedCodim_add_finrank (naturalRepresentation Ω) A
  have hC := fixedCodim_add_finrank (coreRepresentation Ω) A
  rw [finrank_natural_even Ω heven] at hN
  rw [finrank_core] at hC
  have hp := Fintype.card_pos (α := Ω)
  have he := heven.two_dvd
  have hn : 2 ≤ Fintype.card Ω := Nat.le_of_dvd hp he
  omega

end BinaryPermutation.QuotientFixedSpace
