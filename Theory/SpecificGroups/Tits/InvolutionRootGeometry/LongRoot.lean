module

public import Theory.SpecificGroups.Tits.InvolutionRootGeometry.MarkedModel
public import Theory.SpecificGroups.Tits.SylowPointwiseInner

/-!
# The central Tits involution is an actual long-root involution

The word r₈r₁r₈ conjugates s₁ to r₅. This is checked in the faithful
permutation representation. The marked Ree comparison sends s₁ to the
square of a type-V root element, so the central Sylow representative lies
in that actual root class. Sylow conjugacy then identifies every nonidentity
pointwise Sylow fixer as conjugation by a member of the same class.

Source: Parrott (1972), §5, p.683; Aschbacher–Smith 16.1.6, printed p.1172.
-/

public section
namespace Tits.InvolutionRootGeometry
open Subgroup

private def atlasW : Atlas1600Group :=
  atlas1600ParrottAssignment .r8 * atlas1600ParrottAssignment .r1 *
    atlas1600ParrottAssignment .r8

private theorem atlas_conjugates :
    atlasW * atlas1600ParrottAssignment .s1 * atlasW⁻¹ = atlas1600R5 := by
  have val_mul (x y : Atlas1600Group) : (x * y).val = x.val * y.val := rfl
  have val_inv (x : Atlas1600Group) : x⁻¹.val = x.val⁻¹ := rfl
  have val_pow (x : Atlas1600Group) (n : ℕ) : (x ^ n).val = x.val ^ n := rfl
  apply Subtype.ext
  simp only [atlasW, atlas1600R5_eq, val_mul, val_inv, val_pow,
    atlas1600ParrottAssignment_val]
  apply Equiv.ext
  apply Atlas1600ParrottData.allFin
  set_option maxRecDepth 20000 in
  set_option maxHeartbeats 1600000 in
  decide +kernel

/-- The distinguished Sylow-central element is conjugate to the root-marked s₁. -/
theorem atlas_r5_isConj_s1 :
    IsConj (atlas1600ParrottAssignment .s1) atlas1600R5 :=
  isConj_iff.mpr ⟨atlasW, atlas_conjugates⟩

/-- Under the faithful Parrott marking, r₅ belongs to the genuine type-V class. -/
theorem r5_isLongRoot : IsLongRoot (parrottFiniteImageEquiv.symm atlas1600R5) := by
  rw [isLongRoot_iff]
  have h := parrottFiniteImageEquiv.symm.toMonoidHom.map_isConj atlas_r5_isConj_s1
  simpa only [MulEquiv.coe_toMonoidHom, ← parrottFiniteImageEquiv_generator,
    MulEquiv.symm_apply_apply] using h

/-- The root-marked generator is a nonidentity involution. -/
theorem s1_order : orderOf (parrottGenerator .s1) = 2 := by
  apply orderOf_eq_prime
  · simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of] using
      parrott_generators_satisfy_relations .i_s1
  · intro h
    have he : atlas1600ParrottAssignment .s1 = 1 := by
      rw [← parrottFiniteImageEquiv_generator, h, map_one]
    have hc := atlas_r5_isConj_s1
    rw [he, isConj_one_right] at hc
    exact atlas1600R5_ne_one hc

/-- The marked type-V element has order two in the derived matrix group. -/
theorem longRoot_order : orderOf longRoot = 2 :=
  (orderOf_injective derivedEquiv.toMonoidHom derivedEquiv.injective _).trans s1_order

/-- The explicit generator of the binary type-V relative root group. -/
noncomputable def longRootGenerator : ReeF4.Model 0 :=
  ⟨ReeF4.DerivedTits.Realization.quartetElement 0,
    (ReeF4.mem_fixedSubgroup 0 _).mpr
      (ReeF4.DerivedTits.Realization.quartetElement_fixed 0)⟩

/-- The long-root involution is the square of that actual fixed root element. -/
theorem longRoot_eq_square : (longRoot : ReeF4.Model 0) = longRootGenerator ^ 2 := by
  apply ReeF4.toSplitGroup_injective 0
  simpa only [map_pow, ReeF4.toSplitGroup_apply, longRootGenerator] using longRoot_matrix

/-- The actual binary type-V root element has order four. -/
theorem longRootGenerator_order : orderOf longRootGenerator = 4 := by
  have hs : (longRoot : ReeF4.Model 0) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one longRoot
    rw [longRoot_order] at h
    exact congrArg Subtype.val h
  have hn : (longRoot : ReeF4.Model 0) ≠ 1 := by
    intro h
    have he : longRoot = 1 := Subtype.ext h
    have ho := longRoot_order
    rw [he, orderOf_one] at ho
    omega
  rw [longRoot_eq_square] at hs hn
  have h4 : longRootGenerator ^ (2 ^ (1 + 1)) = 1 := by
    simpa only [← pow_mul, Nat.reduceAdd, Nat.reducePow, Nat.reduceMul] using hs
  exact orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using hn) h4

private theorem atlas_central_isConj (P : Sylow 2 Atlas1600Group)
    (x : Atlas1600Group) (hx : x ∈ P)
    (hc : x ∈ centralizer (P : Set Atlas1600Group)) (hne : x ≠ 1) :
    IsConj atlas1600R5 x := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Atlas1600Group P atlas1600SylowTwo
  have hm : (P : Subgroup Atlas1600Group).map (MulAut.conj g).toMonoidHom =
      atlas1600SylowTwoSubgroup := by
    have hh := congrArg Sylow.toSubgroup hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, atlas1600SylowTwo_coe] at hh
    exact hh
  have he := RelativeSylowMarking.image_eq_r5_of_sylow_center (MulAut.conj g) P hm hx hc hne
  exact (isConj_iff.mpr ⟨g, he⟩).symm

/-- The matrix-defined long-root class is exactly the class of nonidentity
Sylow-central elements. This uses the root comparison, not a centrality label. -/
theorem isLongRoot_iff_twoCentral (x : ParrottGroup) :
    IsLongRoot x ↔ x ≠ 1 ∧ ∃ P : Sylow 2 ParrottGroup,
      x ∈ P ∧ x ∈ centralizer (P : Set ParrottGroup) := by
  let e := parrottFiniteImageEquiv
  constructor
  · intro hx
    have hc := e.toMonoidHom.map_isConj ((isLongRoot_iff x).mp hx)
    have hc' : IsConj atlas1600R5 (e x) := atlas_r5_isConj_s1.symm.trans (by
      simpa only [e, MulEquiv.coe_toMonoidHom, parrottFiniteImageEquiv_generator] using hc)
    have hn : x ≠ 1 := by
      intro he
      rw [he, map_one, isConj_one_left] at hc'
      exact atlas1600R5_ne_one hc'
    obtain ⟨g, hg⟩ := isConj_iff.mp hc'
    let f := (MulAut.conj g).trans e.symm
    let P := atlas1600SylowTwo.mapSurjective (f := f.toMonoidHom) f.surjective
    have he : f atlas1600R5 = x := by
      change e.symm (g * atlas1600R5 * g⁻¹) = x
      rw [hg, MulEquiv.symm_apply_apply]
    refine ⟨hn, P, ?_, ?_⟩
    · rw [← he]
      apply mem_map_of_mem f.toMonoidHom
      simpa only [atlas1600SylowTwo_coe] using atlas1600R5_mem_sylowTwo
    · rw [mem_centralizer_iff]
      rintro y ⟨z, hz, rfl⟩
      change f z * x = x * f z
      rw [← he, ← map_mul, ← map_mul]
      congr 1
      have hz' : z ∈ atlas1600SylowTwoSubgroup := by
        change z ∈ (atlas1600SylowTwo : Subgroup Atlas1600Group) at hz
        rwa [atlas1600SylowTwo_coe] at hz
      exact congrArg Subtype.val
        (mem_center_iff.mp atlas1600R5_mem_center_sylowTwo ⟨z, hz'⟩)
  · rintro ⟨hn, P, hx, hc⟩
    let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
    have he : e x ∈ Q := mem_map_of_mem e.toMonoidHom hx
    have hc' : e x ∈ centralizer (Q : Set Atlas1600Group) := by
      rw [mem_centralizer_iff]
      rintro y ⟨z, hz, rfl⟩
      change e z * e x = e x * e z
      rw [← map_mul, ← map_mul]
      exact congrArg e (mem_centralizer_iff.mp hc z hz)
    have hn' : e x ≠ 1 := fun h => hn (e.injective (h.trans (map_one e).symm))
    have h := atlas_r5_isConj_s1.trans (atlas_central_isConj Q (e x) he hc' hn')
    apply (isLongRoot_iff x).mpr
    simpa only [e, MulEquiv.coe_toMonoidHom, ← parrottFiniteImageEquiv_generator,
      MulEquiv.symm_apply_apply] using e.symm.toMonoidHom.map_isConj h

/-- Every nonidentity pointwise Sylow fixer acts by an actual long-root element.
No assumption about the order of the automorphism is needed. -/
theorem fixing_sylow_longRoot (P : Sylow 2 ParrottGroup) (a : MulAut ParrottGroup)
    (ha : ∀ x ∈ P, a x = x) (hne : a ≠ 1) :
    ∃ x ∈ P, a = MulAut.conj x ∧ IsLongRoot x := by
  obtain ⟨x, hx, rfl⟩ := SylowPointwiseInner.parrott_fixing_sylow_inner P a ha
  have hn : x ≠ 1 := by
    intro h
    exact hne (h ▸ map_one MulAut.conj)
  let e := parrottFiniteImageEquiv
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hxe : e x ∈ Q := mem_map_of_mem e.toMonoidHom hx
  have hce : e x ∈ centralizer (Q : Set Atlas1600Group) := by
    rw [mem_centralizer_iff]
    rintro y ⟨z, hz, rfl⟩
    have he := ha z hz
    change x * z * x⁻¹ = z at he
    exact (map_mul e z x).symm.trans
      ((congrArg e (mul_inv_eq_iff_eq_mul.mp he).symm).trans (map_mul e x z))
  have hne' : e x ≠ 1 := fun h => hn (e.injective (h.trans (map_one e).symm))
  have h := atlas_r5_isConj_s1.trans (atlas_central_isConj Q (e x) hxe hce hne')
  refine ⟨x, hx, rfl, (isLongRoot_iff x).mpr ?_⟩
  have h' := e.symm.toMonoidHom.map_isConj h
  simpa only [e, MulEquiv.coe_toMonoidHom, ← parrottFiniteImageEquiv_generator,
    MulEquiv.symm_apply_apply] using h'

end Tits.InvolutionRootGeometry
