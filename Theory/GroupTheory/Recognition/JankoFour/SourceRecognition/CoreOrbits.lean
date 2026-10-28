module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.CubicModule
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.VectorOrbits.Native
public import Theory.GroupTheory.PGroup.ExtraspecialPrimeCosetFusion
public import Theory.Representation.Mathieu.M22James.Unitary.Forms

/-!
# Actual core involutions and their quotient stabilizers

The James-module equivalence preserves the original extraspecial square form:
the native module has only one nonzero invariant binary quadratic form. It
therefore also preserves the polar form. Its two singular vector orbits lift
to two distinct noncentral involutions in the original Q. Inner fusion within
a central coset lifts each vector transport to conjugacy in H = C_G(z).
The same adjustment identifies each quotient-vector stabilizer with the image
of C_H(r) through the original H → H/Q, retaining the literal quotient map.

Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*, Invent.
Math. 105 (1991), (4.2), p.597, DOI 10.1007/BF01232280. The stabilizer types
S₅/E₃₂ and S₅/E₁₆ and their use in (4.3) remain to be constructed; the
cover theorem here does not assert that the two H-classes are different.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open Subgroup Sporadic.Mathieu Representation
variable {G : Type*} [Group G] [Finite G] {z : G} (h : IsTypeJ4 z)
variable (e : CubicAutomorphismQuotient ((centralizer z) ⧸ core z))
variable (X : Sylow 3 (LocalGeometry.CubicLift.subgroup e))
variable [IsExtraspecial 2 (core z)]

noncomputable def coreNativeEquiv : CoreSpace (z := z) ≃ₗ[ZMod 2] M22TripleCover.BinarySpace :=
  (cubicCentralizerRepresentation_james h e X).2.some.toLinearEquiv

theorem coreNativeEquiv_intertwines (g : cubicCentralizer e X) (v : CoreSpace (z := z)) :
    coreNativeEquiv h e X (cubicCentralizerRepresentation h e X g v) =
      M22TripleCover.binaryRepresentation (cubicCentralizerTripleEquiv h e X g)
        (coreNativeEquiv h e X v) :=
  LinearMap.congr_fun ((cubicCentralizerRepresentation_james h e X).2.some.isIntertwining' g) v

noncomputable def nativeCoreForm : QuadraticForm (ZMod 2) M22TripleCover.BinarySpace :=
  (coreQuadraticForm (z := z)).comp (coreNativeEquiv h e X).symm.toLinearMap

theorem nativeCoreForm_invariant (g : M22TripleCover) (v : M22TripleCover.BinarySpace) :
    nativeCoreForm h e X (M22TripleCover.binaryRepresentation g v) = nativeCoreForm h e X v := by
  obtain ⟨g,rfl⟩ := (cubicCentralizerTripleEquiv h e X).surjective g
  obtain ⟨v,rfl⟩ := (coreNativeEquiv h e X).surjective v
  rw [← coreNativeEquiv_intertwines]
  change coreQuadraticForm ((coreNativeEquiv h e X).symm
    (coreNativeEquiv h e X (cubicCentralizerRepresentation h e X g v))) =
      coreQuadraticForm ((coreNativeEquiv h e X).symm (coreNativeEquiv h e X v))
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply,
    cubicCentralizerRepresentation_apply, coreQuadraticForm_invariant]

theorem nativeCoreForm_ne_zero : nativeCoreForm h e X ≠ 0 := by
  intro hz
  have hq : coreQuadraticForm (z := z) = 0 := by
    ext v
    have he := congrArg (fun q : QuadraticForm (ZMod 2) M22TripleCover.BinarySpace =>
      q (coreNativeEquiv h e X v)) hz
    change coreQuadraticForm ((coreNativeEquiv h e X).symm (coreNativeEquiv h e X v)) = 0 at he
    change coreQuadraticForm v = 0
    simpa only [LinearEquiv.symm_apply_apply] using he
  let : Nontrivial (CoreSpace (z := z)) :=
    (coreNativeEquiv h e X).toEquiv.nontrivial
  obtain ⟨v,hv⟩ := exists_ne (0 : CoreSpace (z := z))
  apply hv
  apply (coreQuadraticForm_nondegenerate (z := z)).1 v
  intro w
  rw [hq]
  simp [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]

private theorem native_unitary_form_ne_zero : M22TripleCover.Unitary.quadraticForm ≠ 0 := by
  intro hq
  have he := congrArg (fun q : QuadraticForm (ZMod 2) M22TripleCover.BinarySpace =>
    q (VectorOrbits.decode 1)) hq
  have ho : M22TripleCover.Unitary.quadraticForm (VectorOrbits.decode 1) = 1 := by decide +kernel
  rw [ho] at he
  exact one_ne_zero he

/-- The module marking preserves the original square form exactly. -/
theorem nativeCoreForm_eq_unitary : nativeCoreForm h e X = M22TripleCover.Unitary.quadraticForm :=
  VectorOrbits.invariant_quadratic_unique (nativeCoreForm h e X)
    (nativeCoreForm_invariant h e X) (nativeCoreForm_ne_zero h e X)
    M22TripleCover.Unitary.quadraticForm M22TripleCover.Unitary.quadraticForm_invariant
    native_unitary_form_ne_zero

theorem coreNativeEquiv_quadratic (v : CoreSpace (z := z)) :
    M22TripleCover.Unitary.quadraticForm (coreNativeEquiv h e X v) = coreQuadraticForm v := by
  rw [← nativeCoreForm_eq_unitary h e X]
  exact congrArg coreQuadraticForm ((coreNativeEquiv h e X).symm_apply_apply v)

theorem coreNativeEquiv_polar (v w : CoreSpace (z := z)) :
    M22TripleCover.Unitary.quadraticForm.polarBilin (coreNativeEquiv h e X v)
      (coreNativeEquiv h e X w) = (coreQuadraticForm (z := z)).polarBilin v w := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    ← map_add (coreNativeEquiv h e X), coreNativeEquiv_quadratic]

/-- The exact original square form, in native coordinates. -/
theorem coreNativeEquiv_square (q : core z) :
    q ^ 2 = 1 ↔
      VectorOrbits.label (coreNativeEquiv h e X
        (Additive.ofMul (QuotientGroup.mk' (center (core z)) q))) ≠ 1 := by
  let v := Additive.ofMul (QuotientGroup.mk' (center (core z)) q)
  obtain ⟨n, hn⟩ := VectorOrbits.decode_bijective.surjective (coreNativeEquiv h e X v)
  have hv := VectorOrbits.quadratic_value (nativeCoreForm h e X)
    (nativeCoreForm_invariant h e X) (nativeCoreForm_ne_zero h e X) n
  rw [hn] at hv
  change coreQuadraticForm ((coreNativeEquiv h e X).symm (coreNativeEquiv h e X v)) = _ at hv
  rw [LinearEquiv.symm_apply_apply] at hv
  rw [← coreQuadraticForm_mk_eq_zero]
  change coreQuadraticForm v = 0 ↔ _
  rw [hv, ← hn, VectorOrbits.label_decode]
  split_ifs <;> simp_all

/-- A vector orbit for the original H/Q action lifts to literal H-conjugacy. -/
theorem core_isConj_of_vector_orbit (a b : core z) (ha : a ∉ center (core z))
    (g : centralizer z ⧸ core z)
    (hg : coreBinaryRepresentation h g
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) a)) =
        Additive.ofMul (QuotientGroup.mk' (center (core z)) b)) :
    IsConj (a : centralizer z) (b : centralizer z) := by
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (core z) g
  have hc : QuotientGroup.mk' (center (core z)) (MulAut.conjNormal g a) =
      QuotientGroup.mk' (center (core z)) b := by
    have he := congrArg Additive.toMul hg
    change coreQuotientAction h (QuotientGroup.mk' (core z) g)
      (QuotientGroup.mk' (center (core z)) a) = QuotientGroup.mk' (center (core z)) b at he
    rwa [coreQuotientAction_mk] at he
  have hnc : MulAut.conjNormal g a ∉ center (core z) := by
    intro hn
    apply ha
    apply mem_center_iff.mpr
    intro y
    apply (MulAut.conjNormal g).injective
    simpa only [map_mul] using (mem_center_iff.mp hn (MulAut.conjNormal g y))
  obtain ⟨u,hu⟩ := isConj_iff.mp
    (IsExtraspecial.isConj_of_center_quotient_eq_prime (p := 2) hnc hc)
  apply isConj_iff.mpr
  refine ⟨(u : centralizer z) * g, ?_⟩
  have he := congrArg Subtype.val hu
  change (u : centralizer z) * (g * (a : centralizer z) * g⁻¹) * (u : centralizer z)⁻¹ = b at he
  calc
    _ = (u : centralizer z) * (g * (a : centralizer z) * g⁻¹) * (u : centralizer z)⁻¹ := by group
    _ = b := he

/-- Stabilizer for the literal original quotient action. -/
noncomputable def coreVectorStabilizer (r : core z) : Subgroup (centralizer z ⧸ core z) where
  carrier := {g | coreBinaryRepresentation h g
    (Additive.ofMul (QuotientGroup.mk' (center (core z)) r)) =
      Additive.ofMul (QuotientGroup.mk' (center (core z)) r)}
  one_mem' := by
    change coreBinaryRepresentation h 1 _ = _
    rw [map_one]
    rfl
  mul_mem' := by
    intro a b ha hb
    change coreBinaryRepresentation h (a*b) _ = _
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := by
    intro g hg
    have he := congrArg (coreBinaryRepresentation h g⁻¹) hg
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one] at he
    exact he.symm

/-- The source stabilizer is the image of the element centralizer, through
H → H/Q. Inner conjugation supplies exactly the missing central adjustment. -/
theorem coreVectorStabilizer_eq_centralizer_image (r : core z)
    (hr : r ∉ center (core z)) :
    coreVectorStabilizer h r =
      (Subgroup.centralizer ({(r : centralizer z)} : Set (centralizer z))).map
        (QuotientGroup.mk' (core z)) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (core z) g
    have hc : QuotientGroup.mk' (center (core z)) (MulAut.conjNormal g r) =
        QuotientGroup.mk' (center (core z)) r := by
      have he := congrArg Additive.toMul hg
      change coreQuotientAction h (QuotientGroup.mk' (core z) g)
        (QuotientGroup.mk' (center (core z)) r) = QuotientGroup.mk' (center (core z)) r at he
      rwa [coreQuotientAction_mk] at he
    have hnc : MulAut.conjNormal g r ∉ center (core z) := by
      intro hn
      apply hr
      apply mem_center_iff.mpr
      intro y
      apply (MulAut.conjNormal g).injective
      simpa only [map_mul] using (mem_center_iff.mp hn (MulAut.conjNormal g y))
    obtain ⟨u,hu⟩ := isConj_iff.mp
      (IsExtraspecial.isConj_of_center_quotient_eq_prime (p := 2) hnc hc)
    refine ⟨(u : centralizer z) * g, ?_, ?_⟩
    · apply mem_centralizer_singleton_iff.mpr
      have he := congrArg Subtype.val hu
      change (u : centralizer z) * (g * (r : centralizer z) * g⁻¹) *
        (u : centralizer z)⁻¹ = r at he
      have heq : ((u : centralizer z) * g) * r * ((u : centralizer z) * g)⁻¹ = r := by
        calc
          _ = (u : centralizer z) * (g * (r : centralizer z) * g⁻¹) *
            (u : centralizer z)⁻¹ := by group
          _ = r := he
      exact mul_inv_eq_iff_eq_mul.mp heq
    · have hu0 : QuotientGroup.mk' (core z) (u : centralizer z) = 1 :=
        (QuotientGroup.eq_one_iff (u : centralizer z)).mpr u.property
      rw [map_mul, hu0, one_mul]
  · rintro _ ⟨g,hg,rfl⟩
    change coreBinaryRepresentation h (QuotientGroup.mk' (core z) g)
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) r)) = _
    change Additive.ofMul (coreQuotientAction h (QuotientGroup.mk' (core z) g)
      (QuotientGroup.mk' (center (core z)) r)) = _
    rw [coreQuotientAction_mk]
    congr 2
    apply Subtype.ext
    change g * (r : centralizer z) * g⁻¹ = r
    rw [mem_centralizer_singleton_iff.mp hg, mul_inv_cancel_right]

/-- Equal native vector labels give conjugacy in the original centralizer. -/
theorem core_isConj_of_label (a b : core z) (ha : a ∉ center (core z))
    (he : VectorOrbits.label (coreNativeEquiv h e X
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) a))) =
        VectorOrbits.label (coreNativeEquiv h e X
          (Additive.ofMul (QuotientGroup.mk' (center (core z)) b)))) :
    IsConj (a : centralizer z) (b : centralizer z) := by
  obtain ⟨g,hg⟩ := (VectorOrbits.orbit_iff_label _ _).mpr he
  let c := (cubicCentralizerTripleEquiv h e X).symm g
  apply core_isConj_of_vector_orbit h a b ha (centerToCoreProjection h c.val)
  apply (coreNativeEquiv h e X).injective
  change coreNativeEquiv h e X (cubicCentralizerRepresentation h e X c _) = _
  rw [coreNativeEquiv_intertwines]
  simpa only [c, MulEquiv.apply_symm_apply] using hg

/-- Representatives for both singular vector orbits lift to noncentral
involutions of Q, and every noncentral involution is H-conjugate to one of
them. The coordinates and conjugators belong to the original source group. -/
theorem source_involution_orbit_cover :
    ∃ r₁ r₂ : core z,
      orderOf r₁ = 2 ∧ orderOf r₂ = 2 ∧
      r₁ ∉ center (core z) ∧ r₂ ∉ center (core z) ∧
      coreNativeEquiv h e X (Additive.ofMul (QuotientGroup.mk' (center (core z)) r₁)) =
        VectorOrbits.decode 4 ∧
      coreNativeEquiv h e X (Additive.ofMul (QuotientGroup.mk' (center (core z)) r₂)) =
        VectorOrbits.decode 7 ∧
      ∀ r : core z, orderOf r = 2 → r ∉ center (core z) →
        IsConj (r : centralizer z) (r₁ : centralizer z) ∨
          IsConj (r : centralizer z) (r₂ : centralizer z) := by
  have hex (n : VectorOrbits.Word) (hn : n = 4 ∨ n = 7) :
      ∃ r : core z, orderOf r = 2 ∧ r ∉ center (core z) ∧
        coreNativeEquiv h e X (Additive.ofMul (QuotientGroup.mk' (center (core z)) r)) =
          VectorOrbits.decode n := by
    obtain ⟨r,hr⟩ := QuotientGroup.mk'_surjective (center (core z))
      ((coreNativeEquiv h e X).symm (VectorOrbits.decode n)).toMul
    have he : coreNativeEquiv h e X
        (Additive.ofMul (QuotientGroup.mk' (center (core z)) r)) = VectorOrbits.decode n := by
      rw [hr]
      exact (coreNativeEquiv h e X).apply_symm_apply _
    have hnc : r ∉ center (core z) := by
      intro hc
      have hr0 : QuotientGroup.mk' (center (core z)) r = 1 :=
        (QuotientGroup.eq_one_iff r).mpr hc
      rw [hr0] at he
      have hz : VectorOrbits.decode n = VectorOrbits.decode 0 := by
        change _ = VectorOrbits.vector 0
        rw [VectorOrbits.vector_zero, ← he]
        exact map_zero _
      have hz := VectorOrbits.decode_injective hz
      rcases hn with rfl | rfl
      · exact (by decide : (4 : VectorOrbits.Word) ≠ 0) hz
      · exact (by decide : (7 : VectorOrbits.Word) ≠ 0) hz
    have hr2 : r^2=1 := by
      rw [coreNativeEquiv_square h e X, he, VectorOrbits.label_decode]
      rcases hn with rfl | rfl <;> decide +kernel
    exact ⟨r,orderOf_eq_prime hr2 (fun h1 => hnc (h1 ▸ (center (core z)).one_mem)), hnc, he⟩
  obtain ⟨r₁,h₁,h₁c,e₁⟩ := hex 4 (Or.inl rfl)
  obtain ⟨r₂,h₂,h₂c,e₂⟩ := hex 7 (Or.inr rfl)
  refine ⟨r₁,r₂,h₁,h₂,h₁c,h₂c,e₁,e₂,?_⟩
  intro r hr hrc
  let v := Additive.ofMul (QuotientGroup.mk' (center (core z)) r)
  obtain ⟨n,hn⟩ := VectorOrbits.decode_bijective.surjective (coreNativeEquiv h e X v)
  have hn0 : n ≠ 0 := by
    intro hn0
    have he := hn
    rw [hn0] at he
    change VectorOrbits.vector 0 = _ at he
    rw [VectorOrbits.vector_zero] at he
    have hv : v = 0 := (coreNativeEquiv h e X).injective ((map_zero _).trans he).symm
    exact hrc ((QuotientGroup.eq_one_iff r).mp (congrArg Additive.toMul hv))
  have hn1 : (VectorOrbits.treeRow n).root ≠ 1 := by
    have he := (coreNativeEquiv_square h e X r).mp (hr ▸ pow_orderOf_eq_one r)
    change VectorOrbits.label (coreNativeEquiv h e X v) ≠ 1 at he
    rwa [← hn, VectorOrbits.label_decode] at he
  rcases VectorOrbits.root_cases n with h0 | h1 | h4 | h7
  · exact False.elim (hn0 ((VectorOrbits.root_zero n).mp h0))
  · exact False.elim (hn1 h1)
  · left
    apply core_isConj_of_label h e X r r₁ hrc
    change VectorOrbits.label (coreNativeEquiv h e X v) = _
    rw [← hn, e₁, VectorOrbits.label_decode, VectorOrbits.label_decode, h4]
    rfl
  · right
    apply core_isConj_of_label h e X r r₂ hrc
    change VectorOrbits.label (coreNativeEquiv h e X v) = _
    rw [← hn, e₂, VectorOrbits.label_decode, VectorOrbits.label_decode, h7]
    rfl

omit [IsExtraspecial 2 (core z)] in
include h in
/-- The intrinsic source hypotheses produce two distinct noncentral
involutions covering all H-classes of noncentral involutions in Q. The
stabilizer structures in the rest of AS91 (4.2) remain separate obligations. -/
theorem source_involution_cover :
    ∃ r₁ r₂ : core z,
      orderOf r₁ = 2 ∧ orderOf r₂ = 2 ∧
      r₁ ∉ center (core z) ∧ r₂ ∉ center (core z) ∧ r₁ ≠ r₂ ∧
      ∀ r : core z, orderOf r = 2 → r ∉ center (core z) →
        IsConj (r : centralizer z) (r₁ : centralizer z) ∨
          IsConj (r : centralizer z) (r₂ : centralizer z) := by
  let := h.extraspecial
  obtain ⟨e⟩ := h.cubic_quotient
  obtain ⟨X⟩ := (inferInstance : Nonempty (Sylow 3 (LocalGeometry.CubicLift.subgroup e)))
  obtain ⟨r₁,r₂,h₁,h₂,h₁c,h₂c,e₁,e₂,hcov⟩ := source_involution_orbit_cover h e X
  refine ⟨r₁,r₂,h₁,h₂,h₁c,h₂c,?_,hcov⟩
  intro he
  subst r₂
  have he := VectorOrbits.decode_injective (e₁.symm.trans e₂)
  exact (by decide : (4 : VectorOrbits.Word) ≠ 7) he

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
end
