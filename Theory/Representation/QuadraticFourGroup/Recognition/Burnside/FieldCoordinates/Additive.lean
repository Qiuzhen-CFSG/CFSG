module

public import Theory.Representation.QuadraticFourGroup.Recognition.Burnside.FieldCoordinates.Data

/-!
# Additive coordinates on the actual Sylow set

Choose distinct Sylow two-subgroups P and Q. The regular action of P
identifies its elements with every point other than P, sending the identity
to Q. An additive equivalence from P to a field therefore extends to an
equivalence from the actual Sylow set to the projective line `Option K`.

We prove that P acts by translations in these coordinates. Given the
intermediate scalar coordinates, we also prove the exact multiplication
formula for the actual two-point stabilizer. No field existence or reciprocal
membership is asserted here; these remain needed for `SylowCoordinates`.

Source: Burnside (1900), pp. 274–275,
`refs/original/burnside-1900.pdf`.
-/

@[expose] public section

open Subgroup Theory.GroupTheory Theory.GroupTheory.InvolutionOddSpectrum
namespace Representation.QuadraticFourGroup.Burnside
variable {G K : Type*} [Group G] [Finite G] [IsSimpleGroup G] [Group.IsPerfect G]

/-- The orbit of Q under P is precisely the complement of P. -/
noncomputable def rootOrbitEquiv (hG : InvolutionOddSpectrum G)
    (t : G) (ht : orderOf t = 2) (P Q : Sylow 2 G) (hPQ : P ≠ Q) :
    P ≃ {R : Sylow 2 G // R ≠ P} := by
  let f : P → {R : Sylow 2 G // R ≠ P} := fun x => ⟨(x : G) • Q, by
    intro hx
    have hxP : (x : G) • P = P :=
      Sylow.smul_eq_iff_mem_normalizer.mpr (le_normalizer x.property)
    exact hPQ (smul_left_cancel (x : G) (hxP.trans hx.symm))⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y he
    obtain ⟨z, _, hz⟩ := hG.sylow_regular t ht P Q (f x) hPQ.symm (f x).property
    exact (hz x rfl).trans (hz y (congrArg Subtype.val he).symm).symm
  · intro R
    obtain ⟨x, hx, _⟩ := hG.sylow_regular t ht P Q R hPQ.symm R.property
    exact ⟨x, Subtype.ext hx⟩

@[simp] theorem rootOrbitEquiv_apply (hG : InvolutionOddSpectrum G)
    (t : G) (ht : orderOf t = 2) (P Q : Sylow 2 G) (hPQ : P ≠ Q) (x : P) :
    (rootOrbitEquiv hG t ht P Q hPQ x).val = (x : G) • Q := rfl

variable [Field K]

/-- Extend additive root-group coordinates by placing P at infinity and Q at zero. -/
noncomputable def rootPointEquiv (hG : InvolutionOddSpectrum G)
    (t : G) (ht : orderOf t = 2) (P Q : Sylow 2 G) (hPQ : P ≠ Q)
    (e : Additive P ≃+ K) : Sylow 2 G ≃ Option K := by
  classical
  exact (Equiv.optionSubtypeNe P).symm.trans (Equiv.optionCongr
    ((rootOrbitEquiv hG t ht P Q hPQ).symm.trans (Additive.ofMul.trans e.toEquiv)))

@[simp] theorem rootPointEquiv_infinity (hG : InvolutionOddSpectrum G)
    (t : G) (ht : orderOf t = 2) (P Q : Sylow 2 G) (hPQ : P ≠ Q)
    (e : Additive P ≃+ K) : rootPointEquiv hG t ht P Q hPQ e P = none := by
  classical
  simp [rootPointEquiv]

@[simp] theorem rootPointEquiv_orbit (hG : InvolutionOddSpectrum G)
    (t : G) (ht : orderOf t = 2) (P Q : Sylow 2 G) (hPQ : P ≠ Q)
    (e : Additive P ≃+ K) (x : P) :
    rootPointEquiv hG t ht P Q hPQ e ((x : G) • Q) = some (e (Additive.ofMul x)) := by
  classical
  let r := rootOrbitEquiv hG t ht P Q hPQ x
  have hr : (x : G) • Q ≠ P := r.property
  simp only [rootPointEquiv, Equiv.trans_apply, Equiv.optionSubtypeNe_symm_of_ne hr,
    Equiv.optionCongr_apply, Option.map_some]
  congr 1
  change e (Additive.ofMul ((rootOrbitEquiv hG t ht P Q hPQ).symm
    (rootOrbitEquiv hG t ht P Q hPQ x))) = e (Additive.ofMul x)
  rw [Equiv.symm_apply_apply]

@[simp] theorem rootPointEquiv_zero (hG : InvolutionOddSpectrum G)
    (t : G) (ht : orderOf t = 2) (P Q : Sylow 2 G) (hPQ : P ≠ Q)
    (e : Additive P ≃+ K) : rootPointEquiv hG t ht P Q hPQ e Q = some 0 := by
  simpa using rootPointEquiv_orbit hG t ht P Q hPQ e 1

/-- The transported root subgroup consists of the translations. -/
theorem rootPointEquiv_translation (hG : InvolutionOddSpectrum G)
    (t : G) (ht : orderOf t = 2) (P Q : Sylow 2 G) (hPQ : P ≠ Q)
    (e : Additive P ≃+ K) (x : P) :
    sylowActionInCoordinates (rootPointEquiv hG t ht P Q hPQ e) (x : G) =
      translation K (e (Additive.ofMul x)) := by
  let ep := rootPointEquiv hG t ht P Q hPQ e
  apply Equiv.ext
  intro y
  obtain ⟨R, rfl⟩ := ep.surjective y
  change ep ((x : G) • ep.symm (ep R)) = translation K (e (Additive.ofMul x)) (ep R)
  rw [ep.symm_apply_apply]
  by_cases hRP : R = P
  · subst R
    have hxP : (x : G) • P = P :=
      Sylow.smul_eq_iff_mem_normalizer.mpr (le_normalizer x.property)
    rw [hxP]
    simp [ep]
  · obtain ⟨z, hz, _⟩ := hG.sylow_regular t ht P Q R hPQ.symm hRP
    rw [← hz, ← mul_smul]
    change ep (((x * z : P) : G) • Q) = translation K (e (Additive.ofMul x)) (ep ((z : G) • Q))
    simp only [ep, rootPointEquiv_orbit, translation_some]
    congr 1
    exact e.map_add (Additive.ofMul x) (Additive.ofMul z)

/-- Every translation is in the transported ambient action image. -/
theorem rootPointEquiv_translations_mem (hG : InvolutionOddSpectrum G)
    (t : G) (ht : orderOf t = 2) (P Q : Sylow 2 G) (hPQ : P ≠ Q)
    (e : Additive P ≃+ K) (b : K) :
    translation K b ∈ (sylowActionInCoordinates (rootPointEquiv hG t ht P Q hPQ e)).range := by
  refine ⟨((e.symm b).toMul : G), ?_⟩
  simpa using rootPointEquiv_translation hG t ht P Q hPQ e ((e.symm b).toMul)

/-- The actual two-point stabilizer acts by the designated field scalars. -/
theorem rootPointEquiv_scalar (hG : InvolutionOddSpectrum G)
    (t : G) (ht : orderOf t = 2) (P Q : Sylow 2 G) (hPQ : P ≠ Q)
    (C : ScalarCoordinates P Q K) (d : twoPoint P Q) (y : Option K) :
    sylowActionInCoordinates (rootPointEquiv hG t ht P Q hPQ C.additive) (d : G) y =
      Option.map (fun x => (C.scalars d : K) * x) y := by
  let ep := rootPointEquiv hG t ht P Q hPQ C.additive
  obtain ⟨R, rfl⟩ := ep.surjective y
  change ep ((d : G) • ep.symm (ep R)) = Option.map (fun x => (C.scalars d : K) * x) (ep R)
  rw [ep.symm_apply_apply]
  have hdFix := (mem_twoPoint P Q d).mp d.property
  by_cases hRP : R = P
  · subst R
    rw [hdFix.1]
    simp only [ep, rootPointEquiv_infinity, Option.map_none]
  · obtain ⟨z, hz, _⟩ := hG.sylow_regular t ht P Q R hPQ.symm hRP
    have hdz : (d : G) • ((z : G) • Q) = ((twoPointConj P Q d z : P) : G) • Q := by
      rw [twoPointConj_coe, mul_smul, mul_smul, inv_smul_eq_iff.mpr hdFix.2.symm]
    rw [← hz, hdz]
    simp only [ep, rootPointEquiv_orbit, Option.map_some]
    exact congrArg some (C.conjugation d z)

end Representation.QuadraticFourGroup.Burnside

end
