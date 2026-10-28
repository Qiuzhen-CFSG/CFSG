/-
Copyright (c) 2026 Gerald Höhn and ATLAS contributors. All rights reserved.
Uses the ATLAS deleted-eight construction and Siegel factorizations, adapted
from revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.BinaryMaps
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.ReflectionGeneration.SiegelReflections
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple


/-!
# The alternating deleted-eight image is the Siegel-generated Omega group

On the deleted eight-point quadratic module, each nonsingular reflection is an
actual coordinate transposition. The Siegel factorization therefore puts the
whole elementary group inside the alternating image. Conjugation covariance
makes the elementary group normal in the full isometry group. A concrete
nonidentity Siegel transformation and the simplicity of A₈ then give equality.
No order computation or identification with an abstract commutator group is used.

Source: Aschbacher--Smith, H.15.2(2), printed pp.398--399. The deleted module,
its split coordinates and the Siegel factorization are the licensed ATLAS ports
imported above. This binary argument replaces the general Dickson-character
route in `Atlas/Comparisons/Exceptional/Order20160A8.lean`.
-/

open ClassicalOrthogonal ClassicalOrthogonal.Quadratic
open ClassicalOrthogonal.ReflectionGeneration Atlas.Codes
noncomputable section
namespace Atlas.Order20160A8.DeletedEight
private abbrev Q := formD 3 Bit
/-- The 28 nonsingular vectors are exactly the duads modulo the constant word.
The finite certificate only tests the 64 vectors of the split six-space. -/
private theorem coverage (v : D) (hv : Q v ≠ 0) :
    ∃ i j : Fin 8, i ≠ j ∧ splitIsometry v = (Submodule.Quotient.mk (duad i j) : W) := by
  have h : ∀ v : D, Q v ≠ 0 → ∃ i j : Fin 8, i ≠ j ∧
      raw v = duadVector i j + (duadVector i j 7) • (fun _ => 1) := by
    decide +kernel
  obtain ⟨i, j, hij, hv⟩ := h v hv
  refine ⟨i, j, hij, ?_⟩
  change (Submodule.Quotient.mk (intoEven v) : W) = Submodule.Quotient.mk (duad i j)
  apply (Submodule.Quotient.eq constants).mpr
  apply Submodule.mem_span_singleton.mpr
  refine ⟨duadVector i j 7, ?_⟩
  apply Subtype.ext
  change (duadVector i j 7) • (fun _ => (1 : Bit)) = raw v - duadVector i j
  rw [hv, add_sub_cancel_left]

private theorem polar_mk (x y : evenCode) :
    quotientQuadratic.polarBilin (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      binaryDot x.val y.val := by
  change quadratic.polarBilin x y = _
  exact HalfWeight.binaryHalfWeightQuadratic_polar _ _ _ _

private theorem polar_duad (x : evenCode) (i j : Fin 8) :
    quotientQuadratic.polarBilin (Submodule.Quotient.mk x)
      (Submodule.Quotient.mk (duad i j)) = x.val i + x.val j := by
  rw [polar_mk]
  simp [duad, duadVector, binaryDot_apply, mul_add, Finset.sum_add_distrib,
    Pi.single_apply, mul_ite]

private theorem swap_action (x : evenCode) (i j : Fin 8) (hij : i ≠ j) :
    evenPerm (Equiv.swap i j) x = x - (x.val i + x.val j) • duad i j := by
  ext k
  by_cases hi : k = i
  · subst k
    simp [evenPerm, duad, duadVector, Equiv.swap_apply_left, hij]
  by_cases hj : k = j
  · subst k
    simp [evenPerm, duad, duadVector, Equiv.swap_apply_right, Ne.symm hij]
  · simp [evenPerm, duad, duadVector, Equiv.swap_apply_of_ne_of_ne hi hj,
      hi, hj]

private theorem orthogonal_action (p : Equiv.Perm (Fin 8)) (x : D) :
    splitIsometry ((orthogonalHom p).val x) = quotientPerm p (splitIsometry x) :=
  splitIsometry.apply_symm_apply _

/-- Reflections in nonsingular vectors are the actual transpositions of the
underlying eight coordinates. -/
private theorem reflection_swap (v : D) (hv : Q v ≠ 0) :
    ∃ i j : Fin 8, i ≠ j ∧ reflectionElement Q v hv = orthogonalHom (Equiv.swap i j) := by
  obtain ⟨i, j, hij, he⟩ := coverage v hv
  refine ⟨i, j, hij, ?_⟩
  have hv1 : Q v = 1 := (bit_cases (Q v)).resolve_left hv
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply splitIsometry.injective
  change splitIsometry (reflectionLinear Q v hv x) =
    splitIsometry ((orthogonalHom (Equiv.swap i j)).val x)
  rw [orthogonal_action]
  rw [reflectionLinear_apply, map_sub, map_smul, hv1, inv_one, one_mul, he]
  have hb : Q.polarBilin x v = (raw x i + raw x j) := by
    rw [← isometry_between_polar Q quotientQuadratic splitIsometry x v, he]
    exact polar_duad (intoEven x) i j
  rw [hb]
  change constants.mkQ (intoEven x) - (raw x i + raw x j) • constants.mkQ (duad i j) =
    constants.mkQ (evenPerm (Equiv.swap i j) (intoEven x))
  rw [swap_action _ _ _ hij, map_sub, map_smul]
  rfl

private abbrev altImage := (alternatingGroup (Fin 8)).map orthogonalHom

private theorem reflection_pair_mem (v w : D) (hv : Q v ≠ 0) (hw : Q w ≠ 0) :
    reflectionElement Q v hv * reflectionElement Q w hw ∈ altImage := by
  obtain ⟨i, j, hij, hi⟩ := reflection_swap v hv
  obtain ⟨k, l, hkl, hk⟩ := reflection_swap w hw
  rw [hi, hk, ← map_mul]
  apply Subgroup.mem_map.mpr
  refine ⟨Equiv.swap i j * Equiv.swap k l, ?_, rfl⟩
  apply Equiv.Perm.mem_alternatingGroup.mpr
  simp [map_mul, Equiv.Perm.sign_swap hij, Equiv.Perm.sign_swap hkl]

private theorem anisotropic_mem (u v : D) (hu : Q u = 0) (huv : Q.polarBilin u v = 0)
    (hv : Q v ≠ 0) : siegelElement Q u v hu huv ∈ altImage := by
  rw [siegelElement_reflection_factor Q u v hu huv hv]
  apply reflection_pair_mem

/-- A nonsingular Siegel parameter gives two reflections; a singular parameter
splits into two nonsingular perpendicular parameters, giving four reflections. -/
private theorem elementary_le : elementarySubgroup Q ≤ altImage := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨u, v, hu, huv, rfl⟩
  by_cases hv : Q v = 0
  · obtain ⟨w₁, w₂, he, h₁, h₂, hu₁, hu₂⟩ :=
      isotropic_parameter_anisotropic_sum_stable Q polarD_nondegenerate
        (by simp [VectorD, Index]) u v hv huv
    have hs : siegelElement Q u v hu huv =
        siegelElement Q u w₁ hu hu₁ * siegelElement Q u w₂ hu hu₂ := by
      rw [siegelElement_add]
      simp only [he]
    rw [hs]
    exact altImage.mul_mem (anisotropic_mem u w₁ hu hu₁ h₁) (anisotropic_mem u w₂ hu hu₂ h₂)
  · exact anisotropic_mem u v hu huv hv

/-- Conjugation by any quadratic isometry sends a Siegel generator to a Siegel
generator, so normality is in the full isometry group. -/
private theorem elementary_normal : (elementarySubgroup Q).Normal where
  conj_mem g hg k := by
    change g ∈ Subgroup.closure _ at hg
    refine Subgroup.closure_induction (fun z hz => ?_) ?_
      (fun x y _ _ hx hy => ?_) (fun x _ hx => ?_) hg
    · obtain ⟨u, v, hu, huv, rfl⟩ := hz
      let K := Atlas.Order20160A8.isometryCarrierEquiv Q k
      have hu' : Q (K u) = 0 := (K.map_app u).trans hu
      have huv' : Q.polarBilin (K u) (K v) = 0 := (isometry_polar Q K u v).trans huv
      have he : k * siegelElement Q u v hu huv * k⁻¹ =
          siegelElement Q (K u) (K v) hu' huv' := by
        apply Subtype.ext
        apply LinearEquiv.ext
        intro x
        change K (siegel Q u v (K.symm x)) = siegel Q (K u) (K v) x
        rw [siegel_covariant, K.apply_symm_apply]
      rw [he]
      exact siegelElement_mem Q (K u) (K v) hu' huv'
    · simp
    · rw [← conj_mul]
      exact (elementarySubgroup Q).mul_mem hx hy
    · rw [← conj_inv]
      exact (elementarySubgroup Q).inv_mem hx

private theorem elementary_nontrivial : ∃ g ∈ elementarySubgroup Q, g ≠ 1 := by
  let u : D := Pi.single (.inl 0) 1
  let v : D := Pi.single (.inl 1) 1
  have hu : Q u = 0 := by decide +kernel
  have huv : Q.polarBilin u v = 0 := by decide +kernel
  refine ⟨siegelElement Q u v hu huv, siegelElement_mem Q u v hu huv, ?_⟩
  intro he
  have hh := congrArg (fun g : O_DPlus 3 Bit => g.val (Pi.single (.inr 0) 1) (.inl 1)) he
  have hn : siegel Q u v (Pi.single (.inr 0) 1) (.inl 1) ≠ (0 : Bit) := by decide +kernel
  exact hn hh

/-- The actual alternating deleted-eight image is exactly the subgroup of the
full split isometry group generated by Siegel transformations. -/
public theorem alternatingImage_eq_elementary :
    (alternatingGroup (Fin 8)).map orthogonalHom =
      elementarySubgroup (formD 3 (ZMod 2)) := by
  change altImage = elementarySubgroup Q
  apply le_antisymm ?_ elementary_le
  let f := orthogonalHom.comp (alternatingGroup (Fin 8)).subtype
  let N := (elementarySubgroup Q).comap f
  let : (elementarySubgroup Q).Normal := elementary_normal
  have hn : N = ⊤ := by
    rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top (by simp : 5 ≤ Nat.card (Fin 8))
        (N := N) with hb | ht
    · obtain ⟨g, hg, hg1⟩ := elementary_nontrivial
      obtain ⟨p, hp, rfl⟩ := elementary_le hg
      have hmem : (⟨p, hp⟩ : alternatingGroup (Fin 8)) ∈ N := hg
      rw [hb, Subgroup.mem_bot] at hmem
      have he : p = 1 := congrArg Subtype.val hmem
      exact (hg1 (by rw [he, map_one])).elim
    · exact ht
  rintro g ⟨p, hp, rfl⟩
  have hmem : (⟨p, hp⟩ : alternatingGroup (Fin 8)) ∈ N := by rw [hn]; trivial
  exact hmem
end Atlas.Order20160A8.DeletedEight
