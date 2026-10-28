module

public import Theory.SpecificGroups.SU3.BorelTorus.EvenCenterAction
public import Theory.SpecificGroups.SU3.BinaryRootFrattini
public import Theory.GroupTheory.Commutator.CentralExtensionPairing

/-!
# Mixed central-root commutators in binary unitary central extensions

In any central extension of PSU₃(q), q even and q > 2, lifts of the central
root group commute with every lift of the root group. Choose a norm-one torus
parameter whose cube is nontrivial. It fixes the central root coordinate;
centrality of the covering kernel then makes its commutators with root lifts
commute with each central-root lift. These commutators cover every first
coordinate, and squares recover the central layer. Thus their images generate
the whole root group, which proves the mixed commutator identity.

Source: Huppert II.10.12 for the coordinates and torus; the defining-primary
multiplier calculation in Aschbacher–Smith I.1.3 (PDF p.418), citing GLS3 §6.1.
This lemma does not assume perfectness or finiteness of the extension group.
-/

public section
open scoped commutatorElement
open Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
open BenderSuzuki.MatrixGroups.HermitianForm
open BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus
open BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus.EvenCenterAction
open BenderSuzuki.MatrixGroups.HermitianForm.EvenInner

namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.EvenKernelBound

/-- The elementary central-extension commutator identity used by the lift. -/
private theorem commute_commutator_of_map_commute
    {E G : Type*} [Group E] [Group G] (f : E →* G)
    (hc : f.ker ≤ center E) {a b c : E}
    (hab : Commute (f a) (f b)) (hac : Commute (f a) (f c)) :
    Commute a ⁅b, c⁆ := by
  have hb : f (a * b * a⁻¹) = f b := by
    rw [map_mul, map_mul, map_inv, hab.eq, mul_inv_cancel_right]
  have hd : f (a * c * a⁻¹) = f c := by
    rw [map_mul, map_mul, map_inv, hac.eq, mul_inv_cancel_right]
  have hh := CentralExtension.commutator_eq_of_image_eq f hc hb hd
  rw [← conjugate_commutatorElement] at hh
  exact mul_inv_eq_iff_eq_mul.mp hh

/-- Every lift of the central root group commutes with every root-group lift.
Both images are taken under the original central extension map. -/
theorem commute_of_central_root_images
    {F : Type*} [Field F] [Finite F] [CharP F 2] (J : HermitianForm 3 F)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {q : ℕ} (hq : 2 < q)
    (hcard : Nat.card F = q ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = q)
    {E : Type*} [Group E] (f : E →* ProjectiveSpecialUnitaryMatrixGroup J)
    (hf : Function.Surjective f) (hker : f.ker ≤ center E)
    (b : Multiplicative (fixedField J)) {x y : E}
    (hx : f x = centralMap J hJ b) (hy : f y ∈ projectiveRoot J hJ) :
    Commute x y := by
  obtain ⟨k, _, hk3, _, hkconj⟩ :=
    BenderSuzuki.External.exists_hermitian_norm_one_torus_cube_ne_one J q
      hcard hfixed hJ hq
  have hinv : inverseNorm J k = 1 := by
    apply Units.ext
    apply Subtype.ext
    rw [inverseNorm_val, hkconj]
    simp
  obtain ⟨t, ht⟩ := hf (hermitianTorusPSU J hJ k)
  let N : Subgroup E := centralizer ({x} : Set E)
  have hfirst : ∀ a : F, ∃ z : hermitianUnipotentCoord J,
      z.val.1 = a ∧ hermitianUnipotentPSU J hJ z ∈ N.map f := by
    intro a
    obtain ⟨z, hzfirst⟩ := BinaryRootFrattini.firstCoordinate_surjective J hcard hfixed
      (Multiplicative.ofAdd (a / ((k : F) ^ 3 - 1)))
    have hzfirst' : z.val.1 = a / ((k : F) ^ 3 - 1) := by
      exact congrArg Multiplicative.toAdd hzfirst
    have hzroot : hermitianUnipotentPSU J hJ z ∈ projectiveRoot J hJ := ⟨z, rfl⟩
    obtain ⟨y, hy⟩ := hf (hermitianUnipotentPSU J hJ z)
    let w := ⁅t, y⁆
    have hxt : Commute (f x) (f t) := by
      apply (commute_iff_eq _ _).mpr
      have hh := projective_torus_central J hJ k b
      rw [hinv] at hh
      have hh' : f t * f x * (f t)⁻¹ =
          f x := by
        rw [ht, hx]
        simpa using hh
      calc
        f x * f t =
            (f t * f x * (f t)⁻¹) *
              f t := by rw [hh']
        _ = f t * f x := by group
    have hxy : Commute (f x) (f y) := by
      apply (commute_iff_eq _ _).mpr
      have hroot := root_centralizes J hJ
      have hzimage : f x ∈ centralImage J hJ := by
        rw [hx]
        exact ⟨b, rfl⟩
      have he := mem_centralizer_iff.mp (hroot hzroot) (f x) hzimage
      rw [← hy] at he
      exact he
    have hwx : Commute x w :=
      commute_commutator_of_map_commute f hker hxt hxy
    have hwN : w ∈ N := by
      apply mem_centralizer_iff.mpr
      intro u hu
      rw [Set.mem_singleton_iff.mp hu]
      exact hwx.eq
    have hwmap : f w = hermitianUnipotentPSU J hJ
        (hermitianTorusAction J k z * z⁻¹) := by
      change f ⁅t, y⁆ = _
      rw [map_commutatorElement, ht, hy, commutatorElement_def,
        EvenInner.projective_torus_action, map_mul, map_inv]
    have hwfirst : (hermitianTorusAction J k z * z⁻¹).val.1 = a := by
      change (hermitianTorusAction J k z).val.1 + -z.val.1 = a
      rw [EvenInner.normOne_action_first J k hkconj, hzfirst']
      field_simp [sub_ne_zero.mpr hk3]
      ring
    refine ⟨hermitianTorusAction J k z * z⁻¹, hwfirst, ?_⟩
    exact ⟨w, hwN, hwmap⟩
  have hrootN : projectiveRoot J hJ ≤ N.map f := by
    change (hermitianUnipotentPSU J hJ).range ≤ _
    exact EvenInner.range_le_of_first_surjective J hcard hfixed
      (hermitianUnipotentPSU J hJ) _ hfirst
  obtain ⟨v, hv, hvf⟩ := hrootN hy
  have hvcomm : Commute x v := (mem_centralizer_iff.mp hv x (by simp))
  apply commutatorElement_eq_one_iff_commute.mp
  rw [CentralExtension.commutator_eq_of_image_eq f hker rfl hvf.symm]
  exact hvcomm.commutator_eq

end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.EvenKernelBound
