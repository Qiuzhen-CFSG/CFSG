module

public import Theory.SpecificGroups.SU3.BorelTorus.EvenCenterAction
public import Theory.SpecificGroups.SU3.EvenTwoRank
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Field
public import Theory.GroupTheory.NormalizedRootCentralizers
/-!
# The full Sylow center and uniform Borel centralizers in PSU₃

Commuting with roots having every possible first coordinate forces the
first coordinate of a central root to vanish. Its second coordinate is
then precisely the additive fixed field. The full Borel acts there by
inverse-norm scalars, so fixing one nonzero coordinate fixes them all.
The field hypotheses retain matrix-field order q² and fixed-field order q.

Source: Aschbacher–Smith, proof of 13.6.6, printed p.927, with
1.1.5(3a), A.2.3–4, and the matrix conventions of Huppert II.10.12.
-/

public section
open Subgroup Matrix BenderSuzuki.External
open scoped Pointwise
namespace BenderSuzuki.MatrixGroups.HermitianForm.NormalizedRootCentralizers
open BorelTorus BorelTorus.EvenCenterAction
variable {E : Type*} [Field E] [Finite E] [CharP E 2] (J : HermitianForm 3 E)
variable {n : ℕ} (hn : 1 < n) (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)

include hn hcard hfixed in
/-- The full center of the Hermitian Heisenberg group is the additive fixed field. -/
theorem coord_center : center (hermitianUnipotentCoord J) = (centralCoord J).range := by
  apply le_antisymm
  · intro z hz
    have hc (a : E) : a * J.conj z.val.1 = z.val.1 * J.conj a := by
      obtain ⟨b, hb⟩ := huppert_II_10_4_trace_surjective J (2 ^ n) hcard hfixed
        (-(a * J.conj a)) (by rw [map_neg, map_mul, J.conj_involutive, mul_comm])
      let w : hermitianUnipotentCoord J := ⟨(a, b), by dsimp only; rw [hb]; ring⟩
      have hw' : w.val.1 = a := rfl
      have he := congrArg (fun t : hermitianUnipotentCoord J => t.val.2)
        (mem_center_iff.mp hz w)
      change w.val.2 + z.val.2 - w.val.1 * J.conj z.val.1 =
        z.val.2 + w.val.2 - z.val.1 * J.conj w.val.1 at he
      rw [hw'] at he
      linear_combination -he
    have ha : J.conj z.val.1 = z.val.1 := by simpa using hc 1
    have hz0 : z.val.1 = 0 := by
      by_contra hnz
      apply J.conj_ne_one_of_card n (by omega) hcard hfixed
      apply RingEquiv.ext
      intro a
      have he := hc a
      rw [ha, mul_comm a] at he
      exact (mul_left_cancel₀ hnz he).symm
    have hb : J.conj z.val.2 = z.val.2 := by
      have hp := z.property
      rw [hz0, zero_mul, add_zero] at hp
      exact (eq_neg_of_add_eq_zero_right hp).trans (CharTwo.neg_eq _)
    exact ⟨.ofAdd ⟨z.val.2, hb⟩, Subtype.ext (Prod.ext hz0.symm rfl)⟩
  · rintro _ ⟨b, rfl⟩
    exact centralCoord_mem_center J b

variable (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
include hn hcard hfixed in
/-- The injective projective root map identifies the entire embedded center. -/
theorem root_center : (center (projectiveRoot J hJ)).map (projectiveRoot J hJ).subtype =
    centralImage J hJ := by
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨w, hw⟩ := z.property
    have hwc : w ∈ center (hermitianUnipotentCoord J) := by
      apply mem_center_iff.mpr
      intro v
      apply EvenInner.root_injective J hJ
      rw [map_mul, map_mul, hw]
      exact congrArg Subtype.val (mem_center_iff.mp hz
        ⟨hermitianUnipotentPSU J hJ v, ⟨v, rfl⟩⟩)
    rw [coord_center J hn hcard hfixed] at hwc
    obtain ⟨b, rfl⟩ := hwc
    exact ⟨b, hw⟩
  · exact centralImage_le_center J hJ

omit [Finite E] [CharP E 2] in
private theorem torus_normalizes_root : projectiveTorus J hJ ≤
    normalizer (projectiveRoot J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  have hc (k : Eˣ) (x : ProjectiveSpecialUnitaryMatrixGroup J)
      (hx : x ∈ projectiveRoot J hJ) :
      hermitianTorusPSU J hJ k * x * (hermitianTorusPSU J hJ k)⁻¹ ∈ projectiveRoot J hJ := by
    obtain ⟨z, rfl⟩ := hx
    rw [EvenInner.projective_torus_action]
    exact ⟨_, rfl⟩
  rintro _ ⟨k, rfl⟩
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · exact hc k x
  · intro hx
    have hh := hc k⁻¹ _ hx
    simpa only [map_inv, inv_inv, inv_mul_cancel_left, mul_inv_cancel_right,
      mul_assoc, inv_mul_cancel, mul_one] using hh

omit [Finite E] in
/-- Every element of the actual PSU Borel acts by a fixed-field scalar. -/
theorem borel_scalar (g : ProjectiveSpecialUnitaryMatrixGroup J)
    (hg : g ∈ projectiveBorel J hJ) :
    ∃ k : Eˣ, ∀ b : Multiplicative (fixedField J),
      g * centralMap J hJ b * g⁻¹ =
        centralMap J hJ (.ofAdd ((inverseNorm J k : fixedField J) * b.toAdd)) := by
  have hx : g ∈ (projectiveRoot J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) * (projectiveTorus J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ (torus_normalizes_root J hJ)]
    exact hg
  obtain ⟨u, hu, t, ⟨k, rfl⟩, rfl⟩ := hx
  refine ⟨k, fun b => ?_⟩
  rw [_root_.mul_inv_rev]
  calc
    _ = u * (hermitianTorusPSU J hJ k * centralMap J hJ b *
        (hermitianTorusPSU J hJ k)⁻¹) * u⁻¹ := by group
    _ = _ := by
      rw [projective_torus_central]
      have hc := mem_centralizer_iff.mp (root_centralizes J hJ hu)
        _ (show centralMap J hJ (.ofAdd ((inverseNorm J k : fixedField J) * b.toAdd)) ∈
          centralImage J hJ from ⟨_, rfl⟩)
      rw [← hc, mul_assoc, mul_inv_cancel, mul_one]

omit [Finite E] in
theorem uniform_centralImage (r : ProjectiveSpecialUnitaryMatrixGroup J)
    (hr : r ∈ centralImage J hJ) (hne : r ≠ 1) :
    projectiveBorel J hJ ⊓ centralizer ({r} : Set _) =
      projectiveBorel J hJ ⊓ centralizer (centralImage J hJ : Set _) := by
  obtain ⟨b, rfl⟩ := hr
  have hb : b.toAdd ≠ 0 := fun he => hne (by rw [show b = 1 from he, map_one])
  apply le_antisymm
  · rintro g ⟨hg, hc⟩
    obtain ⟨k, hk⟩ := borel_scalar J hJ g hg
    have he : centralMap J hJ (.ofAdd ((inverseNorm J k : fixedField J) * b.toAdd)) =
        centralMap J hJ b := by
      rw [← hk b, mem_centralizer_singleton_iff.mp hc, mul_assoc,
        mul_inv_cancel, mul_one]
    have hs : (inverseNorm J k : fixedField J) = 1 := by
      apply mul_right_cancel₀ hb
      simpa only [one_mul, toAdd_ofAdd] using congrArg Multiplicative.toAdd (centralMap_injective J hJ he)
    refine ⟨hg, mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨c, rfl⟩
    have hh := hk c
    rw [hs, one_mul] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · exact inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr ⟨b, rfl⟩))

include hn hcard hfixed in
/-- Uniform centralizers of every nonidentity element of the full root center. -/
theorem uniform (r : ProjectiveSpecialUnitaryMatrixGroup J)
    (hr : r ∈ (center (projectiveRoot J hJ)).map (projectiveRoot J hJ).subtype)
    (hne : r ≠ 1) :
    projectiveBorel J hJ ⊓ centralizer ({r} : Set _) =
      projectiveBorel J hJ ⊓ centralizer
        (((center (projectiveRoot J hJ)).map (projectiveRoot J hJ).subtype : Subgroup _) : Set _) := by
  rw [root_center J hn hcard hfixed hJ] at hr ⊢
  exact uniform_centralImage J hJ r hr hne

include hn hcard hfixed in
/-- This is the full center of the existing actual model Sylow subgroup. -/
theorem rootSylow_center :
    (center (EvenTwoRank.rootSylow J hJ (by omega : 0 < n) hcard hfixed)).map
      ((EvenTwoRank.rootSylow J hJ (by omega : 0 < n) hcard hfixed :
        Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))).subtype =
        centralImage J hJ :=
  root_center J hn hcard hfixed hJ

end BenderSuzuki.MatrixGroups.HermitianForm.NormalizedRootCentralizers
