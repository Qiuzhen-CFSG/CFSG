module
public import Theory.SpecificGroups.SU3.NormalizedRootCentralizers
public import Theory.GroupTheory.CenterWeakClosureByDerivedLines

/-!
# The full binary unitary Sylow-center action, including q = 2

The intrinsic center of the Hermitian root group is its upper-right
fixed-field coordinate. Nontriviality of the field involution follows
from the distinct field and fixed-field cardinalities, including the
quadratic field of order four. The inverse-norm torus action is
transitive on nonzero central coordinates. Sylow conjugacy transports
this irreducibility to the center of every Sylow subgroup of the actual
projective special unitary carrier. No simplicity assumption is used.

This is the scalar-action input for the literal center commutator in
Fong--Seitz I (6A)(c). The projective group here is the faithful panel
image; it does not replace the full root-generated SU3 actor.
The companion CenterIrreducibility module applies it before projection
on the same marked quadrangle.

Source: Fong--Seitz I (5C), (6A)(c), pp.26,37;
Huppert II.10.12, with the repository's Hermitian matrix convention.
-/

public noncomputable section
open Subgroup BenderSuzuki.External
open scoped Pointwise
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
open BenderSuzuki.MatrixGroups BenderSuzuki.MatrixGroups.HermitianForm
open BorelTorus BorelTorus.EvenCenterAction
variable {E : Type*} [Field E] [Finite E] [CharP E 2] (J : HermitianForm 3 E)
variable {n : ℕ} (hn : 0 < n) (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
include hn hcard hfixed
omit [Finite E] [CharP E 2] in
private theorem binary_conj_ne_one : J.conj ≠ 1 := by
  intro h
  let e : {z : E // J.conj z = z} ≃ E :=
    { toFun := Subtype.val
      invFun := fun z => ⟨z, by rw [h]; rfl⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have he := Nat.card_congr e
  rw [hcard,hfixed] at he
  have := Nat.one_lt_two_pow (show n ≠ 0 by omega)
  nlinarith

theorem binary_coord_center : center (hermitianUnipotentCoord J) = (centralCoord J).range := by
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
      apply binary_conj_ne_one J hn hcard hfixed
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
theorem binary_root_center : (center (projectiveRoot J hJ)).map (projectiveRoot J hJ).subtype =
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
    rw [binary_coord_center J hn hcard hfixed] at hwc
    obtain ⟨b, rfl⟩ := hwc
    exact ⟨b, hw⟩
  · exact centralImage_le_center J hJ

omit hn hcard hfixed [Finite E] [CharP E 2] in
theorem unitary_torus_normalizes_root : projectiveTorus J hJ ≤
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


include hJ in
/-- A nonzero normalizer-invariant subgroup of a unitary Sylow center is its whole center. -/
theorem unitary_sylow_center_irreducible
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (A : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hA : A ≤ (center S).map (S : Subgroup _).subtype) (hne : A ≠ ⊥)
    (hN : normalizer (S : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ normalizer (A : Set (ProjectiveSpecialUnitaryMatrixGroup J))) :
    A = (center S).map (S : Subgroup _).subtype := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J)
    (EvenTwoRank.rootSylow J hJ hn hcard hfixed) S
  let f := (MulAut.conj g).toMonoidHom
  have hS : (projectiveRoot J hJ).map f = (S : Subgroup _) :=
    congrArg (fun T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J) => T.toSubgroup) hg
  have hZ : (centralImage J hJ).map f = (center S).map (S : Subgroup _).subtype := by
    rw [←hS,map_center_image_of_injective _ f (MulAut.conj g).injective,
      ←map_map,binary_root_center J hn hcard hfixed hJ]
  have hAC : A.comap f ≤ centralImage J hJ := by
    rw [←hZ] at hA
    have hh := comap_mono (f := f) hA
    rwa [comap_map_eq_self_of_injective (MulAut.conj g).injective] at hh
  have hne' : A.comap f ≠ ⊥ := by
    intro hz
    apply hne
    rw [←map_comap_eq_self_of_surjective (f := f) (MulAut.conj g).surjective A,hz,Subgroup.map_bot]
  have hn' : projectiveTorus J hJ ≤ normalizer (A.comap f : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    apply (map_le_map_iff_of_injective (f := f) (MulAut.conj g).injective).mp
    apply le_trans (map_mono (unitary_torus_normalizes_root J hJ))
    rw [map_normalizer_eq_of_bijective _ (MulAut.conj g).bijective,hS,
      map_normalizer_eq_of_bijective _ (MulAut.conj g).bijective,
      map_comap_eq_self_of_surjective (MulAut.conj g).surjective]
    exact hN
  have hh := (central_irreducible J hJ hcard hfixed (A.comap f) hAC hn').resolve_left hne'
  have he := congrArg (Subgroup.map f) hh
  rwa [map_comap_eq_self_of_surjective (MulAut.conj g).surjective,hZ] at he

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
