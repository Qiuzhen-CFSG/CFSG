module

public import Theory.SpecificGroups.SU3.NormalizedRootCentralizers
public import Theory.SpecificGroups.SU3.EvenSemilinear.Coordinates
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison
public import Theory.GroupTheory.PGroup.OmegaAmbient
public import Theory.GroupTheory.PGroup.OmegaImage

/-!
# First omega subgroups of binary SU₃ and PSU₃ Sylow subgroups

In Hermitian Heisenberg coordinates, the square-one elements are exactly
those with zero first coordinate. The center calculation identifies that
layer with the additive fixed field, of order q. Sylow conjugacy transports
this calculation to every projective Sylow subgroup. The actual SU₃ → PSU₃
map restricts to an isomorphism on each Sylow two-subgroup: its scalar kernel
has exponent three. Thus the special group itself has the same Sylow omega
and center geometry, including when its center is nontrivial.

The special-unitary carrier here is literally `J.specialSubgroup`.
Both field cardinalities and the antidiagonal Gram matrix are retained.
Source: GLS, Volume 4, Chapter 4, Lemma 3.2(b), and its use for SU₃
in Chapter 2, Section 16; root coordinates from Huppert II.10.12.
-/

open Subgroup BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.SylowOmega
open BorelTorus BorelTorus.EvenCenterAction

variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
  {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2 ^ n) ^ 2)
  (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)

include hcard in
private theorem charTwo : CharP E 2 := by
  let := Fintype.ofFinite E
  apply charP_of_card_eq_prime_pow (p := 2) (f := n * 2)
  simpa [Nat.card_eq_fintype_card, pow_mul] using hcard

include hn hcard hfixed in
private theorem coord_square_iff_center [CharP E 2] (x : hermitianUnipotentCoord J) :
    x ^ 2 = 1 ↔ x ∈ center (hermitianUnipotentCoord J) := by
  rw [EvenSemilinear.square_eq_one_iff_first_zero,
    NormalizedRootCentralizers.coord_center J hn hcard hfixed]
  constructor
  · intro hx
    have hb : J.conj x.val.2 = x.val.2 := by
      have hp := x.property
      rw [hx, zero_mul, add_zero] at hp
      exact (eq_neg_of_add_eq_zero_right hp).trans (CharTwo.neg_eq _)
    exact ⟨.ofAdd ⟨x.val.2, hb⟩, Subtype.ext (Prod.ext hx.symm rfl)⟩
  · rintro ⟨b, rfl⟩
    rfl

private noncomputable def coordCenterEquiv [CharP E 2] :
    center (hermitianUnipotentCoord J) ≃* Multiplicative (fixedField J) :=
  (MulEquiv.subgroupCongr (NormalizedRootCentralizers.coord_center J hn hcard hfixed)).trans
    (MonoidHom.ofInjective (centralCoord_injective J)).symm

private theorem square_iff_center_of_equiv
    {H K : Type*} [Group H] [Group K] (e : H ≃* K)
    (hK : ∀ x : K, x ^ 2 = 1 ↔ x ∈ center K) (x : H) :
    x ^ 2 = 1 ↔ x ∈ center H := by
  have hsq : x ^ 2 = 1 ↔ (e x) ^ 2 = 1 := by
    rw [← map_pow, ← e.map_one, e.injective.eq_iff]
  rw [hsq, hK]
  constructor
  · intro hx
    have hh := ((centerCongr e).symm ⟨e x, hx⟩).property
    change e.symm (e x) ∈ center H at hh
    simpa only [e.symm_apply_apply] using hh
  · intro hx
    exact (centerCongr e ⟨x, hx⟩).property

include hn hcard hfixed in
private theorem omega_data_of_equiv
    {G : Type*} [Group G] (P : Subgroup G) (e : P ≃* hermitianUnipotentCoord J) :
    omegaOneAmbient P = (center P).map P.subtype ∧
      IsElementaryAbelian 2 (omegaOneAmbient P) ∧
      Nat.card (omegaOneAmbient P) = 2 ^ n := by
  let : CharP E 2 := charTwo hcard
  have hs := square_iff_center_of_equiv e (coord_square_iff_center J hn hcard hfixed)
  have he : omegaOneAmbient P = (center P).map P.subtype := by
    apply le_antisymm
    · apply (omegaOneAmbient_le_iff _ _).mpr
      intro x hx hp
      exact ⟨⟨x, hx⟩, (hs _).mp (Subtype.ext hp), rfl⟩
    · rintro x ⟨y, hy, rfl⟩
      apply (omegaOneAmbient_le_iff _ _).mp le_rfl _ y.property
      exact congrArg Subtype.val ((hs y).mpr hy)
  refine ⟨he, ?_, ?_⟩
  · let : IsElementaryAbelian 2 (center P) := {
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
        (fun x => Subtype.ext ((hs x.val).mpr x.property)) }
    rw [he]
    exact IsElementaryAbelian.map _
  · rw [he, card_map_of_injective P.subtype_injective,
      Nat.card_congr (centerCongr e).toEquiv,
      Nat.card_congr (coordCenterEquiv J hn hcard hfixed).toEquiv,
      Nat.card_congr Multiplicative.toAdd]
    exact hfixed

variable (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

private instance : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

/-- Every actual projective Sylow group has the Hermitian root coordinates. -/
public noncomputable def projectiveSylowEquivCoords
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    P ≃* hermitianUnipotentCoord J :=
  (P.equiv (EvenTwoRank.rootSylow J hJ (by omega) hcard hfixed)).trans
    (MonoidHom.ofInjective (EvenInner.root_injective J hJ)).symm

omit [Finite E] in
/-- The scalar projection is injective on every special-unitary Sylow two-subgroup. -/
public theorem specialProjection_injective_on_sylow (P : Sylow 2 J.specialSubgroup) :
    Function.Injective (J.specialToProjective.comp (P : Subgroup _).subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  have h3 : IsPGroup 3 J.specialToProjective.ker :=
    fun y => ⟨1, by simpa using J.specialToProjective_ker_cube y⟩
  have hd := P.isPGroup'.disjoint_of_coprime h3 (by decide : Nat.Coprime 2 3)
  apply Subtype.ext
  exact Subgroup.disjoint_def.mp hd x.property hx

/-- The actual scalar projection identifies a Sylow group with its projective image. -/
public noncomputable def specialSylowEquivProjective (P : Sylow 2 J.specialSubgroup) :
    P ≃* (P.mapSurjective J.specialToProjective_surjective : Sylow 2
      (ProjectiveSpecialUnitaryMatrixGroup J)) :=
  (MonoidHom.ofInjective (specialProjection_injective_on_sylow J P)).trans
    (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, Subgroup.range_subtype]; rfl))

/-- The Sylow isomorphism uses the literal scalar projection. -/
public theorem specialSylowEquivProjective_apply (P : Sylow 2 J.specialSubgroup) (x : P) :
    (specialSylowEquivProjective J P x : ProjectiveSpecialUnitaryMatrixGroup J) =
      J.specialToProjective x := by rfl

/-- First omega subgroups match under the actual special-to-projective map. -/
public theorem special_sylow_omega_map (P : Sylow 2 J.specialSubgroup) :
    (omegaOneAmbient (P : Subgroup J.specialSubgroup)).map J.specialToProjective =
      omegaOneAmbient
        (P.mapSurjective J.specialToProjective_surjective :
          Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  let Q := P.mapSurjective J.specialToProjective_surjective
  let e := specialSylowEquivProjective J P
  have he : (Q : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype.comp e.toMonoidHom =
      J.specialToProjective.comp (P : Subgroup J.specialSubgroup).subtype := by
    ext x
    rfl
  change ((omega₁ P (p := 2)).map (P : Subgroup J.specialSubgroup).subtype).map
    J.specialToProjective =
      (omega₁ Q (p := 2)).map (Q : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype
  have hw : (omega₁ P (p := 2)).map e.toMonoidHom = omega₁ Q (p := 2) :=
    e.map_omega 2 1
  rw [← hw, map_map, map_map, he]

include hn hcard hfixed hJ in
/-- Omega, center, elementary abelianness and exact order for every PSU₃ Sylow group. -/
public theorem projective_sylow_omega
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    omegaOneAmbient (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) =
        (center P).map (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype ∧
      IsElementaryAbelian 2 (omegaOneAmbient (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))) ∧
      Nat.card (omegaOneAmbient (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))) = 2 ^ n :=
  omega_data_of_equiv J hn hcard hfixed (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (projectiveSylowEquivCoords J hn hcard hfixed hJ P)

include hn hcard hfixed hJ in
/-- Omega, center, elementary abelianness and exact order for every SU₃ Sylow group. -/
public theorem special_sylow_omega (P : Sylow 2 J.specialSubgroup) :
    omegaOneAmbient (P : Subgroup J.specialSubgroup) =
        (center P).map (P : Subgroup J.specialSubgroup).subtype ∧
      IsElementaryAbelian 2 (omegaOneAmbient (P : Subgroup J.specialSubgroup)) ∧
      Nat.card (omegaOneAmbient (P : Subgroup J.specialSubgroup)) = 2 ^ n :=
  omega_data_of_equiv J hn hcard hfixed (P : Subgroup J.specialSubgroup)
    ((specialSylowEquivProjective J P).trans
      (projectiveSylowEquivCoords J hn hcard hfixed hJ _))

variable {G : Type*} [Group G] [Finite G]

include hn hcard hfixed hJ in
/-- The same conclusions in a group actually isomorphic to the projective model. -/
public theorem omega_of_projective_equiv (e : G ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (P : Sylow 2 G) :
    omegaOneAmbient (P : Subgroup G) = (center P).map (P : Subgroup G).subtype ∧
      IsElementaryAbelian 2 (omegaOneAmbient (P : Subgroup G)) ∧
      Nat.card (omegaOneAmbient (P : Subgroup G)) = 2 ^ n := by
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  exact omega_data_of_equiv J hn hcard hfixed (P : Subgroup G)
    (((P : Subgroup G).equivMapOfInjective e.toMonoidHom e.injective).trans
      (projectiveSylowEquivCoords J hn hcard hfixed hJ Q))

include hn hcard hfixed hJ in
/-- The same conclusions in a group actually isomorphic to the special model. -/
public theorem omega_of_special_equiv (e : G ≃* J.specialSubgroup) (P : Sylow 2 G) :
    omegaOneAmbient (P : Subgroup G) = (center P).map (P : Subgroup G).subtype ∧
      IsElementaryAbelian 2 (omegaOneAmbient (P : Subgroup G)) ∧
      Nat.card (omegaOneAmbient (P : Subgroup G)) = 2 ^ n := by
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  exact omega_data_of_equiv J hn hcard hfixed (P : Subgroup G)
    ((((P : Subgroup G).equivMapOfInjective e.toMonoidHom e.injective).trans
      (specialSylowEquivProjective J Q)).trans
        (projectiveSylowEquivCoords J hn hcard hfixed hJ _))

end BenderSuzuki.MatrixGroups.HermitianForm.SylowOmega
