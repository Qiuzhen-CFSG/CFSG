module
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Layers.CoordinateTransport
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Layers.HexacodeDual.Actions
public import Theory.Mathieu.M24.LocalGeometry.SubnormalSextet.CubicTranslations
public import Theory.Mathieu.M24.LocalGeometry.SextetCore.Hexacode

/-!
# A cubic-fixed cocode commutator witness

Three even words supported on the zero rows of two sextet columns are fixed
by the hexacode scalar. Three even column permutations commute with that
scalar. Their displacements sum, modulo the explicit Golay word eta, to the
common tetrad class. Transport through the actual sextet coordinates retains
both the native M24 operators and the original marker vector.

A normal subgroup of a sextet stabilizer whose order is divisible by three
and prime to five contains this literal scalar: its column image is trivial,
and scalar commutators force all affine translations into the subgroup.
These statements feed FullCubicPerfect, which lifts the witness inside the
original cubic lift and proves the full centralizer perfect in its genuine
marked cocode application.

Source: Aschbacher--Segev, The uniqueness of groups of type J4,
Invent. Math. 105 (1991), (4.9), p.599, DOI 10.1007/BF01232280.
The imported Golay and affine hexacode coordinates are by Gerald Hoehn and
ATLAS contributors, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917,
under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
The three-displacement certificate and its transport are proved here.
-/

@[expose] public section
open Subgroup
open scoped BigOperators
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.CubicWitness
open Atlas.Codes MathieuCode.SextetLayers
noncomputable section

def scalar : SextetStabilizer := sextetSection hexZ

def actor : Fin 3 → SextetStabilizer
  | 0 => sextetSection (hexLift 0 * hexLift 1)
  | 1 => sextetSection (hexLift 2 * hexLift 3)
  | _ => sextetSection (hexLift 4 * hexLift 3)

def word (i : Fin 3) : BinaryWord := fun p =>
  if p.2 = 0 ∧ hexIndexEquiv p.1 ∈ (![({0,3} : Finset (Fin 6)), {2,0}, {5,0}] i)
    then 1 else 0

theorem word_even : ∀ i, word i ∈ AtlasCore := by
  change ∀ i, (∑ p, word i p) = 0
  decide +kernel

def vector (i : Fin 3) : AtlasCore := ⟨word i, word_even i⟩

theorem scalar_cube : scalar ^ 3 = 1 := by
  rw [scalar, ← map_pow, hexZ_cube, map_one]

theorem scalar_ne_one : scalar ≠ 1 := by
  intro he
  have hh := congrArg sextetQuotient he
  rw [scalar, sextetQuotient_section, map_one] at hh
  exact hexZ_ne_one hh

theorem actor_commutes (i : Fin 3) : Commute (actor i) scalar := by
  have hh (j k : Fin 5) : Commute (hexLift j * hexLift k) hexZ := by
    change (hexLift j * hexLift k) * hexZ = hexZ * (hexLift j * hexLift k)
    apply (mul_inv_eq_iff_eq_mul).mp
    calc
      (hexLift j * hexLift k) * hexZ * (hexLift j * hexLift k)⁻¹ =
          hexLift j * (hexLift k * hexZ * (hexLift k)⁻¹) * (hexLift j)⁻¹ := by group
      _ = hexLift j * hexZ⁻¹ * (hexLift j)⁻¹ := by rw [hexLift_inverts]
      _ = (hexLift j * hexZ * (hexLift j)⁻¹)⁻¹ := by group
      _ = hexZ := by rw [hexLift_inverts, inv_inv]
  fin_cases i <;> exact (hh _ _).map sextetSection

theorem vector_fixed (i : Fin 3) : atlasCoreRepresentation scalar (vector i) = vector i := by
  apply Subtype.ext
  funext p
  change word i ((scalar.val.val).symm p) = word i p
  revert i p
  decide +kernel

private theorem displacement_word :
    (∑ i : Fin 3, (atlasCoreRepresentation (actor i) (vector i) - vector i)).val -
      (atlasTetradCore (2,1)).val = eta := by
  funext p
  change (∑ i : Fin 3, (word i ((actor i).val.val.symm p) - word i p)) -
    (if p.1 = (2,1) then 1 else 0) = eta p
  revert p
  decide +kernel

theorem displacement_sum :
    (∑ i : Fin 3, (atlasCocodeRepresentation (actor i) (atlasCodeInCore.mkQ (vector i)) -
      atlasCodeInCore.mkQ (vector i))) = atlasCodeInCore.mkQ (atlasTetradCore (0,0)) := by
  simp_rw [atlasCocodeRepresentation_mk, ←map_sub]
  rw [←map_sum, ←atlasTetradClass_eq (2,1) (0,0)]
  apply (Submodule.Quotient.eq atlasCodeInCore).mpr
  change (∑ i : Fin 3, (atlasCoreRepresentation (actor i) (vector i) - vector i)).val -
    (atlasTetradCore (2,1)).val ∈ golay
  rw [displacement_word]
  exact ⟨(0,0,1), by simp [golayEncoder, c0Encoder]⟩
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open MathieuCode.SextetLayers.CoordinateTransport

def nativeScalar (S : Sextet) : M24 := (nativeStabilizerEquiv S scalar).val

def nativeActor (S : Sextet) (i : Fin 3) : M24 := (nativeStabilizerEquiv S (actor i)).val

def nativeVector (S : Sextet) (i : Fin 3) : Cocode :=
  nativeCocodeEquiv S (atlasCodeInCore.mkQ (vector i))

theorem nativeScalar_order (S : Sextet) : orderOf (nativeScalar S) = 3 := by
  rw [nativeScalar, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  exact orderOf_eq_prime scalar_cube scalar_ne_one

theorem nativeScalar_mem (S : Sextet) : nativeScalar S ∈ sextetStabilizer S :=
  (nativeStabilizerEquiv S scalar).property

theorem nativeActor_mem (S : Sextet) (i : Fin 3) : nativeActor S i ∈ sextetStabilizer S :=
  (nativeStabilizerEquiv S (actor i)).property

theorem nativeActor_commutes (S : Sextet) (i : Fin 3) :
    Commute (nativeActor S i) (nativeScalar S) :=
  ((actor_commutes i).map (nativeStabilizerEquiv S).toMonoidHom).map (sextetStabilizer S).subtype

theorem nativeVector_fixed (S : Sextet) (i : Fin 3) :
    cocodeRepresentation (nativeScalar S) (nativeVector S i) = nativeVector S i := by
  rw [nativeVector, nativeScalar, ←nativeCocodeEquiv_equivariant,
    atlasCocodeRepresentation_mk, vector_fixed]

theorem native_displacement_sum (S : Sextet) :
    (∑ i : Fin 3, (cocodeRepresentation (nativeActor S i) (nativeVector S i) -
      nativeVector S i)) = sextetVector S := by
  simp_rw [nativeActor, nativeVector, ←nativeCocodeEquiv_equivariant, ←map_sub]
  rw [←map_sum, displacement_sum, nativeCocodeEquiv_tetrad]

end
end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.CubicWitness

namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.CubicWitness
open Subgroup Atlas.Codes

/-- A normal subgroup of the sextet stabilizer whose order is divisible by
three and prime to five contains the literal cubic scalar. -/
theorem scalar_mem_normal (A : Subgroup SextetStabilizer) [A.Normal]
    (hthree : 3 ∣ Nat.card A) (hfive : ¬ 5 ∣ Nat.card A) : scalar ∈ A := by
  let B := A.map sextetQuotient
  let : B.Normal := Subgroup.Normal.map inferInstance _ sextetQuotient_surjective
  have hBfive : ¬ 5 ∣ Nat.card B := fun hh => hfive (hh.trans (A.card_map_dvd _))
  have hBthree : 3 ∣ Nat.card B := by
    have hh := (sextetQuotient.comp A.subtype).ker.card_mul_index
    rw [index_ker,MonoidHom.range_comp,range_subtype] at hh
    have hk : Nat.card (sextetQuotient.comp A.subtype).ker ∣ 64 := by
      change Nat.card (sextetQuotient.ker.subgroupOf A) ∣ 64
      rw [←sextetQuotient_kernel_card]
      exact card_comap_dvd_of_injective _ A.subtype A.subtype_injective
    have hn : ¬ 3 ∣ Nat.card (sextetQuotient.comp A.subtype).ker := by
      intro hd
      have : 3 ∣ 64 := hd.trans hk
      norm_num at this
    rw [←hh] at hthree
    exact (Nat.prime_three.dvd_mul.mp hthree).resolve_left hn
  have hBK : B ≤ hexCoordinateSixHom.ker := by
    let C := B.map hexCoordinateSixHom
    let : C.Normal := Subgroup.Normal.map inferInstance _ hexCoordinateSix_surjective
    have hc : C = ⊥ := by
      by_contra hn
      have hnt : Nontrivial C := (Subgroup.nontrivial_iff_ne_bot _).mpr hn
      have hle := Equiv.Perm.alternatingGroup_le_of_normal
        (by simp : 5 ≤ Nat.card (Fin 6)) hnt
      have hd : 5 ∣ Nat.card C :=
        (show 5 ∣ Nat.card (alternatingGroup (Fin 6)) by
          rw [nat_card_alternatingGroup,Nat.card_fin]; decide).trans (card_dvd_of_le hle)
      exact hBfive (hd.trans (B.card_map_dvd _))
    intro b hb
    exact mem_bot.mp (hc ▸ (mem_map_of_mem hexCoordinateSixHom hb))
  have hBeq : B = hexCoordinateSixHom.ker := by
    apply eq_of_le_of_card_ge hBK
    rw [hexCoordinateSix_kernel,Nat.card_zpowers,hexZ_order]
    exact Nat.le_of_dvd Nat.card_pos hBthree
  have hz : hexZ ∈ A.map sextetQuotient := by
    change hexZ ∈ B
    rw [hBeq,hexCoordinateSix_kernel]
    exact mem_zpowers hexZ
  have hker := Sporadic.Mathieu.M24LocalGeometry.SubnormalSextet.translations_le_of_scalar_mem
    A (inferInstance : A.Normal).isSubnormal hz
  obtain ⟨a,ha,he⟩ := hz
  have hk : scalar * a⁻¹ ∈ sextetQuotient.ker := by
    change sextetQuotient (scalar * a⁻¹) = 1
    rw [map_mul,map_inv,he,scalar,sextetQuotient_section,mul_inv_cancel]
  simpa only [inv_mul_cancel_right] using A.mul_mem (hker hk) ha

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open MathieuCode.SextetLayers.CoordinateTransport

theorem nativeScalar_mem_normal (S : Sextet) (A : Subgroup (sextetStabilizer S)) [A.Normal]
    (hthree : 3 ∣ Nat.card A) (hfive : ¬ 5 ∣ Nat.card A) :
    nativeStabilizerEquiv S scalar ∈ A := by
  let e := nativeStabilizerEquiv S
  let B := A.map e.symm.toMonoidHom
  have hc : Nat.card B = Nat.card A := card_map_of_injective e.symm.injective
  let : B.Normal := Subgroup.Normal.map inferInstance _ e.symm.surjective
  have hs := scalar_mem_normal B (by rw [hc]; exact hthree) (by rw [hc]; exact hfive)
  obtain ⟨a,ha,he⟩ := hs
  have he' : a = e scalar := (e.symm_apply_eq).mp he
  rwa [←he']
end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.CubicWitness
