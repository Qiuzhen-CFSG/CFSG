module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Lifting
public import Theory.SpecificGroups.Suzuki.BorelFieldQuotient
public import Theory.SpecificGroups.Suzuki.RootOvoidGeometry
public import Theory.GroupTheory.OddElementLift
public import Theory.GroupTheory.NormalSylowQuotientAction
public import Theory.GroupTheory.SylowNormalizerCommutingFamily

/-!
# The literal Suzuki orbit Borel and its coefficient quotient

For I₀ = ⟨I^T⟩, use B = N_{I₀}(T ∩ I₀). A marked projection from
I₀ to the Suzuki component restricts to the original I/O₂(I) projection
and sends T ∩ I₀ to the standard root group. It therefore sends B into
the standard Borel. Compose with its explicit root-group quotient.

A nontrivial field action on that quotient yields the required movement
as soon as its parameters lift to N_B(T). Extract an odd-order power of
one moved lift. This requires neither an invariant torus nor a two-group
kernel for B → Fˣ, and accommodates the diagonal normalizer in a pair of
components. Construction of the marked orbit and the normalizer lifts
remains separate from this conditional lifting theorem.
Source: Aschbacher--Smith 11.5.6(3), printed pp.780--781.
-/

@[expose] public noncomputable section
open Subgroup
open scoped commutatorElement
open BenderSuzuki BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open BenderSuzuki.MatrixGroups.SuzukiBorelFieldQuotient
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.Suzuki
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- The original component orbit, including the possible pair. -/
def orbit (T : Sylow 2 G) (I : Subgroup G) : Subgroup G :=
  conjugateSpanBy I (T : Subgroup G)

/-- The actual relative normalizer of the orbit's Sylow intersection. -/
def borel (T : Sylow 2 G) (I : Subgroup G) : Subgroup G :=
  orbit T I ⊓ normalizer (((T : Subgroup G) ⊓ orbit T I : Subgroup G) : Set G)

omit [Finite G] in
/-- The ambient definition is the intrinsic Sylow-intersection normalizer. -/
theorem borel_subgroupOf (T : Sylow 2 G) (I : Subgroup G) :
    (borel T I).subgroupOf (orbit T I) =
      normalizer ((T : Subgroup G).subgroupOf (orbit T I) : Set (orbit T I)) := by
  rw [borel, inf_subgroupOf_left, subgroupOf_normalizer_eq inf_le_right,
    inf_subgroupOf_right]

/-- A component projection with its literal quotient restriction and Sylow
marking. Its existence is a mathematical output, not source input. -/
structure OrbitCoordinates (T : Sylow 2 G) (I : Subgroup G) (m : ℕ) where
  component : (I ⧸ pCore 2 I) ≃* SuzukiMatrixGroup m
  quotient : orbit T I →* SuzukiMatrixGroup m
  restriction : ∀ i : I, quotient (inclusion (le_conjugateSpanBy I (T : Subgroup G)) i) =
    component (QuotientGroup.mk' (pCore 2 I) i)
  sylow_image : ((T : Subgroup G).subgroupOf (orbit T I)).map quotient =
    SuzukiRootSubgroup m

namespace OrbitCoordinates
variable {I : Subgroup G} {m : ℕ} (c : OrbitCoordinates T I m) (hm : 0 < m)

omit [Finite G] in
/-- The component projection is surjective, by its original quotient restriction. -/
theorem quotient_surjective : Function.Surjective c.quotient := by
  intro s
  obtain ⟨q, rfl⟩ := c.component.surjective s
  obtain ⟨i, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 I) q
  exact ⟨inclusion (le_conjugateSpanBy I (T : Subgroup G)) i, c.restriction i⟩

omit [Finite G] in
private theorem image_mem_borel (hm : 0 < m) (b : borel T I) :
    c.quotient ⟨b, b.property.1⟩ ∈ SuzukiBorelSubgroup m := by
  rw [← suzukiRootSubgroup_normalizer m hm, ← c.sylow_image]
  apply ((T : Subgroup G).subgroupOf (orbit T I)).le_normalizer_map c.quotient
  apply mem_map_of_mem
  rw [← borel_subgroupOf]
  exact b.property

/-- The map to the standard Borel comes from the same original component projection. -/
def borelMap (hm : 0 < m) : borel T I →* SuzukiBorelSubgroup m :=
  (c.quotient.comp (inclusion inf_le_left)).codRestrict
    (SuzukiBorelSubgroup m) (by intro b; exact image_mem_borel c hm b)

/-- The coefficient quotient kills the actual root group, rather than a chosen torus. -/
def coefficient : borel T I →* (BinaryGaloisField (2 * m + 1))ˣ :=
  (projection m hm).comp (c.borelMap hm)

/-- Sylow-normalizer transport makes the original Borel map onto the
standard Borel, including in the orbit of two components. -/
theorem borelMap_surjective : Function.Surjective (c.borelMap hm) := by
  obtain ⟨P, hP⟩ := NormalSylowQuotientAction.intersection_sylow T (orbit T I)
    (le_normalizer_conjugateSpanBy I (T : Subgroup G))
  have he := P.normalizer_map_surjective c.quotient c.quotient_surjective
  change (normalizer ((P : Subgroup (orbit T I)) : Set (orbit T I))).map c.quotient =
    normalizer ((P : Subgroup (orbit T I)).map c.quotient : Set (SuzukiMatrixGroup m)) at he
  rw [hP, c.sylow_image, suzukiRootSubgroup_normalizer m hm] at he
  intro b
  have hb : (b : SuzukiMatrixGroup m) ∈
      (normalizer ((T : Subgroup G).subgroupOf (orbit T I) : Set (orbit T I))).map
        c.quotient := he.symm ▸ b.property
  obtain ⟨j, hj, heq⟩ := hb
  rw [← borel_subgroupOf] at hj
  exact ⟨⟨j, hj⟩, Subtype.ext heq⟩

/-- Every field unit occurs in the literal orbit Borel quotient. -/
theorem coefficient_surjective : Function.Surjective (c.coefficient hm) :=
  (projection_surjective m hm).comp (c.borelMap_surjective hm)

/-- Exactly the normalizer-lift calculation needed in both component orbits. -/
def NormalizerLifts : Prop :=
  ∀ u : (BinaryGaloisField (2 * m + 1))ˣ,
    ∃ b : borel T I, (b : G) ∈ normalizer (T : Set G) ∧ c.coefficient hm b = u

end OrbitCoordinates

variable {L V : Subgroup G} {D : ChosenModule T L V} {E : Geometry D}
    {I : Subgroup G} {m : ℕ}

/-- The original Cartan actor on the marked Borel quotient. The inner
factor is retained, so no invariant split-torus choice is demanded. -/
structure FieldAction (E : Geometry D) (c : OrbitCoordinates T I m) (hm : 0 < m) where
  actor : normalizer (borel T I : Set G)
  actor_mem : (actor : G) ∈ E.X
  inner : SuzukiBorelSubgroup m
  coefficient : BinaryGaloisField (2 * m + 1) ≃ₐ[ZMod 2] BinaryGaloisField (2 * m + 1)
  nontrivial : coefficient ≠ 1
  action : ∀ b : borel T I,
    c.borelMap hm ((borel T I).normalizerMonoidHom actor b) =
      borelActor m inner coefficient (c.borelMap hm b)

namespace FieldAction
variable {c : OrbitCoordinates T I m} {hm : 0 < m} (a : FieldAction E c hm)

private theorem units_odd : Odd (Nat.card (BinaryGaloisField (2 * m + 1))ˣ) := by
  rw [Nat.card_units, GaloisField.card 2 (2 * m + 1) (by omega)]
  exact Nat.Even.sub_odd (pow_pos (by decide : 0 < (2 : ℕ)) _)
    (even_two.pow_of_ne_zero (by omega)) odd_one

/-- The explicit Borel quotient removes the inner factor of the same actor. -/
theorem coefficient_action (b : borel T I) :
    c.coefficient hm ((borel T I).normalizerMonoidHom a.actor b) =
      Units.map a.coefficient.toRingEquiv.toMonoidHom (c.coefficient hm b) := by
  change projection m hm (c.borelMap hm ((borel T I).normalizerMonoidHom a.actor b)) = _
  rw [a.action, projection_borelActor]
  rfl

include a in
/-- A single moved coefficient has an odd-order lift in the actual
T-normalizer, giving the shared source movement predicate. -/
theorem borel_movement (hIY : orbit T I ≤ E.Y) (hlift : c.NormalizerLifts hm) :
    E.BorelMovement := by
  classical
  by_contra hmove
  apply a.nontrivial
  have hfix (u : (BinaryGaloisField (2 * m + 1))ˣ) :
      Units.map a.coefficient.toRingEquiv.toMonoidHom u = u := by
    obtain ⟨b, hbN, hbu⟩ := hlift u
    obtain ⟨r, hr, hro, hre⟩ := (c.coefficient hm).exists_odd_power_with_image b
      (units_odd.of_dvd_nat (orderOf_dvd_natCard _))
    have hrN : (r : G) ∈ normalizer (T : Set G) := by
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hr
      exact (normalizer (T : Set G)).zpow_mem hbN n
    have hrY : (r : G) ∈ E.Y := hIY r.property.1
    let B : Subgroup G := zpowers (r : G)
    have hBY : B ≤ E.Y := zpowers_le.mpr hrY
    have hBN : B ≤ normalizer (T : Set G) := zpowers_le.mpr hrN
    have hBo : Odd (Nat.card B) := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe r]
      exact hro
    have hcomm : ⁅E.X, B⁆ ≤ (T : Subgroup G) := by
      by_contra hn
      exact hmove ⟨B, hBY, hBN, hBo, hn⟩
    let d : borel T I := (borel T I).normalizerMonoidHom a.actor r * r⁻¹
    have hdT : (d : G) ∈ (T : Subgroup G) :=
      hcomm (commutator_mem_commutator a.actor_mem (mem_zpowers (r : G)))
    obtain ⟨k, hk⟩ := T.isPGroup'.exists_pow_pow_eq_one ⟨d, hdT⟩
    have hdp : d ^ (2 ^ k) = 1 := Subtype.ext (congrArg (fun t : T => (t : G)) hk)
    have hcd : c.coefficient hm d =
        Units.map a.coefficient.toRingEquiv.toMonoidHom u * u⁻¹ := by
      rw [map_mul, map_inv, a.coefficient_action, hre, hbu]
    have hpow : (Units.map a.coefficient.toRingEquiv.toMonoidHom u * u⁻¹) ^ (2 ^ k) = 1 := by
      rw [← hcd, ← map_pow, hdp, map_one]
    exact mul_inv_eq_one.mp (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      (units_odd.coprime_two_left.pow_left k)
      (orderOf_dvd_of_pow_eq_one hpow) (orderOf_dvd_natCard _)))
  ext x
  by_cases hx : x = 0
  · simp [hx]
  · exact congrArg Units.val (hfix (Units.mk0 x hx))

end FieldAction
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.Suzuki
