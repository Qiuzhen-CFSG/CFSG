module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointRadicalSpecial
public import Theory.GroupTheory.SylowFrattiniBounds


/-!
# Frattini generators of the binary unitary-four Sylow subgroup

The standard Sylow subgroup consists of the Hermitian Heisenberg radical
and the middle fixed-field transvections. Every homomorphism to an abelian
group kills the radical center. Conjugation by one middle transvection then
kills the first horizontal coordinate. Thus every element in the abelian
image has a representative with one full-field coordinate and one fixed-field
coordinate, bounding the Frattini quotient by their cardinality product.
Conjugacy transports this bound to every Sylow two-subgroup.

The PSU₄(4) instance supplies the model input to the original residual
inner-action argument in Aschbacher--Smith 4.4.10, printed p.621, using the
unitary flag and radical conventions of F.1.12(I)(6), printed pp.263--264.
-/

open Matrix BenderSuzuki.MatrixGroups Subgroup
open scoped IsMulCommutative commutatorElement
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointLocal
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointQuotient
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow
public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.Frattini
variable (F : Type*) [Field F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "R" => radical F σ hσ
local notation "U" => localUpper F σ hσ
local notation "κ" => coordinatesOfRadical F σ hσ

private def radicalInclusion : R →* U := inclusion (radical_le_localUpper F σ hσ)

private def shear (t : FixedBy.subfield F σ) : U :=
  ⟨leviSL F σ hσ (SpecialLinearGroup.transvection zero_ne_one t), by
    change middleSL F σ hσ _ ∈ SpecialLinearGroup.upperUnipotent _
    rw [middleSL_leviSL]
    exact ⟨Multiplicative.ofAdd t, rfl⟩⟩

private def rootY (y : F) : R := radicalOfCoordinates F σ hσ ⟨0,y,0,by simp⟩

private theorem coord_mul (a b : R) :
    (κ (a*b)).x = (κ a).x + (κ b).x ∧
    (κ (a*b)).y = (κ a).y + (κ b).y := by
  obtain ⟨c, rfl⟩ := (radicalCoordinatesEquiv F σ hσ).surjective a
  obtain ⟨d, rfl⟩ := (radicalCoordinatesEquiv F σ hσ).surjective b
  exact ⟨(radical_mul_coordinates F σ hσ c d).1,
    (radical_mul_coordinates F σ hσ c d).2.1⟩

private def horizontal : R →* Multiplicative (F × F) where
  toFun a := Multiplicative.ofAdd ((κ a).x, (κ a).y)
  map_one' := by
    change Multiplicative.ofAdd ((κ 1).x, (κ 1).y) = 1
    simp [coordinatesOfRadical]
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    exact Prod.ext (coord_mul F σ hσ a b).1 (coord_mul F σ hσ a b).2

private theorem horizontal_surjective : Function.Surjective (horizontal F σ hσ) := by
  intro v
  refine ⟨radicalOfCoordinates F σ hσ
    ((radicalParametersEquiv F σ hσ).symm (v.toAdd.1, v.toAdd.2, 0)), ?_⟩
  rfl

private theorem image_radical {A : Type*} [CommGroup A] (φ : U →* A)
    (hnt : ∃ u, σ u ≠ u) (r : R) :
    φ (radicalInclusion F σ hσ r) =
      φ (radicalInclusion F σ hσ (rootY F σ hσ (κ r).y)) := by
  let γ := φ.comp (radicalInclusion F σ hσ)
  have hker : (horizontal F σ hσ).ker ≤ γ.ker := by
    intro a ha
    have hxy : (κ a).x = 0 ∧ (κ a).y = 0 := by
      have hh : ((κ a).x, (κ a).y) = (0,0) :=
        congrArg Multiplicative.toAdd ha
      exact ⟨congrArg Prod.fst hh, congrArg Prod.snd hh⟩
    obtain ⟨b,c,rfl⟩ := center_radical_exists_commutator F σ hσ hnt a
      ((mem_center_radical_iff F σ hσ hnt a).mpr hxy)
    change γ ⁅b,c⁆ = 1
    rw [map_commutatorElement]
    exact (Commute.all _ _).commutator_eq
  let δ : Multiplicative (F × F) →* A :=
    (horizontal F σ hσ).liftOfSurjective (horizontal_surjective F σ hσ) ⟨γ,hker⟩
  have hδ (a : R) : δ (horizontal F σ hσ a) = γ a := by simp [δ]
  have hx (x : F) : δ (Multiplicative.ofAdd (x,0)) = 1 := by
    let c : RadicalCoordinates F σ := ⟨0,x,0,by simp⟩
    let b := (middleEquivSL F σ hσ).symm
      (SpecialLinearGroup.transvection zero_ne_one (1 : FixedBy.subfield F σ))
    let r1 := leviConjugate F σ hσ b c
    have hr1 : horizontal F σ hσ r1 = Multiplicative.ofAdd (x,x) := by
      have hh := leviSL_conjugation_coordinates F σ hσ
        (SpecialLinearGroup.transvection zero_ne_one (1 : FixedBy.subfield F σ)) c
      apply Multiplicative.toAdd.injective
      apply Prod.ext
      · simpa [horizontal, r1, b, c, SpecialLinearGroup.transvection_coe] using hh.1
      · simpa [horizontal, r1, b, c, SpecialLinearGroup.transvection_coe] using hh.2.1
    have hr0 : horizontal F σ hσ (rootY F σ hσ x) = Multiplicative.ofAdd (0,x) := rfl
    have he : δ (Multiplicative.ofAdd (x,x)) = δ (Multiplicative.ofAdd (0,x)) := by
      rw [← hr1, ← hr0, hδ, hδ]
      change φ (shear F σ hσ 1 * radicalInclusion F σ hσ (rootY F σ hσ x) *
        (shear F σ hσ 1)⁻¹) = _
      simp [γ]
    have heq : (Multiplicative.ofAdd (x,x) : Multiplicative (F × F)) =
        Multiplicative.ofAdd (x,0) * Multiplicative.ofAdd (0,x) := by
      apply Multiplicative.toAdd.injective
      simp
    rw [heq, map_mul] at he
    exact mul_right_cancel (he.trans (one_mul _).symm)
  change γ r = γ (rootY F σ hσ (κ r).y)
  rw [← hδ, ← hδ]
  change δ (Multiplicative.ofAdd ((κ r).x, (κ r).y)) =
    δ (Multiplicative.ofAdd (0,(κ r).y))
  have heq : (Multiplicative.ofAdd ((κ r).x, (κ r).y) : Multiplicative (F × F)) =
      Multiplicative.ofAdd ((κ r).x,0) * Multiplicative.ofAdd (0,(κ r).y) := by
    apply Multiplicative.toAdd.injective
    simp
  rw [heq, map_mul, hx, one_mul]

private theorem image_representative {A : Type*} [CommGroup A] (φ : U →* A)
    (hnt : ∃ u, σ u ≠ u) (u : U) :
    ∃ y : F, ∃ t : FixedBy.subfield F σ,
      φ u = φ (radicalInclusion F σ hσ (rootY F σ hσ y)) * φ (shear F σ hσ t) := by
  obtain ⟨t, ht⟩ := (SpecialLinearGroup.mem_upperUnipotent _ _).mp u.property
  let r : R := ⟨u.val * (shear F σ hσ t).val⁻¹, by
    rw [← middleSL_ker]
    change middleSL F σ hσ (u.val * _) = 1
    rw [map_mul, map_inv]
    change middleSL F σ hσ u.val *
      (middleSL F σ hσ (leviSL F σ hσ _))⁻¹ = 1
    rw [middleSL_leviSL, ht, mul_inv_cancel]⟩
  have hu : u = radicalInclusion F σ hσ r * shear F σ hσ t := by
    apply Subtype.ext
    change u.val = (u.val * (shear F σ hσ t).val⁻¹) * (shear F σ hσ t).val
    group
  refine ⟨(κ r).y,t,?_⟩
  rw [hu, map_mul, image_radical F σ hσ φ hnt r]

/-- The elementary Frattini quotient needs only one full-field root and the
middle fixed-field root. -/
theorem local_frattini_card_le [Finite F] (hnt : ∃ u, σ u ≠ u) :
    Nat.card (U ⧸ frattini U) ≤ Nat.card F * Nat.card (FixedBy.subfield F σ) := by
  let : Fact (IsPGroup 2 U) := ⟨(localSylow F σ hσ).isPGroup'⟩
  let : IsElementaryAbelian 2 (U ⧸ frattini U) := isElementaryAbelian_quotient_frattini
  let φ := QuotientGroup.mk' (frattini U)
  let f : F × FixedBy.subfield F σ → U ⧸ frattini U := fun p =>
    φ (radicalInclusion F σ hσ (rootY F σ hσ p.1)) * φ (shear F σ hσ p.2)
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (frattini U) z
    obtain ⟨y,t,ht⟩ := image_representative F σ hσ φ hnt u
    exact ⟨(y,t),ht.symm⟩
  simpa only [Nat.card_prod] using Nat.card_le_card_of_surjective f hf

/-- The same bound holds for every Sylow two-subgroup of the standard
special unitary group. -/
theorem sylow_frattini_card_le [Finite F] (hnt : ∃ u, σ u ≠ u)
    (P : Sylow 2 (SU F (form F σ hσ))) :
    Nat.card (P ⧸ frattini P) ≤ Nat.card F * Nat.card (FixedBy.subfield F σ) := by
  let e : U ≃* upper F σ hσ :=
    (localUpper F σ hσ).equivMapOfInjective (localSU F (form F σ hσ)).subtype
      (localSU F (form F σ hσ)).subtype_injective
  calc
    Nat.card (P ⧸ frattini P) =
        Nat.card (sylow F σ hσ ⧸ frattini (sylow F σ hσ)) :=
      Theory.GroupTheory.SylowFrattiniBounds.card_congr (Sylow.equiv P (sylow F σ hσ))
    _ = Nat.card (U ⧸ frattini U) :=
      Theory.GroupTheory.SylowFrattiniBounds.card_congr e.symm
    _ ≤ _ := local_frattini_card_le F σ hσ hnt

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.Frattini
