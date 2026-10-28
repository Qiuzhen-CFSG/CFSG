module

public import CFSG.Quasithin.MainConverse.EvenClassicalSections.LinearThree.Exhaustion.SimpleCore.Reduction
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.MatrixModel

/-!
# The common-center-and-axis groups in Hartley's argument

The parameter `a` represents the actual projective image of `I + a E₀₂`,
conjugated by an element of PSL₃. This is the root group of the conjugated
incident point-line flag. Intersecting it with the group being studied is
equivalent to taking the inverse image in the additive parameter group.
In characteristic two every nonidentity element of this intersection is an
involution. An intersection of order greater than two therefore means two
distinct nonidentity elations with this same center and axis.

These are geometric definitions and elementary matrix facts, not recognition
assumptions. The two recognition arguments separated by this condition remain
to be proved. In particular no list of group models is built into the setup.

Source: R. W. Hartley, *Determination of the ternary collineation groups whose
coefficients lie in the GF(2ⁿ)*, Ann. Math. 27 (1925), 140–158,
doi:10.2307/1967970, Theorem 1 (pp.142–148) and condition B (p.148).
The concrete unitriangular maps are reused from `UnipotentGeometry`.
-/

namespace CFSG.Quasithin.MainConverse.LinearThreeSections.ModelRecognition

open scoped MatrixGroups

open Matrix.PSL3Even

variable (F : Type) [Field F]

/-- The conjugate of the actual one-parameter projective root group. -/
@[expose] public def elationHom (g : PSL(3,F)) : Multiplicative F →* PSL(3,F) :=
  (MulAut.conj g).toMonoidHom.comp ((UnipotentGeometry.projective F).comp (UnipotentGeometry.central F))

/-- Scalar quotienting loses none of the root parameters. -/
public theorem elationHom_injective (g : PSL(3,F)) :
    Function.Injective (elationHom F g) :=
  (MulAut.conj g).injective.comp
    ((UnipotentGeometry.projective_injective F).comp (UnipotentGeometry.central_injective F))

/-- Explicit matrix representative of a root element. -/
public theorem elationHom_apply (g : PSL(3,F)) (a : F) :
    elationHom F g (Multiplicative.ofAdd a) =
      g * UnipotentGeometry.projective F ⟨0, 0, a⟩ * g⁻¹ := rfl

/-- The standard representative fixes the plane `v₂ = 0` pointwise, and its
displacement is always in the line spanned by the first coordinate vector. -/
public theorem standard_elation_displacement (a : F) (v : Fin 3 → F) :
    (UnipotentGeometry.specialLinear F ⟨0, 0, a⟩).val.mulVec v - v =
      (a * v 2) • (![1, 0, 0] : Fin 3 → F) := by
  change (!![1, 0, a; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F).mulVec v - v = _
  ext i
  fin_cases i <;>
    simp [dotProduct, Fin.sum_univ_three]

/-- The full group of elations at the conjugated standard flag, with identity. -/
@[expose] public def elationRoot (g : PSL(3,F)) : Subgroup PSL(3,F) :=
  (elationHom F g).range

/-- The root is the conjugate of the existing concrete unitriangular center. -/
public theorem elationRoot_eq (g : PSL(3,F)) :
    elationRoot F g =
      (UnipotentGeometry.projectiveCenter F).map (MulAut.conj g).toMonoidHom := by
  rw [elationRoot, elationHom, MonoidHom.range_comp, MonoidHom.range_comp]
  rfl

/-- The actual additive parameters for the intersection with `H`. -/
@[expose] public def elationParameters (H : Subgroup PSL(3,F)) (g : PSL(3,F)) :
    Subgroup (Multiplicative F) := H.comap (elationHom F g)

/-- Parameters and the actual root intersection are multiplicatively equivalent. -/
public noncomputable def elationParametersEquiv (H : Subgroup PSL(3,F)) (g : PSL(3,F)) :
    elationParameters F H g ≃* ↥(H ⊓ elationRoot F g) :=
  (Subgroup.equivMapOfInjective _ _ (elationHom_injective F g)).trans
    (MulEquiv.subgroupCongr (by
      rw [elationParameters, Subgroup.map_comap_eq, inf_comm]
      rfl))

/-- The numerical condition is the order of the actual projective subgroup. -/
public theorem card_elationParameters (H : Subgroup PSL(3,F)) (g : PSL(3,F)) :
    Nat.card (elationParameters F H g) = Nat.card ↥(H ⊓ elationRoot F g) :=
  Nat.card_congr (elationParametersEquiv F H g).toEquiv

/-- Nonzero parameters give precisely the nonidentity elements of a root. -/
public theorem elationHom_ne_one_iff (g : PSL(3,F)) (a : F) :
    elationHom F g (Multiplicative.ofAdd a) ≠ 1 ↔ a ≠ 0 := by
  rw [← map_one (elationHom F g), (elationHom_injective F g).ne_iff]
  rfl

/-- Every root element has square one in characteristic two. -/
public theorem elationHom_sq [CharP F 2] (g : PSL(3,F)) (a : F) :
    elationHom F g (Multiplicative.ofAdd a) ^ 2 = 1 := by
  rw [← map_pow]
  have h : (Multiplicative.ofAdd a) ^ 2 = (1 : Multiplicative F) := by
    rw [pow_two]
    change Multiplicative.ofAdd (a + a) = Multiplicative.ofAdd 0
    rw [CharTwo.add_self_eq_zero]
  rw [h, map_one]

/-- Two distinct nonzero parameters constitute Hartley's large-root case.
The equivalent cardinality condition is proved below. -/
@[expose] public def HasThickElationRoot (H : Subgroup PSL(3,F)) : Prop :=
  ∃ (g : PSL(3,F)) (a b : F), a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
    elationHom F g (Multiplicative.ofAdd a) ∈ H ∧
    elationHom F g (Multiplicative.ofAdd b) ∈ H

private theorem two_lt_card_iff_two_ne_one {G : Type*} [Group G] [Finite G] :
    2 < Nat.card G ↔ ∃ a b : G, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  classical
  let := Fintype.ofFinite G
  rw [Nat.card_eq_fintype_card, Fintype.two_lt_card_iff]
  constructor
  · rintro ⟨a, b, c, hab, hac, hbc⟩
    by_cases ha : a = 1
    · exact ⟨b, c, fun h => hab (ha.trans h.symm),
        fun h => hac (ha.trans h.symm), hbc⟩
    by_cases hb : b = 1
    · exact ⟨a, c, ha, fun h => hbc (hb.trans h.symm), hac⟩
    exact ⟨a, b, ha, hb, hab⟩
  · rintro ⟨a, b, ha, hb, hab⟩
    exact ⟨1, a, b, Ne.symm ha, Ne.symm hb, hab⟩

/-- Hartley's threshold is exactly order greater than two, including identity. -/
public theorem hasThickElationRoot_iff [Finite F] (H : Subgroup PSL(3,F)) :
    HasThickElationRoot F H ↔
      ∃ g : PSL(3,F), 2 < Nat.card ↥(H ⊓ elationRoot F g) := by
  constructor
  · rintro ⟨g, a, b, ha, hb, hab, hma, hmb⟩
    refine ⟨g, ?_⟩
    rw [← card_elationParameters, two_lt_card_iff_two_ne_one]
    refine ⟨⟨Multiplicative.ofAdd a, hma⟩, ⟨Multiplicative.ofAdd b, hmb⟩, ?_, ?_, ?_⟩
    · exact fun h => ha (congrArg (fun x => x.val.toAdd) h)
    · exact fun h => hb (congrArg (fun x => x.val.toAdd) h)
    · exact fun h => hab (congrArg (fun x => x.val.toAdd) h)
  · rintro ⟨g, hg⟩
    rw [← card_elationParameters, two_lt_card_iff_two_ne_one] at hg
    obtain ⟨a, b, ha, hb, hab⟩ := hg
    exact ⟨g, a.val.toAdd, b.val.toAdd,
      fun h => ha (Subtype.ext h), fun h => hb (Subtype.ext h),
      fun h => hab (Subtype.ext h), a.property, b.property⟩

/-- The complementary case bounds every actual root intersection. -/
public theorem not_hasThickElationRoot_iff [Finite F] (H : Subgroup PSL(3,F)) :
    ¬ HasThickElationRoot F H ↔
      ∀ g : PSL(3,F), Nat.card ↥(H ⊓ elationRoot F g) ≤ 2 := by
  simp only [hasThickElationRoot_iff, not_exists, not_lt]

end CFSG.Quasithin.MainConverse.LinearThreeSections.ModelRecognition
