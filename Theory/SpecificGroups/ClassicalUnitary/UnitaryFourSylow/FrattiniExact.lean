module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.Frattini
public import Theory.Frattini.SquareImage
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFormTransport

/-!
# Exact Frattini coordinates for binary unitary-four Sylow subgroups

In the standard upper Sylow, the last horizontal matrix coordinate and the
middle transvection parameter form a surjective homomorphism onto the additive
groups of the full field and its fixed subfield. This elementary abelian image
kills the Frattini subgroup. The matching upper bound from the radical
commutator calculation identifies the quotient and its order exactly.

Arbitrary-form transport gives order 2^(3n) for every Sylow two-subgroup of
PSU₄(2ⁿ). Consequently the seven-generator test in the Hall component argument
applies exactly at n≤2; larger parameters need a structural automorphism proof.

Source: Aschbacher--Smith F.1.12(I)(6), printed pp.263--264, and the
Sylow-restriction application in 4.4.10, printed p.621.
-/

open Matrix BenderSuzuki.MatrixGroups Subgroup
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointLocal
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointQuotient
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow
public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.FrattiniExact
variable (F : Type*) [Field F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "U" => localUpper F σ hσ
local notation "K" => FixedBy.subfield F σ

private theorem last_coordinate_mul (a b : U) :
    (a*b).val.val.val.val 2 3 = a.val.val.val.val 2 3 + b.val.val.val.val 2 3 := by
  have ha := (mem_localUpper F σ hσ a.val).mp a.property
  have hb := last_row F σ hσ b.val.val b.val.property
  have ha0 := (mem_localSU F _ a.val.val).mp a.val.property
  change (a.val.val.val.val * b.val.val.val.val) 2 3 = _
  simp [Matrix.mul_apply, Fin.sum_univ_succ, ha.2.1, ha.2.2, hb.2.2.2, ha0.2.2.1, add_comm]

private def lastCoordinate : U →* Multiplicative F where
  toFun a := Multiplicative.ofAdd (a.val.val.val.val 2 3)
  map_one' := by rfl
  map_mul' a b := congrArg Multiplicative.ofAdd (last_coordinate_mul F σ hσ a b)

private def middleCoordinate : U →* Multiplicative K :=
  (MonoidHom.ofInjective (SpecialLinearGroup.upperUnipotentHom_injective K)).symm.toMonoidHom.comp
    (((middleSL F σ hσ).comp (localUpper F σ hσ).subtype).codRestrict (SpecialLinearGroup.upperUnipotent K)
      (fun a => a.property))

private def rootY (y : F) : U :=
  inclusion (radical_le_localUpper F σ hσ)
    (radicalOfCoordinates F σ hσ ⟨0,y,0,by simp⟩)

private def shear (t : K) : U :=
  ⟨leviSL F σ hσ (SpecialLinearGroup.transvection zero_ne_one t), by
    change middleSL F σ hσ _ ∈ SpecialLinearGroup.upperUnipotent K
    rw [middleSL_leviSL]
    exact ⟨Multiplicative.ofAdd t,rfl⟩⟩

private theorem last_rootY (y : F) :
    lastCoordinate F σ hσ (rootY F σ hσ y) = Multiplicative.ofAdd y := rfl

private theorem last_shear (t : K) :
    lastCoordinate F σ hσ (shear F σ hσ t) = 1 := by
  change Multiplicative.ofAdd ((leviSL F σ hσ _).val.val.val 2 3) = 1
  rw [leviSL_val]
  rfl

private theorem middle_rootY (y : F) :
    middleCoordinate F σ hσ (rootY F σ hσ y) = 1 := by
  apply (MonoidHom.ofInjective (SpecialLinearGroup.upperUnipotentHom_injective K)).injective
  change (MonoidHom.ofInjective (SpecialLinearGroup.upperUnipotentHom_injective K))
    ((MonoidHom.ofInjective (SpecialLinearGroup.upperUnipotentHom_injective K)).symm _) = _

  rw [MulEquiv.apply_symm_apply]
  rw [map_one]
  apply Subtype.ext
  change middleSL F σ hσ (radicalOfCoordinates F σ hσ ⟨0,y,0,by simp⟩).val = 1
  apply MonoidHom.mem_ker.mp
  rw [middleSL_ker]
  exact (radicalOfCoordinates F σ hσ ⟨0,y,0,by simp⟩).property

private theorem middle_shear (t : K) :
    middleCoordinate F σ hσ (shear F σ hσ t) = Multiplicative.ofAdd t := by
  apply (MonoidHom.ofInjective (SpecialLinearGroup.upperUnipotentHom_injective K)).injective
  change (MonoidHom.ofInjective (SpecialLinearGroup.upperUnipotentHom_injective K))
    ((MonoidHom.ofInjective (SpecialLinearGroup.upperUnipotentHom_injective K)).symm _) = _
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  exact middleSL_leviSL F σ hσ _

/-- The simple roots give a surjection onto one additive full-field coordinate
and one additive fixed-field coordinate. -/
def simpleRootHom : U →* Multiplicative F × Multiplicative K :=
  (lastCoordinate F σ hσ).prod (middleCoordinate F σ hσ)

theorem simpleRootHom_surjective : Function.Surjective (simpleRootHom F σ hσ) := by
  rintro ⟨y,t⟩
  refine ⟨rootY F σ hσ y.toAdd * shear F σ hσ t.toAdd, ?_⟩
  apply Prod.ext
  · change lastCoordinate F σ hσ (_ * _) = y
    rw [map_mul, last_rootY, last_shear, mul_one]
    rfl
  · change middleCoordinate F σ hσ (_ * _) = t
    rw [map_mul, middle_rootY, middle_shear, one_mul]
    rfl

private theorem simpleRoot_frattini_le_ker [Finite F] :
    frattini U ≤ (simpleRootHom F σ hσ).ker := by
  let f := simpleRootHom F σ hσ
  exact
    Theory.GroupTheory.frattini_le_ker_of_square_image f (by
      intro a
      rw [pow_two]
      apply Prod.ext <;> apply Multiplicative.toAdd.injective
      · change (f a).1.toAdd + (f a).1.toAdd = 0
        exact CharTwo.add_self_eq_zero _
      · change (f a).2.toAdd + (f a).2.toAdd = 0
        exact CharTwo.add_self_eq_zero _)

/-- The simple-root image supplies the exact-order lower bound. -/
theorem local_frattini_card_ge [Finite F] :
    Nat.card F * Nat.card K ≤ Nat.card (U ⧸ frattini U) := by
  let f := simpleRootHom F σ hσ
  have hk := simpleRoot_frattini_le_ker F σ hσ
  have hs := QuotientGroup.lift_surjective_of_surjective (frattini U) f
    (simpleRootHom_surjective F σ hσ) hk
  simpa only [Nat.card_prod, Nat.card_congr Multiplicative.toAdd] using
    Nat.card_le_card_of_surjective _ hs

/-- The standard local Sylow Frattini quotient has the root-coordinate order. -/
theorem local_frattini_card [Finite F] (hnt : ∃ u, σ u ≠ u) :
    Nat.card (U ⧸ frattini U) = Nat.card F * Nat.card K :=
  le_antisymm (Frattini.local_frattini_card_le F σ hσ hnt)
    (local_frattini_card_ge F σ hσ)

/-- Sylow conjugacy preserves the exact root-coordinate order. -/
theorem sylow_frattini_card [Finite F] (hnt : ∃ u, σ u ≠ u)
    (P : Sylow 2 (SU F (form F σ hσ))) :
    Nat.card (P ⧸ frattini P) = Nat.card F * Nat.card K := by
  let e : U ≃* upper F σ hσ :=
    (localUpper F σ hσ).equivMapOfInjective (localSU F (form F σ hσ)).subtype
      (localSU F (form F σ hσ)).subtype_injective
  calc
    Nat.card (P ⧸ frattini P) =
        Nat.card (sylow F σ hσ ⧸ frattini (sylow F σ hσ)) :=
      Theory.GroupTheory.SylowFrattiniBounds.card_congr (Sylow.equiv P (sylow F σ hσ))
    _ = Nat.card (U ⧸ frattini U) :=
      Theory.GroupTheory.SylowFrattiniBounds.card_congr e.symm
    _ = _ := local_frattini_card F σ hσ hnt

/-- The matrix-root coordinates identify the entire Frattini quotient. -/
def simpleRootFrattiniEquiv [Finite F] (hnt : ∃ u, σ u ≠ u) :
    (U ⧸ frattini U) ≃* Multiplicative F × Multiplicative K := by
  let f := simpleRootHom F σ hσ
  have hk := simpleRoot_frattini_le_ker F σ hσ
  let q := QuotientGroup.lift (frattini U) f hk
  apply MulEquiv.ofBijective q
  apply (QuotientGroup.lift_surjective_of_surjective (frattini U) f
    (simpleRootHom_surjective F σ hσ) hk).bijective_of_nat_card_le
  rw [local_frattini_card F σ hσ hnt, Nat.card_prod]
  exact le_rfl

omit [CharP F 2] in
/-- Every Sylow two-subgroup of an arbitrary binary PSU₄ form has exactly
three times the fixed-field exponent many Frattini generators. -/
theorem projective_frattini_card [Finite F] (J : HermitianForm 4 F) {n : ℕ}
    (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    [Finite (ProjectiveSpecialUnitaryMatrixGroup J)]
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    Nat.card (P ⧸ frattini P) = 2 ^ (3 * n) := by
  let : CharP F 2 := UnitaryFourFormTransport.charP_two n hn hcard
  have hfixed : Nat.card (FixedBy.subfield F J.conj) = 2 ^ n :=
    UnitaryFourFormTransport.fixed_card J n hn hcard hconj
  have hnt : ∃ u, J.conj u ≠ u := by
    by_contra! h
    let j : FixedBy.subfield F J.conj ≃ F := Equiv.ofBijective Subtype.val
      ⟨Subtype.val_injective, fun x => ⟨⟨x,h x⟩,rfl⟩⟩
    have he := Nat.card_congr j
    rw [hfixed,hcard] at he
    have hp : 1 < 2 ^ n := one_lt_pow₀ (by decide) hn.ne'
    nlinarith
  obtain ⟨j⟩ := UnitaryFourFormTransport.nonempty_projectiveEquiv_standardSU
    J n hn hcard hconj
  let Q := P.mapSurjective (f := j.toMonoidHom) j.surjective
  have hPQ : Nat.card (P ⧸ frattini P) = Nat.card (Q ⧸ frattini Q) :=
    Theory.GroupTheory.SylowFrattiniBounds.card_congr
      (P.equivMapOfInjective j.toMonoidHom j.injective)
  rw [hPQ, sylow_frattini_card F J.conj J.conj_involutive hnt Q, hcard, hfixed]
  rw [← pow_mul, ← pow_add]
  congr 1
  omega

omit [CharP F 2] in
/-- The seven-generator outer-action test applies to the PSU₄ family exactly
at fixed-field parameters two and four. -/
theorem projective_frattini_card_le_128_iff [Finite F] (J : HermitianForm 4 F) {n : ℕ}
    (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    [Finite (ProjectiveSpecialUnitaryMatrixGroup J)]
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    Nat.card (P ⧸ frattini P) ≤ 128 ↔ n ≤ 2 := by
  rw [projective_frattini_card F J hn hcard hconj P]
  change 2 ^ (3 * n) ≤ 2 ^ 7 ↔ _
  rw [Nat.pow_le_pow_iff_right (by decide)]
  omega

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.FrattiniExact
