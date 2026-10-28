module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.Torus
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.CoreFree
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFour.Sylow
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFour.Geometry

/-!
# Sylow and flag geometry of the concrete projective unitary-four amalgam

For q = 2^n, n ≥ 1, the existing upper-unitriangular subgroup has order q^6
and is Sylow in the literal projective group. Its normalizer is the full
point-plane flag overlap B. The compatible projective map carries the matrix
diagonal character to a surjection B → GF(q²)ˣ × GF(q)ˣ, with kernel U.
Thus B/U is abelian of odd order (q²-1)(q-1), B is solvable, and O₂(B)=U.
In particular U is strictly smaller than B, including at q=2.

The matrix normal-core calculation transfers through that same projective
map. The final theorem combines these results with the existing generation,
ambient parabolic maximality, and maximality of the overlap inside both
literal amalgam factors. No structural premises beyond n ≥ 1 remain.

This supplies the geometric and overlap clauses for Aschbacher--Smith
F.1.4--10 and the U₄(q) model in F.1.12(I)(6), printed pp.260--264 of
`refs/quasithin.pdf`. Local-factor calculations and the outer extension have
separate owners; this is not the classification of weak BN-pairs.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
variable (n : ℕ) (hn : 1 ≤ n)

/-- The matrix normalizer is the whole flag overlap. -/
theorem matrixSylow_normalizer :
    Subgroup.normalizer (upperMatrix n hn : Set (MatrixGroup n hn)) = overlapMatrix n hn :=
  UnitaryFourSylow.normalizer_upper (MatrixField n) (fieldConj n)
    (fieldConj_involutive n hn)

/-- The compatible projective image retains the whole Sylow normalizer. -/
theorem projectiveSylow_normalizer :
    Subgroup.normalizer (upperProjective n hn : Set (ProjectiveGroup n hn)) = overlap n hn := by
  rw [upperProjective, ← Subgroup.map_normalizer_eq_of_bijective _
    ⟨projection_injective n hn, UnitaryFourFlag.project_surjective _ _⟩,
    matrixSylow_normalizer]
  rfl

/-- Normality is relative to the flag stabilizer. -/
instance upperProjective_normal_in_overlap :
    ((upperProjective n hn).subgroupOf (overlap n hn)).Normal := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer (upperProjective_le_overlap n hn)).mpr
  rw [projectiveSylow_normalizer]

/-- Restriction of the same projective map used by all three amalgam embeddings. -/
def overlapProjectEquiv : overlapMatrix n hn ≃* overlap n hn :=
  (overlapMatrix n hn).equivMapOfInjective (projection n hn) (projection_injective n hn)

@[simp] theorem overlapProjectEquiv_apply (a : overlapMatrix n hn) :
    (overlapProjectEquiv n hn a).val = projection n hn a.val := rfl

/-- Diagonal coordinates on the actual projective overlap. -/
def overlapTorusCharacter : overlap n hn →* (MatrixField n)ˣ × (PointLocal.FixedField n)ˣ :=
  (UnitaryFourSylow.torusCharacter (MatrixField n) (fieldConj n)
    (fieldConj_involutive n hn)).comp (overlapProjectEquiv n hn).symm.toMonoidHom

/-- On a matrix representative, the projective character is its actual diagonal character. -/
theorem overlapTorusCharacter_project (a : overlapMatrix n hn) :
    overlapTorusCharacter n hn (overlapProjectEquiv n hn a) =
      UnitaryFourSylow.torusCharacter (MatrixField n) (fieldConj n)
        (fieldConj_involutive n hn) a := by
  change UnitaryFourSylow.torusCharacter _ _ _
    ((overlapProjectEquiv n hn).symm (overlapProjectEquiv n hn a)) = _
  rw [MulEquiv.symm_apply_apply]

theorem overlapTorusCharacter_ker : (overlapTorusCharacter n hn).ker =
    (upperProjective n hn).subgroupOf (overlap n hn) := by
  ext a
  let b : UnitaryFourFlag.borelSU (MatrixField n)
      (UnitaryFourFlag.form (MatrixField n) (fieldConj n) (fieldConj_involutive n hn)) :=
    (overlapProjectEquiv n hn).symm a
  change UnitaryFourSylow.torusCharacter _ _ _ b = 1 ↔ _
  rw [← MonoidHom.mem_ker, UnitaryFourSylow.torusCharacter_ker]
  change b.val ∈ upperMatrix n hn ↔
    a.val ∈ upperProjective n hn
  have he : projection n hn b.val = a.val :=
    congrArg Subtype.val ((overlapProjectEquiv n hn).apply_symm_apply a)
  rw [upperProjective, ← he]
  exact (Subgroup.mem_map_iff_mem (f := projection n hn)
    (K := upperMatrix n hn) (x := b.val) (projection_injective n hn)).symm

theorem overlapTorusCharacter_surjective : Function.Surjective (overlapTorusCharacter n hn) :=
  (UnitaryFourSylow.torusCharacter_surjective (MatrixField n) (fieldConj n)
    (fieldConj_involutive n hn)).comp (overlapProjectEquiv n hn).symm.surjective

/-- The literal quotient B/U is the odd diagonal torus over the two stored fields. -/
def overlapQuotientEquivTorus :
    (overlap n hn ⧸ (upperProjective n hn).subgroupOf (overlap n hn)) ≃*
      (MatrixField n)ˣ × (PointLocal.FixedField n)ˣ :=
  (QuotientGroup.quotientMulEquivOfEq (overlapTorusCharacter_ker n hn).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (overlapTorusCharacter n hn)
      (overlapTorusCharacter_surjective n hn))

/-- Compatibility with the literal quotient map B → B/U. -/
theorem overlapQuotientEquivTorus_mk (a : overlap n hn) :
    overlapQuotientEquivTorus n hn (QuotientGroup.mk a) = overlapTorusCharacter n hn a := by
  rfl

theorem overlap_quotient_card :
    Nat.card (overlap n hn ⧸ (upperProjective n hn).subgroupOf (overlap n hn)) =
      ((2 ^ n) ^ 2 - 1) * (2 ^ n - 1) := by
  rw [Nat.card_congr (overlapQuotientEquivTorus n hn).toEquiv,
    Nat.card_prod, Nat.card_units, Nat.card_units, matrixField_card n hn,
    PointLocal.fixedField_card n hn]

theorem overlap_quotient_odd :
    Odd (Nat.card (overlap n hn ⧸ (upperProjective n hn).subgroupOf (overlap n hn))) := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  exact ((projectiveSylow n hn).subtype (upperProjective_le_overlap n hn)).not_dvd_index

/-- Relative index in the overlap, not ambient index in the projective group. -/
theorem upperProjective_relIndex_overlap :
    (upperProjective n hn).relIndex (overlap n hn) =
      ((2 ^ n) ^ 2 - 1) * (2 ^ n - 1) :=
  overlap_quotient_card n hn

theorem overlap_card : Nat.card (overlap n hn) =
    (2 ^ n) ^ 6 * (((2 ^ n) ^ 2 - 1) * (2 ^ n - 1)) := by
  have h := ((upperProjective n hn).subgroupOf (overlap n hn)).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (upperProjective_le_overlap n hn)).toEquiv, upperProjective_card] at h
  exact h.symm.trans (by rw [← upperProjective_relIndex_overlap]; rfl)

/-- Even at q=2, the overlap contains a nontrivial odd torus. -/
theorem upperProjective_lt_overlap : upperProjective n hn < overlap n hn := by
  refine lt_of_le_of_ne (upperProjective_le_overlap n hn) ?_
  intro he
  have hc := upperProjective_relIndex_overlap n hn
  rw [he, Subgroup.relIndex_self] at hc
  have hq : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
  have hq2 : 4 ≤ (2 ^ n) ^ 2 := by nlinarith
  have h1 : 1 ≤ 2 ^ n - 1 := by omega
  have h3 : 3 ≤ (2 ^ n) ^ 2 - 1 := by omega
  nlinarith

/-- The abelian quotient is the literal overlap quotient, with its inherited multiplication. -/
theorem overlap_quotient_mul_comm
    (x y : overlap n hn ⧸ (upperProjective n hn).subgroupOf (overlap n hn)) : x * y = y * x := by
  apply (overlapQuotientEquivTorus n hn).injective
  rw [map_mul, map_mul]
  exact mul_comm _ _

/-- The normal Sylow subgroup is precisely O₂ of the whole overlap, as in F.1.10. -/
theorem overlap_twoCore : pCore 2 (overlap n hn) =
    (upperProjective n hn).subgroupOf (overlap n hn) := by
  let S := (projectiveSylow n hn).subtype (upperProjective_le_overlap n hn)
  exact le_antisymm (pCore_isPGroup.le_sylow_of_normal S)
    (le_sSup ⟨inferInstance, S.isPGroup'⟩)

/-- Solvability of the full overlap follows from its two-group kernel and abelian torus. -/
theorem overlap_isSolvable : Group.IsSolvable (overlap n hn) := by
  let S := (projectiveSylow n hn).subtype (upperProjective_le_overlap n hn)
  let := S.isPGroup'.isNilpotent
  apply Group.isSolvable_of_ker_le_range (S : Subgroup (overlap n hn)).subtype
    (overlapTorusCharacter n hn)
  rw [overlapTorusCharacter_ker, Subgroup.range_subtype]
  exact le_rfl

/-- The core condition in F.1.7 for the actual projective subgroup amalgam. -/
theorem overlap_normalCore_eq_bot : (overlap n hn).normalCore = ⊥ := by
  let N := (overlap n hn).normalCore.comap (projection n hn)
  have hN : N ≤ overlapMatrix n hn := by
    intro a ha
    have ha' := (overlap n hn).normalCore_le ha
    exact (Subgroup.mem_map_iff_mem (projection_injective n hn)).mp ha'
  have hbot : N = ⊥ := @UnitaryFourSylow.eq_bot_of_normal_le_borel
    (MatrixField n) _ _ _ (fieldConj n) (fieldConj_involutive n hn) N
      (Subgroup.normal_comap (projection n hn)) hN
  apply le_antisymm _ bot_le
  intro a ha
  obtain ⟨b, rfl⟩ := UnitaryFourFlag.project_surjective
    (MatrixField n) (standardForm n hn) a
  have hb : b ∈ N := ha
  rw [hbot] at hb
  have hb1 : b = 1 := hb
  change projection n hn b = 1
  rw [hb1, map_one]

/-- The concrete Sylow and flag geometry used by the unitary-four amalgam. -/
theorem sylow_flag_geometry :
    Nat.card (projectiveSylow n hn) = (2 ^ n) ^ 6 ∧
    Subgroup.normalizer (upperProjective n hn : Set (ProjectiveGroup n hn)) = overlap n hn ∧
    Nat.card (overlap n hn ⧸ (upperProjective n hn).subgroupOf (overlap n hn)) =
      ((2 ^ n) ^ 2 - 1) * (2 ^ n - 1) ∧
    Odd (Nat.card (overlap n hn ⧸ (upperProjective n hn).subgroupOf (overlap n hn))) ∧
    (overlap n hn).normalCore = ⊥ ∧
    pointParabolic n hn ⊔ planeParabolic n hn = ⊤ ∧
    pointParabolic n hn ⊓ planeParabolic n hn = overlap n hn ∧
    IsCoatom (pointParabolic n hn) ∧ IsCoatom (planeParabolic n hn) ∧
    IsCoatom (amalgam n hn).left.range ∧ IsCoatom (amalgam n hn).right.range :=
  ⟨projectiveSylow_card n hn, projectiveSylow_normalizer n hn,
    overlap_quotient_card n hn, overlap_quotient_odd n hn, overlap_normalCore_eq_bot n hn,
    parabolic_geometry n hn⟩

end CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
