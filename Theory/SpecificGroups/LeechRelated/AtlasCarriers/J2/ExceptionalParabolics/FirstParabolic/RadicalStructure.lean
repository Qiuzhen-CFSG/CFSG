module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.RadicalStructure.Enumeration
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Quaternion--dihedral factors of the first Hall--Janko radical

The radical has order 32 by the checked word enumeration. The words `[3]`
and `[1, 0]` give an injective homomorphism from the actual `QuaternionGroup 2`;
`[3, 1]` and `[2]` give one from `DihedralGroup 4`. Kernel-checked permutation
identities verify their multiplication laws, pointwise commutation, and a
product decomposition of every radical element. The subgroup product formula
then shows that the two factors meet in order two.

`radical_structure` supplies the raw central-product witnesses inside the
unchanged `RadicalSeed.radical`. Identifying this subgroup with the intrinsic
two-core is a separate argument in the first-parabolic assembly.

Source: Aschbacher--Smith F.1.12(I)(10)--(11), printed p.263 (PDF p.274).
Witnesses are reproduced by `RadicalStructure/source/Generate.py` from the
retained ATLAS J2G1-p100B0 permutations; no external computation is trusted.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic
open GeneratorPair RadicalStructureData

set_option maxRecDepth 100000 in
private theorem quaternion_mul_check : ∀ x y : QuaternionGroup 2,
    RadicalStructureData.tablePerm (quaternionIndex (x * y)) =
      RadicalStructureData.tablePerm (quaternionIndex x) *
        RadicalStructureData.tablePerm (quaternionIndex y) := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem dihedral_mul_check : ∀ x y : DihedralGroup 4,
    RadicalStructureData.tablePerm (dihedralIndex (x * y)) =
      RadicalStructureData.tablePerm (dihedralIndex x) *
        RadicalStructureData.tablePerm (dihedralIndex y) := by
  decide +kernel

private theorem quaternionIndex_injective : Function.Injective quaternionIndex := by decide +kernel
private theorem dihedralIndex_injective : Function.Injective dihedralIndex := by decide +kernel

/-- The marked quaternion subgroup, with generator words `[3]` and `[1, 0]`. -/
def radicalQuaternionHom : QuaternionGroup 2 →* radical where
  toFun x := radicalEnum (quaternionIndex x)
  map_one' := by apply Subtype.ext; rfl
  map_mul' x y := by
    apply Subtype.ext
    apply inclusion_injective
    change inclusion (radicalElement (quaternionIndex (x * y))) =
      inclusion (radicalElement (quaternionIndex x) * radicalElement (quaternionIndex y))
    rw [map_mul, radicalElement_inclusion, radicalElement_inclusion, radicalElement_inclusion]
    exact quaternion_mul_check x y

/-- The marked dihedral subgroup, with generator words `[3, 1]` and `[2]`. -/
def radicalDihedralHom : DihedralGroup 4 →* radical where
  toFun x := radicalEnum (dihedralIndex x)
  map_one' := by apply Subtype.ext; rfl
  map_mul' x y := by
    apply Subtype.ext
    apply inclusion_injective
    change inclusion (radicalElement (dihedralIndex (x * y))) =
      inclusion (radicalElement (dihedralIndex x) * radicalElement (dihedralIndex y))
    rw [map_mul, radicalElement_inclusion, radicalElement_inclusion, radicalElement_inclusion]
    exact dihedral_mul_check x y

theorem radicalQuaternionHom_injective : Function.Injective radicalQuaternionHom := by
  intro x y h
  exact quaternionIndex_injective (radicalEnum_injective h)

theorem radicalDihedralHom_injective : Function.Injective radicalDihedralHom := by
  intro x y h
  exact dihedralIndex_injective (radicalEnum_injective h)

def radicalQuaternionFactor : Subgroup radical := radicalQuaternionHom.range

def radicalDihedralFactor : Subgroup radical := radicalDihedralHom.range

noncomputable def radicalQuaternionEquiv : radicalQuaternionFactor ≃* QuaternionGroup 2 :=
  (MonoidHom.ofInjective radicalQuaternionHom_injective).symm

noncomputable def radicalDihedralEquiv : radicalDihedralFactor ≃* DihedralGroup 4 :=
  (MonoidHom.ofInjective radicalDihedralHom_injective).symm

set_option maxRecDepth 100000 in
private theorem commute_check : ∀ (x : QuaternionGroup 2) (y : DihedralGroup 4),
    RadicalStructureData.tablePerm (quaternionIndex x) *
      RadicalStructureData.tablePerm (dihedralIndex y) =
    RadicalStructureData.tablePerm (dihedralIndex y) *
      RadicalStructureData.tablePerm (quaternionIndex x) := by
  decide +kernel

/-- The two concrete factors centralize each other pointwise. -/
theorem radical_factors_commute :
    ∀ b ∈ radicalQuaternionFactor, ∀ c ∈ radicalDihedralFactor, b * c = c * b := by
  intro b hb c hc
  obtain ⟨x, rfl⟩ := hb
  obtain ⟨y, rfl⟩ := hc
  apply Subtype.ext
  apply inclusion_injective
  change inclusion (radicalElement (quaternionIndex x) * radicalElement (dihedralIndex y)) =
    inclusion (radicalElement (dihedralIndex y) * radicalElement (quaternionIndex x))
  rw [map_mul, map_mul, radicalElement_inclusion, radicalElement_inclusion]
  exact commute_check x y

set_option maxRecDepth 100000 in
private theorem product_check : ∀ i,
    RadicalStructureData.tablePerm (quaternionIndex (quaternionPart i)) *
      RadicalStructureData.tablePerm (dihedralIndex (dihedralPart i)) =
        RadicalStructureData.tablePerm i := by
  apply GeneratorPair.SecondOrbitCertificate.allFin
  decide +kernel

/-- Every radical element has a checked product expression in the factors. -/
theorem radicalEnum_factorization (i : Fin 32) :
    radicalQuaternionHom (quaternionPart i) * radicalDihedralHom (dihedralPart i) =
      radicalEnum i := by
  apply Subtype.ext
  apply inclusion_injective
  change inclusion (radicalElement (quaternionIndex (quaternionPart i)) *
    radicalElement (dihedralIndex (dihedralPart i))) = inclusion (radicalElement i)
  rw [map_mul, radicalElement_inclusion, radicalElement_inclusion, radicalElement_inclusion]
  exact product_check i

/-- The quaternion and dihedral factors generate the entire fixed radical. -/
theorem radical_factors_sup : radicalQuaternionFactor ⊔ radicalDihedralFactor = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨i, rfl⟩ := radicalEnum_surjective x
  rw [← radicalEnum_factorization]
  exact Subgroup.mul_mem_sup ⟨quaternionPart i, rfl⟩ ⟨dihedralPart i, rfl⟩

theorem card_radicalQuaternionFactor : Nat.card radicalQuaternionFactor = 8 := by
  rw [Nat.card_congr radicalQuaternionEquiv.toEquiv, Nat.card_eq_fintype_card,
    QuaternionGroup.card]

theorem card_radicalDihedralFactor : Nat.card radicalDihedralFactor = 8 := by
  rw [Nat.card_congr radicalDihedralEquiv.toEquiv, DihedralGroup.nat_card]

/-- Their intersection is the common order-two central subgroup. -/
theorem card_radical_factors_inf :
    Nat.card (radicalQuaternionFactor ⊓ radicalDihedralFactor : Subgroup radical) = 2 := by
  have hn : radicalDihedralFactor ≤ Subgroup.normalizer (radicalQuaternionFactor : Set radical) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    intro c hc
    exact Subgroup.mem_centralizer_iff.mpr (fun b hb => radical_factors_commute b hb c hc)
  have h := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes
    radicalQuaternionFactor radicalDihedralFactor hn
  rw [card_radicalQuaternionFactor, card_radicalDihedralFactor, radical_factors_sup,
    Subgroup.card_top, card_radical] at h
  omega

/-- The raw central-product structure of the fixed radical. This theorem
makes no claim identifying the subgroup with a two-core. -/
theorem radical_structure :
    Nat.card radical = 32 ∧ ∃ B C : Subgroup radical,
      Nonempty (B ≃* QuaternionGroup 2) ∧ Nonempty (C ≃* DihedralGroup 4) ∧
      Nat.card (B ⊓ C : Subgroup radical) = 2 ∧
      (∀ b ∈ B, ∀ c ∈ C, b * c = c * b) ∧ B ⊔ C = ⊤ :=
  ⟨card_radical, radicalQuaternionFactor, radicalDihedralFactor,
    ⟨radicalQuaternionEquiv⟩, ⟨radicalDihedralEquiv⟩, card_radical_factors_inf,
    radical_factors_commute, radical_factors_sup⟩

end Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic
