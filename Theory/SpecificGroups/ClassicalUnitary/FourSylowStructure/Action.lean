module
public import Theory.SpecificGroups.ClassicalUnitary.FourSylowStructure
public import Theory.SpecificGroups.ClassicalUnitary.FourSylowNormalizer.Basic
public import Theory.GroupTheory.CharacteristicSelfCentralizingAutomorphisms
public import Theory.GroupTheory.CharacteristicRestrictionInnerSquares
public import Theory.PGroup

/-!
# Restricting unitary-four Sylow automorphisms to the norm-plane subgroup

Conjugation on the characteristic elementary subgroup is exactly the
norm-plane root action, with parameter the last simple-root coordinate.
That coordinate is surjective, so its image is the whole root group.
Characteristic restriction consequently maps every Sylow automorphism to
the full additive normalizer of this concrete root group. The restriction
kernel is a two-group because the elementary subgroup contains its own
centralizer. Solvability of the root normalizer therefore implies solvability
of the full Sylow automorphism group.

Source: Aschbacher--Smith, F.1.11 and F.1.12(I)(6), printed pp.262--264,
and the solvable-action step in 4.4.10--11, printed p.621.
-/

open Matrix BenderSuzuki.MatrixGroups Subgroup
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointLocal
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointQuotient
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow

@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.FourSylowStructure
variable (F : Type*) [Field F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "U" => localUpper F σ hσ
local notation "K" => FixedBy.subfield F σ
local notation "E" => elementaryKernel F σ hσ
local notation "M" => Multiplicative (FourSylowNormalizer.Space F σ)

instance elementaryKernel_normal : (E).Normal :=
  inferInstanceAs (lastHom F σ hσ).ker.Normal

theorem lastHom_surjective : Function.Surjective (lastHom F σ hσ) := by
  intro y
  refine ⟨rootWord F σ hσ y.toAdd,?_⟩
  change Multiplicative.ofAdd ((rootWord F σ hσ y.toAdd).val.val.val.val 2 3)=y
  rw [rootWord,element_matrix]
  rfl

theorem elementaryElement_conj (a : U) (v : FourSylowNormalizer.Space F σ) :
    a*elementaryElement F σ hσ v*a⁻¹ =
      elementaryElement F σ hσ
        (FourSylowNormalizer.rootMap F σ hσ (lastHom F σ hσ a).toAdd v) := by
  have hm : a*elementaryElement F σ hσ v =
      elementaryElement F σ hσ
        (FourSylowNormalizer.rootMap F σ hσ (lastHom F σ hσ a).toAdd v)*a := by
    obtain ⟨c,s,rfl⟩ := exists_element F σ hσ a
    rcases v with ⟨t,x,z⟩
    have hy : (lastHom F σ hσ (element F σ hσ c s)).toAdd=c.y := by
      change (element F σ hσ c s).val.val.val.val 2 3=c.y
      rw [element_matrix]
      rfl
    rw [hy,FourSylowNormalizer.rootMap_apply]
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; apply Units.ext
    change (element F σ hσ c s).val.val.val.val *
        (elementaryElement F σ hσ (t,x,z)).val.val.val.val =
      (elementaryElement F σ hσ _).val.val.val.val * (element F σ hσ c s).val.val.val.val
    rw [element_matrix,elementaryElement_matrix,elementaryElement_matrix]
    have ht : σ (t:F)=t := t.property
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Fin.sum_univ_succ,FourSylowNormalizer.pairing_val,
        FourSylowNormalizer.norm_val,map_add,map_mul,ht] <;>
      ring_nf <;> simp [CharTwo.two_eq_zero]
  rw [hm,mul_assoc,mul_inv_cancel,mul_one]

def coordinateInner : U →* MulAut M :=
  (MulAut.congr (elementaryEquiv F σ hσ).symm).toMonoidHom.comp
    (MulAut.conjNormal : U →* MulAut E)

theorem coordinateInner_eq (a : U) :
    coordinateInner F σ hσ a = FourSylowNormalizer.rootAction F σ hσ (lastHom F σ hσ a) := by
  apply MulEquiv.ext
  intro v
  apply (elementaryEquiv F σ hσ).injective
  change (elementaryEquiv F σ hσ)
    ((elementaryEquiv F σ hσ).symm
      (MulAut.conjNormal a (elementaryEquiv F σ hσ v))) = _
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  exact elementaryElement_conj F σ hσ a v.toAdd

theorem coordinateInner_range :
    (coordinateInner F σ hσ).range = (FourSylowNormalizer.rootAction F σ hσ).range := by
  ext a
  constructor
  · rintro ⟨u,rfl⟩
    exact ⟨lastHom F σ hσ u,(coordinateInner_eq F σ hσ u).symm⟩
  · rintro ⟨y,rfl⟩
    obtain ⟨u,rfl⟩ := lastHom_surjective F σ hσ y
    exact ⟨u,coordinateInner_eq F σ hσ u⟩

variable [Finite F] (hnt : ∃ u,σ u≠u)

def coordinateRestriction : MulAut U →* MulAut M := by
  let : (E).Characteristic := elementaryKernel_characteristic F σ hσ hnt
  exact (MulAut.congr (elementaryEquiv F σ hσ).symm).toMonoidHom.comp
    (MulAut.characteristic E)

theorem coordinateRestriction_mem_normalizer (a : MulAut U) :
    coordinateRestriction F σ hσ hnt a ∈ FourSylowNormalizer.rootNormalizer F σ hσ := by
  let : (E).Characteristic := elementaryKernel_characteristic F σ hσ hnt
  have h := characteristic_mem_normalizer_conjNormal_range E a
  let e := MulAut.congr (elementaryEquiv F σ hσ).symm
  have hm := Subgroup.le_normalizer_map e.toMonoidHom
    (show e (MulAut.characteristic E a) ∈
      (normalizer ((MulAut.conjNormal : U →* MulAut E).range : Set (MulAut E))).map
        e.toMonoidHom from ⟨_,h,rfl⟩)
  change coordinateRestriction F σ hσ hnt a ∈
    normalizer ((MulAut.conjNormal : U →* MulAut E).range.map e.toMonoidHom : Set (MulAut M)) at hm
  rw [← MonoidHom.range_comp] at hm
  change coordinateRestriction F σ hσ hnt a ∈
    normalizer ((coordinateInner F σ hσ).range : Set (MulAut M)) at hm
  rwa [coordinateInner_range] at hm

theorem coordinateRestriction_ker_isPGroup :
    IsPGroup 2 (coordinateRestriction F σ hσ hnt).ker := by
  let : (E).Characteristic := elementaryKernel_characteristic F σ hσ hnt
  have hU : IsPGroup 2 U := (localSylow F σ hσ).isPGroup'
  have hk := (E).isPGroup_characteristic_restriction_kernel_of_centralizer_le
    (hU.to_subgroup E) (centralizer_elementaryKernel_le F σ hσ hnt)
  rw [coordinateRestriction,MonoidHom.ker_comp_of_injective _ _
    (MulAut.congr (elementaryEquiv F σ hσ).symm).injective]
  exact hk

include hnt in
theorem mulAut_isSolvable_of_rootNormalizer
    (hn : Group.IsSolvable (FourSylowNormalizer.rootNormalizer F σ hσ)) :
    Group.IsSolvable (MulAut U) := by
  let r := coordinateRestriction F σ hσ hnt
  let s := r.codRestrict (FourSylowNormalizer.rootNormalizer F σ hσ)
    (coordinateRestriction_mem_normalizer F σ hσ hnt)
  let : Group.IsNilpotent r.ker := (coordinateRestriction_ker_isPGroup F σ hσ hnt).isNilpotent
  let : Group.IsSolvable (FourSylowNormalizer.rootNormalizer F σ hσ) := hn
  apply Group.isSolvable_of_ker_le_range r.ker.subtype s
  intro a ha
  rw [Subgroup.range_subtype]
  exact congrArg Subtype.val ha

end Theory.SpecificGroups.ClassicalUnitary.FourSylowStructure
