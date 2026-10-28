module

public import Theory.Representation.OrthogonalFourMinusFirstCohomology.AlternatingFive.Geometry
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Equivariant identification of the small Hermitian module with the A₅ module

Label the five nonzero singular Hermitian matrices by `Fin 5`. The matrix
action permutes them, and their spanning property makes this permutation
action faithful. Perfection forces its image into A₅; the known exceptional
group isomorphism supplies equality of cardinalities and hence surjectivity.

The linear map sending a permutation basis vector to the corresponding
singular matrix is equivariant and surjective. The sum relation kills the
constant vector. Its restriction to the even-weight core is therefore still
surjective and, by the checked dimensions, bijective. Composing its inverse
with `BinaryPermutation.coreEquivNatural` gives the actual binary module
equivalence, with its intertwining identity proved for the same group map.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma I.1.6(3), printed p.408 (PDF p.419).
-/

@[expose] public section

noncomputable section
open Representation.OrthogonalFourMinus.FiniteModel
namespace Representation.OrthogonalFourMinus.AlternatingFive
local instance : Algebra (ZMod 2) (fixedField 1) := ZMod.algebraOfModule 2 (fixedField 1)
local instance : Fintype (Field 1) := Fintype.ofFinite _

instance : Finite Point := by unfold Point; infer_instance
instance : Fintype Point := Fintype.ofFinite _

lemma card_point : Fintype.card Point = 5 := by
  rw [← Fintype.card_congr pointEquiv, Fintype.card_option, card_field]

def label : Point ≃ Fin 5 := Fintype.equivFinOfCardEq card_point

def vector (i : Fin 5) : Space 1 := (label.symm i).val

lemma sum_vector : ∑ i, vector i = 0 := by
  rw [show (∑ i, vector i) = ∑ p : Point, p.val from label.symm.sum_comp _]
  rw [← pointEquiv.sum_comp]
  exact sum_pointVector

lemma span_vector : Submodule.span (ZMod 2) (Set.range vector) = ⊤ := by
  have hr : Set.range vector = Set.range pointVector := by
    ext X
    constructor
    · rintro ⟨i, rfl⟩
      obtain ⟨t, ht⟩ := parametrize_surjective (label.symm i)
      exact ⟨t, congrArg Subtype.val ht⟩
    · rintro ⟨t, rfl⟩
      exact ⟨label (parametrize t), congrArg Subtype.val (label.symm_apply_apply _)⟩
  rw [hr, span_pointVector]

abbrev Group := Matrix.SpecialLinearGroup (Fin 2) (Field 1)

def pointPerm (g : Group) : Equiv.Perm Point where
  toFun p := ⟨action 1 g p.val, by
    constructor
    · intro h
      apply p.property.1
      exact (linearActionHom 1 g).injective (h.trans (map_zero _).symm)
    · rw [form_preserved]; exact p.property.2⟩
  invFun p := ⟨action 1 g⁻¹ p.val, by
    constructor
    · intro h
      apply p.property.1
      exact (linearActionHom 1 g⁻¹).injective (h.trans (map_zero _).symm)
    · rw [form_preserved]; exact p.property.2⟩
  left_inv p := by
    apply Subtype.ext
    exact (linearActionHom 1 g).symm_apply_apply p.val
  right_inv p := by
    apply Subtype.ext
    exact (linearActionHom 1 g).apply_symm_apply p.val

def pointAction : Group →* Equiv.Perm Point where
  toFun := pointPerm
  map_one' := by
    apply Equiv.ext
    intro p
    apply Subtype.ext
    exact LinearMap.congr_fun (action 1).map_one p.val
  map_mul' g h := by
    apply Equiv.ext
    intro p
    apply Subtype.ext
    exact LinearMap.congr_fun ((action 1).map_mul g h) p.val

def permutation : Group →* Equiv.Perm (Fin 5) :=
  label.permCongrHom.toMonoidHom.comp pointAction

lemma vector_permutation (g : Group) (i : Fin 5) :
    vector (permutation g i) = action 1 g (vector i) := by
  change (label.symm (label (pointPerm g (label.symm i)))).val = _
  rw [label.symm_apply_apply]
  rfl

def combination : BinaryPermutation.Full (Fin 5) →ₗ[ZMod 2] Space 1 :=
  Fintype.linearCombination (ZMod 2) vector

lemma combination_surjective : Function.Surjective combination :=
  (span_range_eq_top_iff_surjective_fintypeLinearCombination _ _).mp span_vector

lemma combination_allOne : combination (BinaryPermutation.allOne (Fin 5)) = 0 := by
  simpa [combination, Fintype.linearCombination_apply, BinaryPermutation.allOne] using sum_vector

lemma combination_equivariant (g : Group) (v : BinaryPermutation.Full (Fin 5)) :
    combination (BinaryPermutation.representation (Fin 5) (permutation g) v) =
      action 1 g (combination v) := by
  change (∑ i, v ((permutation g).symm i) • vector i) = _
  rw [← Equiv.sum_comp (permutation g)]
  simp only [Equiv.symm_apply_apply, vector_permutation]
  change _ = ((action 1 g).restrictScalars (ZMod 2)) (∑ i, v i • vector i)
  rw [map_sum]
  simp only [map_smul, LinearMap.restrictScalars_apply]

lemma permutation_injective : Function.Injective permutation := by
  intro g h he
  apply action_injective 1
  apply LinearMap.ext
  intro X
  obtain ⟨v, rfl⟩ := combination_surjective X
  rw [← combination_equivariant, ← combination_equivariant, he]

lemma permutation_even (g : Group) : permutation g ∈ alternatingGroup (Fin 5) := by
  let : _root_.Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (Field 1)) :=
    GorensteinWalter.psl2_isPerfect_of_card_gt_three (Field 1) (by
      simp [Nat.card_eq_fintype_card, card_field])
  let : _root_.Group.IsPerfect Group :=
    _root_.Group.IsPerfect.ofSurjective (f := (sl2EquivPSL2 1).symm.toMonoidHom)
      (sl2EquivPSL2 1).symm.surjective
  let sign := Equiv.Perm.sign.comp permutation
  let : _root_.Group.IsPerfect sign.range := _root_.Group.IsPerfect.range sign
  apply Equiv.Perm.mem_alternatingGroup.mpr
  exact congrArg Subtype.val (Subsingleton.elim (sign.rangeRestrict g) 1)

def alternatingHom : Group →* alternatingGroup (Fin 5) :=
  permutation.codRestrict _ permutation_even

lemma alternatingHom_bijective : Function.Bijective alternatingHom := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨fun g h he => permutation_injective (congrArg Subtype.val he), ?_⟩
  obtain ⟨e⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (K := Field 1) (by simpa [Nat.card_eq_fintype_card] using card_field)
  exact Nat.card_congr ((sl2EquivPSL2 1).trans e).toEquiv

/-- The group identification induced by permutation of the five singular vectors. -/
def groupEquiv : Group ≃* alternatingGroup (Fin 5) :=
  MulEquiv.ofBijective alternatingHom alternatingHom_bijective

@[simp] lemma groupEquiv_coe (g : Group) : (groupEquiv g).val = permutation g := by
  simp [groupEquiv, alternatingHom]

lemma finrank_binary_space : Module.finrank (ZMod 2) (Space 1) = 4 := by
  have hk : Module.finrank (ZMod 2) (fixedField 1) = 1 := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    exact (FiniteField.pow_finrank_eq_natCard 2 (fixedField 1)).trans (card_fixedField 1)
  rw [← Module.finrank_mul_finrank (ZMod 2) (fixedField 1), hk, finrank_space, one_mul]

def coreMap : BinaryPermutation.core (Fin 5) →ₗ[ZMod 2] Space 1 :=
  combination.comp (BinaryPermutation.core (Fin 5)).subtype

lemma coreMap_surjective : Function.Surjective coreMap := by
  intro X
  obtain ⟨v, hv⟩ := combination_surjective X
  let a := BinaryPermutation.augmentation (Fin 5) v
  refine ⟨⟨v - a • BinaryPermutation.allOne (Fin 5), ?_⟩, ?_⟩
  · change BinaryPermutation.augmentation (Fin 5) _ = 0
    have hfive : (Fintype.card (Fin 5) : ZMod 2) = 1 := by decide
    simp only [map_sub, map_smul, BinaryPermutation.augmentation_allOne,
      hfive, smul_eq_mul, mul_one, a, sub_self]
  · change combination (v - a • BinaryPermutation.allOne (Fin 5)) = X
    rw [map_sub, map_smul, combination_allOne, smul_zero, sub_zero, hv]

lemma coreMap_bijective : Function.Bijective coreMap := by
  refine ⟨?_, coreMap_surjective⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := coreMap) ?_).mpr
    coreMap_surjective
  rw [BinaryPermutation.finrank_core, finrank_binary_space]
  rfl

def coreEquiv : BinaryPermutation.core (Fin 5) ≃ₗ[ZMod 2] Space 1 :=
  LinearEquiv.ofBijective coreMap coreMap_bijective

/-- The actual binary linear equivalence with the five-point natural module. -/
def moduleEquiv : Space 1 ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 5) :=
  coreEquiv.symm.trans (BinaryPermutation.coreEquivNatural (Fin 5) (by decide))

/-- This is an identification of representations, using the alternating subgroup inclusion. -/
theorem intertwines (g : Group) (X : Space 1) :
    moduleEquiv (action 1 g X) =
      BinaryPermutation.naturalRepresentation (Fin 5) (groupEquiv g).val (moduleEquiv X) := by
  obtain ⟨v, rfl⟩ := coreEquiv.surjective X
  have he : action 1 g (coreEquiv v) =
      coreEquiv (BinaryPermutation.coreRepresentation (Fin 5) (permutation g) v) :=
    (combination_equivariant g v.val).symm
  rw [he, groupEquiv_coe]
  simpa only [moduleEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    using BinaryPermutation.coreEquivNatural_equivariant (Fin 5) (by decide) (permutation g) v

end Representation.OrthogonalFourMinus.AlternatingFive
