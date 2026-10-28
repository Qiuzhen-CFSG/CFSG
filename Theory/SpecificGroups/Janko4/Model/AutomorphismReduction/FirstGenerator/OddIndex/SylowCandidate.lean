module

public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Image.StarOrder
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.QuotientInvolutions.Bridge
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.QuotientInvolutions.SylowCard
import Mathlib.Tactic.FinCases

/-!
# A specified subgroup of order 2²¹ in the J₄ matrices

Pull back the certified order-1024 star subgroup through the actual quotient
isomorphism of the literal ATLAS `max1Subgroup`, then embed the preimage in
`Model`. Its index in the local subgroup is 239085, so its order is 2²¹.
The eleven kernel basis words together with four lifted star Sylow words
generate this entire preimage. Thus the ambient normalizer can be tested on
fifteen explicit elements of the original matrix carrier.

This establishes a local Sylow subgroup, not its ambient Sylow maximality.
The latter is the outstanding assertion used by the parent `OddIndex` module.
No simplicity, perfectness, ambient order, or automorphism table is assumed.

Source: GLS3 Table 5.3i, `refs/KGroup/GLS3/Chapter5(sec3-).tex`, gives the
two-part 2²¹. The local words are the literal ATLAS `J4G1-max1W1` outputs
recorded in `Cardinality.Subgroup`; the four star words and their permutation
convention are recorded in `QuotientInvolutions.SylowData`.
-/

set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true

@[expose] public section

namespace Janko4.OuterReduction.OddIndex

open Subgroup Theory.GroupTheory Cardinality
open Simplicity.Max1Fusion.QuotientInvolutions Cardinality.QuotientCount.Image

attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel

/-- The actual quotient map followed by its certified star-group isomorphism. -/
noncomputable def localProjection :
    max1Subgroup matrixA_mul_self matrixB_pow_four →* StarGroup :=
  (quotientStarEquiv matrixA_mul_self matrixB_pow_four).toMonoidHom.comp
    (QuotientGroup.mk' (localKernel matrixA_mul_self matrixB_pow_four))

theorem localProjection_surjective : Function.Surjective localProjection :=
  (quotientStarEquiv matrixA_mul_self matrixB_pow_four).surjective.comp
    (QuotientGroup.mk'_surjective _)

/-- The full preimage of the fixed order-1024 star subgroup. -/
noncomputable def localTwoSubgroup :
    Subgroup (max1Subgroup matrixA_mul_self matrixB_pow_four) :=
  sylowCandidate.comap localProjection

theorem localTwoSubgroup_index : localTwoSubgroup.index = 239085 := by
  have hc := sylowCandidate.card_mul_index
  rw [sylowCandidate_card, starGroup_order] at hc
  change (sylowCandidate.comap localProjection).index = _
  rw [sylowCandidate.index_comap_of_surjective localProjection_surjective]
  omega

/-- The kernel extension has the exact two-part asserted in GLS3 Table 5.3i. -/
theorem localTwoSubgroup_card : Nat.card localTwoSubgroup = 2 ^ 21 := by
  have hc := localTwoSubgroup.card_mul_index
  rw [localTwoSubgroup_index, max1Subgroup_card] at hc
  exact (by omega : ∀ n : ℕ, n * 239085 = 501397585920 → n = 2 ^ 21) _ hc

/-- The ambient image of the prescribed local Sylow subgroup. -/
noncomputable def twoSubgroup : Subgroup Model :=
  localTwoSubgroup.map (max1Subgroup matrixA_mul_self matrixB_pow_four).subtype

theorem twoSubgroup_card : Nat.card twoSubgroup = 2 ^ 21 := by
  rw [twoSubgroup, card_map_of_injective _]
  · exact localTwoSubgroup_card
  · exact Subtype.val_injective

theorem twoSubgroup_le :
    twoSubgroup ≤ max1Subgroup matrixA_mul_self matrixB_pow_four :=
  map_subtype_le _

theorem twoSubgroup_relIndex :
    twoSubgroup.relIndex (max1Subgroup matrixA_mul_self matrixB_pow_four) = 239085 := by
  have h := relIndex_map_map_of_injective localTwoSubgroup ⊤
    (max1Subgroup matrixA_mul_self matrixB_pow_four).subtype_injective
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype, relIndex_top_right] at h
  exact h.trans localTwoSubgroup_index

theorem localProjection_ker :
    localProjection.ker = localKernel matrixA_mul_self matrixB_pow_four := by
  ext g
  change quotientStarEquiv matrixA_mul_self matrixB_pow_four
    (QuotientGroup.mk' _ g) = 1 ↔ _
  rw [map_eq_one_iff _ (quotientStarEquiv matrixA_mul_self matrixB_pow_four).injective]
  exact QuotientGroup.eq_one_iff g

/-- The literal local generators and their inverses. -/
def localAlphabet : Fin 4 → max1Subgroup matrixA_mul_self matrixB_pow_four :=
  ![localX matrixA_mul_self matrixB_pow_four, localY matrixA_mul_self matrixB_pow_four,
    (localX matrixA_mul_self matrixB_pow_four)⁻¹, (localY matrixA_mul_self matrixB_pow_four)⁻¹]

/-- The already certified star Sylow words, with Lean multiplication order. -/
def sylowWords : Fin 4 → List (Fin 4) :=
  ![sylowWord0, sylowWord1, sylowWord2, sylowWord3]

/-- Evaluate a star Sylow word in the actual local matrix generators. -/
def localSylowLift (i : Fin 4) : max1Subgroup matrixA_mul_self matrixB_pow_four :=
  evalWord localAlphabet (sylowWords i)

@[simp] theorem localProjection_x :
    localProjection (localX matrixA_mul_self matrixB_pow_four) = starFirst :=
  quotientStarEquiv_x matrixA_mul_self matrixB_pow_four

@[simp] theorem localProjection_y :
    localProjection (localY matrixA_mul_self matrixB_pow_four) = starSecond :=
  quotientStarEquiv_y matrixA_mul_self matrixB_pow_four

private theorem localProjection_alphabet (i : Fin 4) :
    (localProjection (localAlphabet i) : Equiv.Perm (Fin 24)) = starAlphabet i := by
  fin_cases i <;>
    simp [localAlphabet, starAlphabet, starFirst, starSecond]

private theorem localProjection_word (w : List (Fin 4)) :
    (localProjection (evalWord localAlphabet w) : Equiv.Perm (Fin 24)) =
      evalWord starAlphabet w := by
  induction w with
  | nil => simp [evalWord]
  | cons i w ih =>
    simp only [evalWord, map_mul, Subgroup.coe_mul, localProjection_alphabet, ih]

theorem localProjection_lift (i : Fin 4) :
    localProjection (localSylowLift i) = sylowGenerator i := by
  apply Subtype.ext
  change (localProjection (evalWord localAlphabet (sylowWords i)) :
    Equiv.Perm (Fin 24)) = _
  rw [localProjection_word]
  fin_cases i
  · exact sylowPerm0_word.symm
  · exact sylowPerm1_word.symm
  · exact sylowPerm2_word.symm
  · exact sylowPerm3_word.symm

/-- Eleven kernel basis elements and four lifted star generators. -/
def localTwoGenerator : Fin 11 ⊕ Fin 4 →
    max1Subgroup matrixA_mul_self matrixB_pow_four :=
  Sum.elim (KernelCount.basis matrixA_mul_self matrixB_pow_four) localSylowLift

/-- The explicit fifteen elements generate the whole preimage, including its kernel. -/
theorem localTwoSubgroup_eq_closure :
    localTwoSubgroup = Subgroup.closure (Set.range localTwoGenerator) := by
  let R := Subgroup.closure (Set.range localTwoGenerator)
  have hker : localProjection.ker ≤ R := by
    rw [localProjection_ker, ← closure_basis_eq_localKernel]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact Subgroup.subset_closure ⟨Sum.inl i, rfl⟩
  have hR : R ≤ localTwoSubgroup := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i | i, rfl⟩
    · exact (sylowCandidate.ker_le_comap localProjection)
        (localProjection_ker.symm ▸ KernelCount.basis_mem_localKernel
          matrixA_mul_self matrixB_pow_four i)
    · change localProjection (localSylowLift i) ∈ sylowCandidate
      rw [localProjection_lift]
      exact Subgroup.subset_closure ⟨i, rfl⟩
  have himage : sylowCandidate ≤ R.map localProjection := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    rw [← localProjection_lift]
    exact Subgroup.mem_map_of_mem localProjection (Subgroup.subset_closure ⟨Sum.inr i, rfl⟩)
  apply le_antisymm _ hR
  change sylowCandidate.comap localProjection ≤ R
  rw [← Subgroup.comap_map_eq_self hker]
  exact Subgroup.comap_mono himage

/-- The fifteen generators viewed in the exact J₄ model. -/
def twoGenerator : Fin 11 ⊕ Fin 4 → Model :=
  fun i => localTwoGenerator i

theorem twoSubgroup_eq_closure : twoSubgroup = Subgroup.closure (Set.range twoGenerator) := by
  rw [twoSubgroup, localTwoSubgroup_eq_closure, MonoidHom.map_closure, ← Set.range_comp]
  rfl

theorem twoGenerator_mem (i : Fin 11 ⊕ Fin 4) : twoGenerator i ∈ twoSubgroup := by
  rw [twoSubgroup_eq_closure]
  exact Subgroup.subset_closure ⟨i, rfl⟩

/-- Finiteness reduces ambient normalization to the fifteen generator images.
This criterion does not assert that the normalizer stays in the local subgroup. -/
theorem mem_normalizer_iff_generators (g : Model) :
    g ∈ (Subgroup.normalizer (twoSubgroup : Set Model)) ↔
      ∀ i, g * twoGenerator i * g⁻¹ ∈ twoSubgroup := by
  constructor
  · intro h i
    exact (Subgroup.mem_normalizer_iff.mp h _).mp (twoGenerator_mem i)
  · intro h
    have hm : twoSubgroup.map (MulAut.conj g).toMonoidHom ≤ twoSubgroup := by
      rw [twoSubgroup_eq_closure, MonoidHom.map_closure]
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact (twoSubgroup_eq_closure ▸ h i)
    apply Subgroup.mem_normalizer_fintype
    intro x hx
    exact hm (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hx)

theorem twoSubgroup_isPGroup : IsPGroup 2 twoSubgroup :=
  IsPGroup.of_card twoSubgroup_card

/-- The specified lift is Sylow inside the local subgroup; ambient Sylow
maximality is a separate assertion. -/
noncomputable def localSylow :
    Sylow 2 (max1Subgroup matrixA_mul_self matrixB_pow_four) :=
  (IsPGroup.of_card localTwoSubgroup_card).toSylow (by
    rw [localTwoSubgroup_index]
    decide)

@[simp] theorem localSylow_coe :
    (localSylow : Subgroup (max1Subgroup matrixA_mul_self matrixB_pow_four)) =
      localTwoSubgroup := rfl


end Janko4.OuterReduction.OddIndex
