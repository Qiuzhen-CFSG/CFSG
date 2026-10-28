module

public import Theory.SpecificGroups.Monster.Construction.NOctad.Blocks
public import Theory.Representation.BinaryPermutation
public import Mathlib.FieldTheory.Finiteness

/-!
# Even subsets of an octad modulo complementation

The coordinates are the even binary words on the eight actual support
positions of a Golay octad. Extending by zero gives the subset in the source
word `r(c,J)`. Complementation adds the all-one word on these eight positions.
Its fixed-point-free orbits are exactly the 64 classes in Lemma 30.1.

Source: Aschbacher, *Sporadic Groups*, 29.13 and 30.1, pp. 160–163.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Monster.Construction.NOctad
open LocalC LocalC.ShortFamilies TrialitySpin TrialitySpin.SignedModules
open Atlas.Codes Atlas.Fischer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev Support (c : Octad) := {i : Omega // c.val.val i ≠ 0}

theorem support_card (c : Octad) : Fintype.card (Support c) = 8 := by
  simpa only [Support, Fintype.card_subtype, hammingNorm] using c.prop

instance (c : Octad) : Nonempty (Support c) :=
  Fintype.card_pos_iff.mp (by rw [support_card]; decide)

/-- Even subsets, still before the source complement relation. -/
abbrev EvenSubset (c : Octad) := ↥(BinaryPermutation.core (Support c))

/-- Extend a supported subset by zero to all 24 source coordinates. -/
def subsetWord (c : Octad) (J : EvenSubset c) : BinaryWord :=
  fun i => if h : c.val.val i ≠ 0 then J.val ⟨i, h⟩ else 0

@[simp] theorem subsetWord_support (c : Octad) (J : EvenSubset c) (i : Support c) :
    subsetWord c J i.val = J.val i := by simp [subsetWord, i.prop]

theorem subsetWord_supported (c : Octad) (J : EvenSubset c) (i : Omega)
    (h : subsetWord c J i ≠ 0) : c.val.val i ≠ 0 := by
  by_contra hi
  exact h (by simp [subsetWord, hi])

theorem subsetWord_even (c : Octad) (J : EvenSubset c) :
    Even (hammingNorm (subsetWord c J)) := by
  apply (even_weight_iff _).mpr
  calc
    ∑ i, subsetWord c J i =
        ∑ i ∈ Finset.univ.filter (fun i => c.val.val i ≠ 0), subsetWord c J i := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i _ hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
      simp [subsetWord, hi]
    _ = ∑ i : Support c, J.val i := by
      rw [Finset.sum_subtype (p := fun i => c.val.val i ≠ 0)
        (F := (inferInstance : Fintype (Support c))) _ (by intro i; simp)]
      simp
    _ = 0 := J.prop

/-- The actual source parameters with an explicitly chosen Parker-loop sign. -/
def parameters (c : Octad) (J : EvenSubset c) (s : ParkerBit) : OctadParameters :=
  ⟨(c.val, s), subsetWord c J, c.prop, subsetWord_supported c J, subsetWord_even c J⟩

def subsetOne (c : Octad) : EvenSubset c :=
  ⟨BinaryPermutation.allOne (Support c),
    (BinaryPermutation.constants_le_core_iff (Support c)).mpr
      (by rw [support_card]; decide) (Submodule.subset_span (by simp))⟩

/-- Complement inside the octad. -/
def complementSubset (c : Octad) (J : EvenSubset c) : EvenSubset c := J + subsetOne c

theorem complementSubset_involutive (c : Octad) :
    Function.Involutive (complementSubset c) := by
  intro J
  apply Subtype.ext
  funext i
  change (J.val i + 1) + 1 = J.val i
  have h : (1 : ParkerBit) + 1 = 0 := by decide
  rw [add_assoc, h, add_zero]

theorem complementSubset_ne (c : Octad) (J : EvenSubset c) : complementSubset c J ≠ J := by
  intro h
  have hz : subsetOne c = 0 := add_eq_left.mp h
  have he := congrArg (fun a : EvenSubset c => a.val (Classical.choice
    (inferInstance : Nonempty (Support c)))) hz
  exact one_ne_zero he

theorem subsetWord_complement (c : Octad) (J : EvenSubset c) :
    subsetWord c (complementSubset c J) = subsetWord c J + c.val.val := by
  funext i
  by_cases hi : c.val.val i = 0
  · simp [subsetWord, hi]
  · have hc : c.val.val i = 1 := (bit_cases (c.val.val i)).resolve_left hi
    simp [subsetWord, complementSubset, subsetOne, BinaryPermutation.allOne, hc]

/-- The two-element complement orbits, with their concrete involution. -/
def subsetPairing (c : Octad) : Pairing (EvenSubset c) where
  flip := (complementSubset_involutive c).toPerm
  involutive := complementSubset_involutive c

abbrev SubsetClass (c : Octad) := (subsetPairing c).Orbit

def subsetClass (c : Octad) : EvenSubset c → SubsetClass c := (subsetPairing c).orbit

theorem subsetClass_eq (c : Octad) (J K : EvenSubset c) :
    subsetClass c J = subsetClass c K ↔ J = K ∨ J = complementSubset c K :=
  (subsetPairing c).orbit_eq J K

theorem evenSubset_card (c : Octad) : Nat.card (EvenSubset c) = 128 := by
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2),
    BinaryPermutation.finrank_core, support_card, ZMod.card]
  norm_num

/-- The sum in 30.1 has exactly 64 terms after the complement identification. -/
theorem subsetClass_card (c : Octad) : Nat.card (SubsetClass c) = 64 := by
  have h := (subsetPairing c).card_eq_twice (complementSubset_ne c)
  change Nat.card (EvenSubset c) = Nat.card (SubsetClass c) * 2 at h
  rw [evenSubset_card] at h
  omega

theorem subsetWord_injective (c : Octad) : Function.Injective (subsetWord c) := by
  intro J K h
  apply Subtype.ext
  funext i
  simpa only [subsetWord_support] using congrFun h i.val

theorem parameters_complement_vector (c : Octad) (J : EvenSubset c) (s : ParkerBit) :
    vector (parameters c (complementSubset c J) s) = vector (parameters c J s) := by
  apply (vector_eq_iff _ _).mpr
  exact ⟨rfl, Or.inr (subsetWord_complement c J)⟩

/-- The source vector is genuinely defined on complement classes, for either
choice of Parker-loop sign. -/
def classVector (c : Octad) (s : ParkerBit) : SubsetClass c → Space :=
  Quotient.lift (fun J => vector (parameters c J s)) (by
    intro J K h
    rcases h with rfl | h
    · rfl
    · change J = complementSubset c K at h
      rw [h]
      exact parameters_complement_vector c K s)

@[simp] theorem classVector_mk (c : Octad) (s : ParkerBit) (J : EvenSubset c) :
    classVector c s (subsetClass c J) = vector (parameters c J s) := rfl

theorem classVector_sign (c : Octad) (a : SubsetClass c) :
    classVector c 1 a = -classVector c 0 a := by
  refine Quotient.inductionOn a fun J => ?_
  exact vector_sign (parameters c J 0)

theorem classVector_mem_block (c : Octad) (s : ParkerBit) (a : SubsetClass c) :
    classVector c s a ∈ block c := by
  refine Quotient.inductionOn a fun J => ?_
  exact Submodule.subset_span ⟨parameters c J s, rfl, rfl⟩

private theorem parameters_lift_eq (c : Octad) (s : ParkerBit) (J K : EvenSubset c) :
    rOctad (parameters c J s) = rOctad (parameters c K s) ↔
      subsetClass c J = subsetClass c K := by
  rw [rOctad_eq_iff, subsetClass_eq]
  change ((c.val, s) = (c.val, s) ∧
    (subsetWord c J = subsetWord c K ∨ subsetWord c J = subsetWord c K + c.val.val)) ↔ _
  simp only [true_and]
  rw [← subsetWord_complement, (subsetWord_injective c).eq_iff,
    (subsetWord_injective c).eq_iff]

private theorem parameters_lift_ne_flip (c : Octad) (s : ParkerBit) (J K : EvenSubset c) :
    rOctad (parameters c J s) ≠
      (shortLiftSigns sourceLatticeComparison).flip (rOctad (parameters c K s)) := by
  intro h
  have he := congrArg Prod.snd ((rOctad_eq_flip_iff _ _).mp h).1
  change s = s + 1 at he
  have hz : (1 : ParkerBit) = 0 := add_left_cancel (he.symm.trans (add_zero s).symm)
  exact one_ne_zero hz

/-- The 64 class vectors are orthonormal for the induced source form. -/
theorem gamma_classVector (c : Octad) (s : ParkerBit) (a b : SubsetClass c) :
    gamma (classVector c s a) (classVector c s b) = if a = b then 1 else 0 := by
  refine Quotient.inductionOn₂ a b fun J K => ?_
  change gamma (vector (parameters c J s)) (vector (parameters c K s)) = _
  rw [gamma_vector, if_neg (parameters_lift_ne_flip c s J K), sub_zero,
    parameters_lift_eq]
  simp only [subsetClass, Pairing.orbit]
  congr 1

instance (c : Octad) : Fintype (SubsetClass c) := Fintype.ofFinite _

theorem classVector_linearIndependent (c : Octad) (s : ParkerBit) :
    LinearIndependent ℝ (classVector c s) := by
  apply (Fintype.linearIndependent_iff (R := ℝ) (v := classVector c s)).mpr
  intro a ha i
  have h := congrArg (gamma (classVector c s i)) ha
  simpa only [map_sum, map_smul, gamma_classVector, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_zero] using h

end Sporadic.Monster.Construction.NOctad
