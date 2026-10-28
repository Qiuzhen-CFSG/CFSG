module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.TypeASLTangentRootSupport
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.TypeASLRootSubgroups
public import Theory.AlgebraicGroup.RootSubgroups.NormalizerMembership

/-!
# Explicit roots of the special-linear diagonal torus

This module records the character attached to an ordered pair of distinct
diagonal coordinates and proves that each elementary matrix root subgroup
realizes that character.  The character is the Laurent monomial with exponent
`e_j - e_i`; its cocharacter is the corresponding diagonal matrix
cocharacter, so the character--cocharacter pairing is the usual type-A dot
product.

The reverse inclusion, namely that every torus root occurs in this list, is a
tangent-space support statement supplied by the preceding support module.  We
then assemble the finite ordered-pair index, its addition, negation,
reflection, heights, positive roots, and simple roots into a complete
`RootGroupData.IsRealization`.  The proofs are elementary coordinate
calculations and the explicit one-parameter matrix subgroup identities; no
global root-system classification theorem is used.
-/

open scoped BigOperators
open Set

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup

open StandardRootSystem

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

public section

@[expose]
public noncomputable def typeASLRootCorootExponent (m : ℕ) (r : TypeARootIndex m) :
    Fin m → ℤ := fun q =>
  (if r.1.2 = q.castSucc then 1 else 0) -
    (if r.1.1 = q.castSucc then 1 else 0)

@[expose]
public noncomputable def typeASLRootCocharacter (m : ℕ) (r : TypeARootIndex m) :
    ClosedSubgroupTorusCocharacter (typeASLTorus (k := k) m) :=
  typeASLDiagonalCocharacter (k := k) m
    (typeASLRootCorootExponent m r)

@[simp]
public theorem typeASLRootWeight_cocharacter_pairing (m : ℕ)
    (r s : TypeARootIndex m) :
    characterCocharacterPairing (typeASLTorus (k := k) m)
        (typeASLRootCocharacter (k := k) m s)
        (Additive.ofMul (typeASLRootWeight (k := k) m r)) =
      ∑ i,
        (typeASLDiagonalEntryExponent m r.1.2 i -
          typeASLDiagonalEntryExponent m r.1.1 i) *
        typeASLRootCorootExponent m s i := by
  letI := (typeASLTorus (k := k) m).carrierAlgebraicGroup
  apply (weightCocharacterEquation_existsUnique
    (typeASLTorus (k := k) m) (typeASLRootWeight (k := k) m r)
      (typeASLRootCocharacter (k := k) m s)).unique
  · exact characterCocharacterPairing_spec (typeASLTorus (k := k) m)
      (typeASLRootWeight (k := k) m r)
      (typeASLRootCocharacter (k := k) m s)
  · simpa only [typeASLTorus, typeASLRootWeight, Pi.sub_apply,
      typeASLRootCocharacter] using
      (typeASLDiagonalCharacter_cocharacter_pairing (k := k) m
        (typeASLDiagonalEntryExponent m r.1.2 -
          typeASLDiagonalEntryExponent m r.1.1)
        (typeASLRootCorootExponent m s))

lemma typeASLRootWeight_ne_one (m : ℕ) (r : TypeARootIndex m) :
    typeASLRootWeight (k := k) m r ≠ 1 := by
  letI := (typeASLTorus (k := k) m).carrierAlgebraicGroup
  intro h
  change typeASLDiagonalCharacter (k := k) m
      (typeASLDiagonalEntryExponent m r.1.2 -
        typeASLDiagonalEntryExponent m r.1.1) = 1 at h
  have hzero : typeASLDiagonalCharacter (k := k) m 0 = 1 := by
    apply Additive.ofMul.injective
    simpa [typeASLDiagonalCharacterAddEquiv_apply] using
      (typeASLDiagonalCharacterAddEquiv (k := k) m).map_zero
  have h' :
      typeASLDiagonalCharacterAddEquiv (k := k) m
          (typeASLDiagonalEntryExponent m r.1.2 -
            typeASLDiagonalEntryExponent m r.1.1) =
        typeASLDiagonalCharacterAddEquiv (k := k) m 0 := by
    rw [typeASLDiagonalCharacterAddEquiv_apply,
      typeASLDiagonalCharacterAddEquiv_apply]
    exact congrArg Additive.ofMul (h.trans hzero.symm)
  have hz := (typeASLDiagonalCharacterAddEquiv (k := k) m).injective h'
  have hEq : typeASLDiagonalEntryExponent m r.1.2 =
      typeASLDiagonalEntryExponent m r.1.1 := by
    exact sub_eq_zero.mp hz
  exact r.2 (typeASLDiagonalEntryExponent_injective m hEq.symm)

lemma typeASLRootSubgroup_invariant (m : ℕ) (r : TypeARootIndex m) :
    IsClosedSubgroupInvariant (typeASLTorus (k := k) m)
      (typeASLRootSubgroup (k := k) m r) := by
  letI := (typeASLTorus (k := k) m).carrierAlgebraicGroup
  intro t ht x hx
  let s : Variety.Point (typeASLTorus (k := k) m).carrierVariety :=
    (typeASLTorus (k := k) m).pointEquiv.symm ⟨t, ht⟩
  have hs : (typeASLTorus (k := k) m).includePoint s = t := by
    exact congrArg Subtype.val
      ((typeASLTorus (k := k) m).pointEquiv.apply_symm_apply ⟨t, ht⟩)
  have hdiag : slPointMatrix (m + 1)
      ((typeASLTorus (k := k) m).includePoint s) =
      Matrix.diagonal (fun a =>
        (dPointEquiv 1
          ((typeASLDiagonalEntryCharacter (k := k) m a).onPoints s)
            (0 : Fin 1) : k)) := by
    exact typeASLDiagonalTorus_includePoint_matrix (k := k) m s
  rw [← hs]
  exact typeASLRootSubgroup_conjugation_mem_of_diagonal (k := k) m r
    ((typeASLTorus (k := k) m).includePoint s)
    (fun a => dPointEquiv 1
      ((typeASLDiagonalEntryCharacter (k := k) m a).onPoints s) (0 : Fin 1))
    hdiag x hx

lemma typeASLRootWeight_equation (m : ℕ) (r : TypeARootIndex m) :
    RootWeightEquation (typeASLTorus (k := k) m)
      (typeASLRootSubgroup (k := k) m r)
      (typeASLRootWeight (k := k) m r) := by
  letI := (typeASLTorus (k := k) m).carrierAlgebraicGroup
  apply typeASLRootSubgroup_rootWeightEquation_of_diagonal (k := k) m r
    (typeASLTorus (k := k) m)
    (typeASLRootWeight (k := k) m r)
    (fun s a => dPointEquiv 1
      ((typeASLDiagonalEntryCharacter (k := k) m a).onPoints s) (0 : Fin 1))
  · intro s
    exact typeASLDiagonalTorus_includePoint_matrix (k := k) m s
  · intro s
    rw [mul_comm]
    exact typeASLRootWeight_pointCharacter m r s

@[simp]
public theorem typeASLRootWeight_mem_torusRootSet
    (m : ℕ) (r : TypeARootIndex m) :
    typeASLRootWeight (k := k) m r ∈ TorusRootSet (typeASLTorus (k := k) m) := by
  refine ⟨typeASLRootSubgroup (k := k) m r,
    ⟨typeASLRootSubgroup_invariant (k := k) m r,
      typeASLRootSubgroup_isOneParameter (k := k) m r⟩,
    typeASLRootWeight_equation (k := k) m r⟩

noncomputable section

abbrev TypeASLTorusRoot (m : ℕ) := ULift.{u, 0} (TypeARootIndex m)

@[expose] def typeASLTorusRootIndexEquiv (m : ℕ) : TypeASLTorusRoot.{u} m ≃ TypeARootIndex m :=
  Equiv.ulift

@[expose] def typeASLTorusRootWeight (m : ℕ) : TypeASLTorusRoot.{u} m → TorusWeight (typeASLTorus (k := k) m) :=
  fun r => typeASLRootWeight (k := k) m (typeASLTorusRootIndexEquiv m r)

@[expose] def typeASLTorusRootSubgroup (m : ℕ) : TypeASLTorusRoot.{u} m → ClosedSubgroup (slVariety k (m + 1)) :=
  fun r => typeASLRootSubgroup (k := k) m (typeASLTorusRootIndexEquiv m r)

@[expose] def typeASLTorusRootNeg (m : ℕ) : TypeASLTorusRoot.{u} m → TypeASLTorusRoot.{u} m :=
  fun r => ⟨typeASLRootNeg m (typeASLTorusRootIndexEquiv m r)⟩

@[expose] def typeASLTorusRootAdd (m : ℕ) (r s : TypeASLTorusRoot.{u} m) : Option (TypeASLTorusRoot.{u} m) :=
  (typeASLRootAdd m (typeASLTorusRootIndexEquiv m r) (typeASLTorusRootIndexEquiv m s)).map ULift.up

@[expose] def typeASLTorusRootReflect (m : ℕ) (r s : TypeASLTorusRoot.{u} m) : TypeASLTorusRoot.{u} m :=
  ⟨typeASLRootReflect m (typeASLTorusRootIndexEquiv m r) (typeASLTorusRootIndexEquiv m s)⟩

@[expose] def typeASLTorusRootPairing (m : ℕ) (r s : TypeASLTorusRoot.{u} m) : ℤ :=
  (if (typeASLTorusRootIndexEquiv m r).1.1 = (typeASLTorusRootIndexEquiv m s).1.1 then 1 else 0) -
    (if (typeASLTorusRootIndexEquiv m r).1.1 = (typeASLTorusRootIndexEquiv m s).1.2 then 1 else 0) -
    (if (typeASLTorusRootIndexEquiv m r).1.2 = (typeASLTorusRootIndexEquiv m s).1.1 then 1 else 0) +
    (if (typeASLTorusRootIndexEquiv m r).1.2 = (typeASLTorusRootIndexEquiv m s).1.2 then 1 else 0)

@[expose] def typeASLTorusRootWeightPairing (m : ℕ) (χ : TorusWeight (typeASLTorus (k := k) m))
    (s : TypeASLTorusRoot.{u} m) : ℤ :=
  (characterCocharacterPairing (typeASLTorus (k := k) m)
    (typeASLRootCocharacter (k := k) m (typeASLTorusRootIndexEquiv m s))
    (Additive.ofMul χ))

@[expose] def typeASLTorusRootCocharacter (m : ℕ) (r : TypeASLTorusRoot.{u} m) :
    ClosedSubgroupTorusCocharacter (typeASLTorus (k := k) m) :=
  typeASLRootCocharacter (k := k) m (typeASLTorusRootIndexEquiv m r)

@[expose] def typeASLTorusRootHeight (m : ℕ) (r : TypeASLTorusRoot.{u} m) : ℤ :=
  (typeASLTorusRootIndexEquiv m r).1.2.val - (typeASLTorusRootIndexEquiv m r).1.1.val

@[expose] def typeASLTorusPositiveRoots (m : ℕ) : Set (TypeASLTorusRoot.{u} m) := {r | 0 < typeASLTorusRootHeight m r}

@[expose] def typeASLTorusSimpleRoots (m : ℕ) : Set (TypeASLTorusRoot.{u} m) :=
  Set.range (fun i : Fin m => (⟨typeASimpleRootIndex m i⟩ : TypeASLTorusRoot.{u} m))

@[expose] def typeASLTorusRootData (m : ℕ) : RootGroupData (slVariety k (m + 1)) (typeASLTorus (k := k) m) where
  Root := TypeASLTorusRoot.{u} m
  rootWeight := typeASLTorusRootWeight (k := k) m
  rootSubgroup := typeASLTorusRootSubgroup (k := k) m
  neg := typeASLTorusRootNeg m
  add := typeASLTorusRootAdd m
  pairing := typeASLTorusRootPairing m
  weightPairing := typeASLTorusRootWeightPairing (k := k) m
  rootCocharacter := typeASLTorusRootCocharacter (k := k) m
  reflect := typeASLTorusRootReflect m
  positive := typeASLTorusPositiveRoots m
  simple := typeASLTorusSimpleRoots m
  height := typeASLTorusRootHeight m

theorem typeASLTorusRootWeight_range (m : ℕ) :
    Set.range (typeASLTorusRootWeight (k := k) m) =
      TorusRootSet (typeASLTorus (k := k) m) := by
  apply Set.Subset.antisymm
  · rintro χ ⟨r, rfl⟩
    exact typeASLRootWeight_mem_torusRootSet m (typeASLTorusRootIndexEquiv m r)
  · intro χ hχ
    rcases hχ with ⟨X, hX, hEq⟩
    have hcentralizer :
        (typeASLTorus (k := k) m).centralizer.toSubgroup =
          (typeASLTorus (k := k) m).toSubgroup := by
      change (typeASLDiagonalTorus (k := k) m).centralizer.toSubgroup =
        (typeASLDiagonalTorus (k := k) m).toSubgroup
      rw [typeASLDiagonalTorus_centralizer_eq]
    letI := X.carrierAlgebraicGroup
    have hχne : χ ≠ 1 :=
      hX.rootWeight_ne_one_of_centralizer_eq
        (typeASLDiagonalTorus_isSubtorus (k := k) m) hcentralizer χ hEq
    let x : OneParameterParametrization X.carrierVariety := Classical.choice hX.2
    obtain ⟨r, hr, _⟩ := typeASLTangentWeight_eq_rootWeight m hχne
      (oneParameterTangent_isWeightVector
        (typeASLTorus (k := k) m) X x hEq)
    exact ⟨⟨r⟩, hr.symm⟩

/-- The assembled root weight is the quotient of the two diagonal entry
characters indexed by its ordered pair. -/
public theorem typeASLTorusRootWeight_eq_entryCharacters
    (m : ℕ) (r : TypeASLTorusRoot.{u} m) :
    typeASLTorusRootWeight (k := k) m r =
      typeASLDiagonalEntryCharacter (k := k) m
          (typeASLTorusRootIndexEquiv m r).1.2 *
        (typeASLDiagonalEntryCharacter (k := k) m
          (typeASLTorusRootIndexEquiv m r).1.1)⁻¹ := by
  simpa [typeASLTorusRootWeight] using
    typeASLRootWeight_eq_entryCharacters (k := k) m
      (typeASLTorusRootIndexEquiv m r)

theorem typeASLTorusRootWeight_injective (m : ℕ) :
    Function.Injective (typeASLTorusRootWeight (k := k) m) := by
  intro r s h
  apply ULift.ext
  apply (typeASLRootWeight_injective (k := k) m)
  exact h

theorem typeASLTorusRootWeight_neg (m : ℕ) (r : TypeASLTorusRoot.{u} m) :
    typeASLTorusRootWeight (k := k) m (typeASLTorusRootNeg m r) =
      (typeASLTorusRootWeight (k := k) m r)⁻¹ := by
  apply Additive.ofMul.injective
  change typeASLDiagonalCharacterAddEquiv (k := k) m
      (typeASLDiagonalEntryExponent m
        (typeASLRootNeg m (typeASLTorusRootIndexEquiv m r)).1.2 -
        typeASLDiagonalEntryExponent m
          (typeASLRootNeg m (typeASLTorusRootIndexEquiv m r)).1.1) =
    -(typeASLDiagonalCharacterAddEquiv (k := k) m
      (typeASLDiagonalEntryExponent m (typeASLTorusRootIndexEquiv m r).1.2 -
        typeASLDiagonalEntryExponent m (typeASLTorusRootIndexEquiv m r).1.1))
  simp [typeASLRootNeg]

theorem typeASLTorusRootWeight_add (m : ℕ) (r s t : TypeASLTorusRoot.{u} m)
    (h : typeASLTorusRootAdd m r s = some t) :
    typeASLTorusRootWeight (k := k) m t =
      typeASLTorusRootWeight (k := k) m r * typeASLTorusRootWeight (k := k) m s := by
  simp only [typeASLTorusRootAdd, Option.map_eq_some_iff] at h
  obtain ⟨q, hq, ht⟩ := h
  subst t
  have hexp :
      typeASLDiagonalEntryExponent m q.1.2 -
          typeASLDiagonalEntryExponent m q.1.1 =
        (typeASLDiagonalEntryExponent m (typeASLTorusRootIndexEquiv m r).1.2 -
          typeASLDiagonalEntryExponent m (typeASLTorusRootIndexEquiv m r).1.1) +
        (typeASLDiagonalEntryExponent m (typeASLTorusRootIndexEquiv m s).1.2 -
          typeASLDiagonalEntryExponent m (typeASLTorusRootIndexEquiv m s).1.1) := by
    by_cases h₁ : (typeASLTorusRootIndexEquiv m r).1.2 =
        (typeASLTorusRootIndexEquiv m s).1.1
    · by_cases h₂ : (typeASLTorusRootIndexEquiv m r).1.1 =
          (typeASLTorusRootIndexEquiv m s).1.2
      · simp [typeASLRootAdd, h₁, h₂] at hq
      · simp [typeASLRootAdd, h₁, h₂] at hq
        subst q
        rw [← h₁]
        module
    · by_cases h₃ : (typeASLTorusRootIndexEquiv m s).1.2 =
          (typeASLTorusRootIndexEquiv m r).1.1
      · have h₄ : (typeASLTorusRootIndexEquiv m s).1.1 ≠
            (typeASLTorusRootIndexEquiv m r).1.2 := fun h => h₁ h.symm
        simp [typeASLRootAdd, h₁, h₃, h₄] at hq
        subst q
        rw [← h₃]
        module
      · simp [typeASLRootAdd, h₁, h₃] at hq
  apply Additive.ofMul.injective
  change typeASLDiagonalCharacterAddEquiv (k := k) m
      (typeASLDiagonalEntryExponent m q.1.2 -
        typeASLDiagonalEntryExponent m q.1.1) =
    typeASLDiagonalCharacterAddEquiv (k := k) m
        (typeASLDiagonalEntryExponent m (typeASLTorusRootIndexEquiv m r).1.2 -
          typeASLDiagonalEntryExponent m (typeASLTorusRootIndexEquiv m r).1.1) +
      typeASLDiagonalCharacterAddEquiv (k := k) m
        (typeASLDiagonalEntryExponent m (typeASLTorusRootIndexEquiv m s).1.2 -
          typeASLDiagonalEntryExponent m (typeASLTorusRootIndexEquiv m s).1.1)
  rw [← map_add, hexp]

theorem typeASLTorusRootPairing_cast (m : ℕ) (r s : TypeASLTorusRoot.{u} m) :
    (typeASLTorusRootPairing m r s : ℝ) =
      (typeARootPairing m).pairing (typeASLTorusRootIndexEquiv m r)
        (typeASLTorusRootIndexEquiv m s) := by
  rw [typeARootPairing_pairing, typeARootEmbedding_dot]
  simp [typeASLTorusRootPairing]

/-- The pairing carried by the assembled root datum is the standard type-A
pairing after transporting indices through `typeASLTorusRootIndexEquiv`. -/
public theorem typeASLTorusRootData_pairing_cast
    (m : ℕ) (r s : TypeASLTorusRoot.{u} m) :
    ((typeASLTorusRootData (k := k) m).pairing r s : ℝ) =
      (typeARootPairing m).pairing (typeASLTorusRootIndexEquiv m r)
        (typeASLTorusRootIndexEquiv m s) := by
  exact typeASLTorusRootPairing_cast m r s

private lemma entryExponent_eq_rootCoordinate (m : ℕ)
    (i : Fin (m + 1)) (q : Fin m) :
    (typeASLDiagonalEntryExponent m i q : ℝ) =
      basisVector i q.castSucc - basisVector i (Fin.last m) := by
  induction i using Fin.lastCases with
  | last => simp [typeASLDiagonalEntryExponent, basisVector]
  | cast i =>
      simp [typeASLDiagonalEntryExponent, basisVector, Pi.single_apply]

private lemma typeASLExponent_reflect (m : ℕ) (r s : TypeASLTorusRoot.{u} m) :
    (fun q => typeASLDiagonalEntryExponent m
      (typeASLTorusRootIndexEquiv m (typeASLTorusRootReflect m r s)).1.2 q -
      typeASLDiagonalEntryExponent m
        (typeASLTorusRootIndexEquiv m (typeASLTorusRootReflect m r s)).1.1 q) =
      (fun q => typeASLDiagonalEntryExponent m
        (typeASLTorusRootIndexEquiv m s).1.2 q -
        typeASLDiagonalEntryExponent m
          (typeASLTorusRootIndexEquiv m s).1.1 q) -
        typeASLTorusRootPairing m s r • (fun q => typeASLDiagonalEntryExponent m
          (typeASLTorusRootIndexEquiv m r).1.2 q -
          typeASLDiagonalEntryExponent m
            (typeASLTorusRootIndexEquiv m r).1.1 q) := by
  classical
  funext q
  have h := congrFun (typeARoot_reflection_eq_swap
    (typeASLTorusRootIndexEquiv m r).1.1 (typeASLTorusRootIndexEquiv m r).1.2
    (typeASLTorusRootIndexEquiv m s).1.1 (typeASLTorusRootIndexEquiv m s).1.2
    (typeASLTorusRootIndexEquiv m r).2) q.castSucc
  have hlast := congrFun (typeARoot_reflection_eq_swap
    (typeASLTorusRootIndexEquiv m r).1.1 (typeASLTorusRootIndexEquiv m r).1.2
    (typeASLTorusRootIndexEquiv m s).1.1 (typeASLTorusRootIndexEquiv m s).1.2
    (typeASLTorusRootIndexEquiv m r).2) (Fin.last m)
  have hp : (typeASLTorusRootPairing m s r : ℝ) =
      dot (typeARootEmbedding m (typeASLTorusRootIndexEquiv m s))
        (typeARootEmbedding m (typeASLTorusRootIndexEquiv m r)) := by
    simpa [typeARootPairing_pairing] using typeASLTorusRootPairing_cast m s r
  have hp' : (typeASLTorusRootPairing m s r : ℝ) =
      dot (basisVector (typeASLTorusRootIndexEquiv m s).1.1 -
        basisVector (typeASLTorusRootIndexEquiv m s).1.2)
        (basisVector (typeASLTorusRootIndexEquiv m r).1.1 -
          basisVector (typeASLTorusRootIndexEquiv m r).1.2) := by
    simpa [typeARootEmbedding_apply] using hp
  have hreal :
      ((typeASLDiagonalEntryExponent m
        (typeASLTorusRootIndexEquiv m (typeASLTorusRootReflect m r s)).1.2 q -
        typeASLDiagonalEntryExponent m
          (typeASLTorusRootIndexEquiv m (typeASLTorusRootReflect m r s)).1.1 q : ℤ) : ℝ) =
      ((typeASLDiagonalEntryExponent m (typeASLTorusRootIndexEquiv m s).1.2 q -
        typeASLDiagonalEntryExponent m (typeASLTorusRootIndexEquiv m s).1.1 q : ℤ) : ℝ) -
      (typeASLTorusRootPairing m s r : ℝ) *
        ((typeASLDiagonalEntryExponent m (typeASLTorusRootIndexEquiv m r).1.2 q -
          typeASLDiagonalEntryExponent m (typeASLTorusRootIndexEquiv m r).1.1 q : ℤ) : ℝ) := by
    norm_num only [Int.cast_sub, Int.cast_mul]
    rw [entryExponent_eq_rootCoordinate, entryExponent_eq_rootCoordinate,
      entryExponent_eq_rootCoordinate, entryExponent_eq_rootCoordinate,
      entryExponent_eq_rootCoordinate, entryExponent_eq_rootCoordinate]
    simp [typeASLTorusRootReflect, typeASLTorusRootIndexEquiv, typeASLRootReflect]
    simp only [Pi.sub_apply] at h hlast ⊢
    simp [typeASLTorusRootIndexEquiv] at h hlast ⊢
    simp [typeASLTorusRootIndexEquiv] at hp'
    rw [dot_comm] at h hlast
    rw [← hp'] at h hlast
    linear_combination h - hlast
  exact_mod_cast hreal

theorem typeASLTorusRootWeight_reflect (m : ℕ) (r s : TypeASLTorusRoot.{u} m) :
    typeASLTorusRootWeight (k := k) m (typeASLTorusRootReflect m r s) =
      typeASLTorusRootWeight (k := k) m s *
        typeASLTorusRootWeight (k := k) m r ^ (-typeASLTorusRootPairing m s r) := by
  apply Additive.ofMul.injective
  change typeASLDiagonalCharacterAddEquiv (k := k) m
      (fun q => typeASLDiagonalEntryExponent m
        (typeASLTorusRootIndexEquiv m (typeASLTorusRootReflect m r s)).1.2 q -
        typeASLDiagonalEntryExponent m
          (typeASLTorusRootIndexEquiv m (typeASLTorusRootReflect m r s)).1.1 q) =
    typeASLDiagonalCharacterAddEquiv (k := k) m
        (fun q => typeASLDiagonalEntryExponent m (typeASLTorusRootIndexEquiv m s).1.2 q -
          typeASLDiagonalEntryExponent m (typeASLTorusRootIndexEquiv m s).1.1 q) +
      (-typeASLTorusRootPairing m s r) • typeASLDiagonalCharacterAddEquiv (k := k) m
        (fun q => typeASLDiagonalEntryExponent m (typeASLTorusRootIndexEquiv m r).1.2 q -
          typeASLDiagonalEntryExponent m (typeASLTorusRootIndexEquiv m r).1.1 q)
  rw [← map_zsmul, ← map_add]
  exact congrArg (fun v : Fin m → ℤ =>
      typeASLDiagonalCharacterAddEquiv (k := k) m v) (by
    simpa [sub_eq_add_neg, neg_smul] using typeASLExponent_reflect m r s)

private lemma rootExponent_coroot_sum (m : ℕ)
    (i j a b : Fin (m + 1)) :
    ∑ q : Fin m,
      (typeASLDiagonalEntryExponent m j q -
        typeASLDiagonalEntryExponent m i q) *
        ((if b = q.castSucc then 1 else 0) -
          (if a = q.castSucc then 1 else 0)) =
      (if i = a then 1 else 0) - (if i = b then 1 else 0) -
        (if j = a then 1 else 0) + (if j = b then 1 else 0) := by
  induction i using Fin.lastCases <;>
    induction j using Fin.lastCases <;>
      induction a using Fin.lastCases <;>
        induction b using Fin.lastCases <;>
          simp [typeASLDiagonalEntryExponent, Pi.single_apply, Fin.castSucc_inj,
            eq_comm, Fin.castSucc_ne_last, Finset.sum_sub_distrib, mul_sub] <;> ring

theorem typeASLTorusRootWeightPairing_rootWeight (m : ℕ) (r s : TypeASLTorusRoot.{u} m) :
    typeASLTorusRootWeightPairing (k := k) m (typeASLTorusRootWeight (k := k) m r) s =
      typeASLTorusRootPairing m r s := by
  change characterCocharacterPairing (typeASLTorus (k := k) m)
      (typeASLRootCocharacter (k := k) m (typeASLTorusRootIndexEquiv m s))
      (Additive.ofMul (typeASLRootWeight (k := k) m (typeASLTorusRootIndexEquiv m r))) = _
  rw [typeASLRootWeight_cocharacter_pairing]
  classical
  exact rootExponent_coroot_sum m
    (typeASLTorusRootIndexEquiv m r).1.1 (typeASLTorusRootIndexEquiv m r).1.2
    (typeASLTorusRootIndexEquiv m s).1.1 (typeASLTorusRootIndexEquiv m s).1.2

/-- Evaluating a root character on the explicit root cocharacter gives the
assembled Cartan integer. -/
public theorem typeASLTorusRootWeight_cocharacter_pairing
    (m : ℕ) (r s : TypeASLTorusRoot.{u} m) :
    characterCocharacterPairing (typeASLTorus (k := k) m)
        (typeASLTorusRootCocharacter (k := k) m s)
        (Additive.ofMul (typeASLTorusRootWeight (k := k) m r)) =
      typeASLTorusRootPairing m r s := by
  exact typeASLTorusRootWeightPairing_rootWeight (k := k) m r s

theorem typeASLTorusRootPairing_self (m : ℕ) (r : TypeASLTorusRoot.{u} m) : typeASLTorusRootPairing m r r = 2 := by
  have h := (typeASLTorusRootIndexEquiv m r).2
  simp [typeASLTorusRootPairing, h, h.symm]

theorem typeASLTorusRootHeight_neg (m : ℕ) (r : TypeASLTorusRoot.{u} m) :
    typeASLTorusRootHeight m (typeASLTorusRootNeg m r) = -typeASLTorusRootHeight m r := by
  simp [typeASLTorusRootHeight, typeASLTorusRootNeg, typeASLRootNeg, typeASLTorusRootIndexEquiv]

theorem typeASLTorusRootHeight_add (m : ℕ) (r s t : TypeASLTorusRoot.{u} m)
    (h : typeASLTorusRootAdd m r s = some t) :
    typeASLTorusRootHeight m t = typeASLTorusRootHeight m r + typeASLTorusRootHeight m s := by
  simp only [typeASLTorusRootAdd, Option.map_eq_some_iff] at h
  obtain ⟨q, hq, ht⟩ := h
  subst t
  by_cases h₁ : (typeASLTorusRootIndexEquiv m r).1.2 =
      (typeASLTorusRootIndexEquiv m s).1.1
  · by_cases h₂ : (typeASLTorusRootIndexEquiv m r).1.1 =
        (typeASLTorusRootIndexEquiv m s).1.2
    · simp [typeASLRootAdd, h₁, h₂] at hq
    · simp [typeASLRootAdd, h₁, h₂] at hq
      subst q
      have h₁val : r.down.1.2.val = s.down.1.1.val := by
        simpa [typeASLTorusRootIndexEquiv] using congrArg Fin.val h₁
      simp [typeASLTorusRootHeight, typeASLTorusRootIndexEquiv]
      omega
  · by_cases h₃ : (typeASLTorusRootIndexEquiv m s).1.2 =
        (typeASLTorusRootIndexEquiv m r).1.1
    · have h₄ : (typeASLTorusRootIndexEquiv m s).1.1 ≠
          (typeASLTorusRootIndexEquiv m r).1.2 := fun h => h₁ h.symm
      simp [typeASLRootAdd, h₁, h₃, h₄] at hq
      subst q
      have h₃val : s.down.1.2.val = r.down.1.1.val := by
        simpa [typeASLTorusRootIndexEquiv] using congrArg Fin.val h₃
      simp [typeASLTorusRootHeight, typeASLTorusRootIndexEquiv]
      omega
    · simp [typeASLRootAdd, h₁, h₃] at hq

theorem typeASLTorusPositiveRoots_eq (m : ℕ) :
    typeASLTorusPositiveRoots m = {r | (typeASLTorusRootIndexEquiv m r).1.1.val <
      (typeASLTorusRootIndexEquiv m r).1.2.val} := by
  ext r
  simp [typeASLTorusPositiveRoots, typeASLTorusRootHeight]

theorem typeASLTorusSimpleRoots_iff (m : ℕ) (r : TypeASLTorusRoot.{u} m) :
    r ∈ typeASLTorusSimpleRoots m ↔
      r ∈ typeASLTorusPositiveRoots m ∧
        ∀ β γ, typeASLTorusRootAdd m β γ = some r →
          ¬ (β ∈ typeASLTorusPositiveRoots m ∧ γ ∈ typeASLTorusPositiveRoots m) := by
  constructor
  · rintro ⟨i, rfl⟩
    constructor
    · simp [typeASLTorusPositiveRoots, typeASLTorusRootHeight, typeASLTorusRootIndexEquiv,
        typeASimpleRootIndex_pair]
    · intro β γ hadd hβγ
      have hheight := typeASLTorusRootHeight_add m β γ ⟨typeASimpleRootIndex m i⟩ hadd
      have hone : typeASLTorusRootHeight m (⟨typeASimpleRootIndex m i⟩ : TypeASLTorusRoot.{u} m) = 1 := by
        simp [typeASLTorusRootHeight, typeASLTorusRootIndexEquiv, typeASimpleRootIndex_pair]
      rw [hone] at hheight
      have hβpos' := hβγ.1
      have hγpos' := hβγ.2
      change 0 < typeASLTorusRootHeight m β at hβpos'
      change 0 < typeASLTorusRootHeight m γ at hγpos'
      have hβ : 1 ≤ typeASLTorusRootHeight m β := by omega
      have hγ : 1 ≤ typeASLTorusRootHeight m γ := by omega
      omega
  · rintro ⟨hrpos, hindecomp⟩
    have hridx : typeASLTorusRootIndexEquiv m r = r.down := rfl
    have hlt : (typeASLTorusRootIndexEquiv m r).1.1.val <
        (typeASLTorusRootIndexEquiv m r).1.2.val := by
      simpa [typeASLTorusPositiveRoots, typeASLTorusRootHeight] using hrpos
    let i : Fin m := ⟨(typeASLTorusRootIndexEquiv m r).1.1.val, by
      have := (typeASLTorusRootIndexEquiv m r).1.1.isLt
      omega⟩
    have hiVal : i.val = (typeASLTorusRootIndexEquiv m r).1.1.val := rfl
    have hi : (typeASLTorusRootIndexEquiv m r).1.1 = i.castSucc := by
      apply Fin.ext
      rfl
    by_cases hadj : i.val + 1 = (typeASLTorusRootIndexEquiv m r).1.2.val
    · have hj : (typeASLTorusRootIndexEquiv m r).1.2 = i.succ := by
        apply Fin.ext
        dsimp [i]
        omega
      have hi' : r.down.1.1 = i.castSucc := by simpa [hridx] using hi
      have hj' : r.down.1.2 = i.succ := by simpa [hridx] using hj
      refine ⟨i, ?_⟩
      apply ULift.ext
      exact Subtype.ext (Prod.ext
        (by simpa [typeASimpleRootIndex_pair] using hi'.symm)
        (by simpa [typeASimpleRootIndex_pair] using hj'.symm))
    · let c : Fin (m + 1) := i.succ
      have hstep : i.val + 1 < (typeASLTorusRootIndexEquiv m r).1.2.val := by omega
      have hstep' : i.val + 1 < r.down.1.2.val := by
        simpa [hridx] using hstep
      have hcVal : c.val = i.val + 1 := rfl
      let β : TypeASLTorusRoot.{u} m := ⟨⟨(i.castSucc, c), by
        intro h
        have := congrArg Fin.val h
        dsimp [c] at this
        omega⟩⟩
      let γ : TypeASLTorusRoot.{u} m := ⟨⟨(c, (typeASLTorusRootIndexEquiv m r).1.2), by
        intro h
        have := congrArg Fin.val h
        dsimp [c] at this
        omega⟩⟩
      have hic : i.castSucc ≠ c := by
        dsimp [c]
        omega
      have hcr : c ≠ (typeASLTorusRootIndexEquiv m r).1.2 := by
        intro h
        have := congrArg Fin.val h
        dsimp [c] at this
        omega
      have hbr : i.castSucc ≠ (typeASLTorusRootIndexEquiv m r).1.2 := by
        intro h
        have := congrArg Fin.val h
        have hiVal' := hiVal
        omega
      have hadd : typeASLTorusRootAdd m β γ = some r := by
        simp only [typeASLTorusRootAdd, Option.map_eq_some_iff]
        refine ⟨⟨(i.castSucc, (typeASLTorusRootIndexEquiv m r).1.2), hbr⟩, ?_, ?_⟩
        · exact typeASLRootAdd_forward m i.castSucc c
            (typeASLTorusRootIndexEquiv m r).1.2 hic hcr hbr
        · apply ULift.ext
          apply Subtype.ext
          exact Prod.ext hi.symm rfl
      have hβpos : β ∈ typeASLTorusPositiveRoots m := by
        simp [typeASLTorusPositiveRoots, typeASLTorusRootHeight, β, typeASLTorusRootIndexEquiv, c]
      have hγpos : γ ∈ typeASLTorusPositiveRoots m := by
        simp [typeASLTorusPositiveRoots, typeASLTorusRootHeight, γ, typeASLTorusRootIndexEquiv, c] ; omega
      exact False.elim ((hindecomp β γ hadd) ⟨hβpos, hγpos⟩)

theorem typeASLTorusRootWeightPairing_spec (m : ℕ)
    (χ : TorusWeight (typeASLTorus (k := k) m)) (β : TypeASLTorusRoot.{u} m) :
    WeightCocharacterEquation (typeASLTorus (k := k) m) χ
      (typeASLTorusRootCocharacter (k := k) m β)
      (typeASLTorusRootWeightPairing (k := k) m χ β) := by
  exact characterCocharacterPairing_spec (typeASLTorus (k := k) m) χ
    (typeASLRootCocharacter (k := k) m (typeASLTorusRootIndexEquiv m β))

theorem typeASLTorusRootData_isRealization (m : ℕ) :
    (typeASLTorusRootData (k := k) m).IsRealization := by
  refine ⟨typeASLTorusRootWeight_injective (k := k) m, typeASLTorusRootWeight_range (k := k) m, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro α
    change IsTorusRootSubgroup (typeASLTorus (k := k) m)
        (typeASLTorusRootSubgroup (k := k) m α) ∧
      RootWeightEquation (typeASLTorus (k := k) m)
        (typeASLTorusRootSubgroup (k := k) m α) (typeASLTorusRootWeight (k := k) m α)
    simpa [typeASLTorusRootSubgroup, typeASLTorusRootWeight] using
      (⟨⟨typeASLRootSubgroup_invariant (k := k) m (typeASLTorusRootIndexEquiv m α),
          typeASLRootSubgroup_isOneParameter (k := k) m (typeASLTorusRootIndexEquiv m α)⟩,
        typeASLRootWeight_equation (k := k) m (typeASLTorusRootIndexEquiv m α)⟩ :
        IsTorusRootSubgroup (typeASLTorus (k := k) m)
          (typeASLRootSubgroup (k := k) m (typeASLTorusRootIndexEquiv m α)) ∧
          RootWeightEquation (typeASLTorus (k := k) m)
            (typeASLRootSubgroup (k := k) m (typeASLTorusRootIndexEquiv m α))
            (typeASLRootWeight (k := k) m (typeASLTorusRootIndexEquiv m α)))
  · exact typeASLTorusRootWeight_neg (k := k) m
  · exact typeASLTorusRootWeight_add (k := k) m
  · exact typeASLTorusRootWeight_reflect (k := k) m
  · exact typeASLTorusRootPairing_self m
  · exact typeASLTorusRootWeightPairing_rootWeight (k := k) m
  · exact typeASLTorusRootHeight_neg m
  · exact typeASLTorusRootHeight_add m
  · change typeASLTorusPositiveRoots m = {r | 0 < typeASLTorusRootHeight m r}
    rfl
  · exact typeASLTorusSimpleRoots_iff m
  · exact typeASLTorusRootWeightPairing_spec (k := k) m



end

end

end Theory.AlgebraicGroup
