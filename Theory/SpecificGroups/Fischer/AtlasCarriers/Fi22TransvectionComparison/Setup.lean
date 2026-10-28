module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22CentralizerAction
public import Theory.SpecificGroups.ClassicalUnitary.SixDimensionalBinaryTransvections
public import Theory.GroupAction.SchreierActionCertificate

/-!
# Commuting-conjugate certificates for the Fi22 action comparison

The two independent computations concern (1) generation of the ATLAS
involution centralizer by the conjugates commuting with that involution,
and (2) their action table in isotropic-line coordinates. We fix the common
interfaces here so neither computation depends on the other.

The generation criterion is an actual application of Schreier rewriting to
the two defining permutations of `Fi22.Carrier`. Its root-labeling and edge
hypotheses still require certificates. On the unitary side, the additional
singleton represents the identity and every other label represents the
specified matrix transvection `I + v vᴴ` acting on isotropic lines.

Source: GLS3 Table 5.3t, `refs/KGroup/GLS3/Chapter5(sec3-).tex`, including
the conjugation action on the class of 3-transpositions. The centralizer
identification itself is not asserted by these definitions or criteria.
-/

@[expose] public section

namespace Sporadic.Fischer.Fi22.TransvectionComparison
open Theory.SpecificGroups

/-- The second published generator, in the actual generated subgroup. -/
def atlasB : Carrier := ⟨generatorB, Subgroup.subset_closure (by simp)⟩

/-- The two defining generators as elements of the Fi22 carrier. -/
def atlasGenerators : Set Carrier := {atlasA, atlasB}

/-- The carrier definition supplies generation internally as well. -/
theorem atlasGenerators_closure : Subgroup.closure atlasGenerators = ⊤ := by
  have hs : atlasGenerators =
      (generated.subtype : Carrier → Equiv.Perm (Fin 3510)) ⁻¹' {generatorA, generatorB} := by
    ext g
    simp only [atlasGenerators, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · rintro (rfl | rfl) <;> simp [atlasA, atlasB]
    · rintro (ha | hb)
      · exact Or.inl (Subtype.ext ha)
      · exact Or.inr (Subtype.ext hb)
  rw [hs]
  exact Subgroup.closure_closure_coe_preimage

/-- Conjugates in Fi22 of the distinguished involution, restricted to its
actual centralizer. No geometric identification is part of this set. -/
def commutingConjugates : Set centralizerA := {t | IsConj atlasA t.val}

/-- The subgroup they generate, viewed in the ambient Fi22 carrier. -/
def commutingConjugateSubgroup : Subgroup Carrier :=
  (Subgroup.closure commutingConjugates).map centralizerA.subtype

/-- Every member remains in the specified relative centralizer. -/
theorem commutingConjugateSubgroup_le : commutingConjugateSubgroup ≤ centralizerA := by
  rintro g ⟨t, _, rfl⟩
  exact t.property

/-- A finite conjugate-labeling and Schreier-edge certificate is sufficient
to prove that the commuting conjugates generate the entire centralizer. -/
theorem commutingConjugates_generate_of_edges
    (rep root : Fin 3510 → Carrier) (base : Fin 3510)
    (hbase : rep base = 1) (hrootBase : root base = atlasA)
    (hrootFiber : ∀ x, root x = atlasA → x = base)
    (hroot : ∀ s ∈ atlasGenerators, ∀ x,
      root (inclusion s x) = s * root x * s⁻¹)
    (hedge : ∀ s ∈ atlasGenerators, ∀ x,
      (rep (inclusion s x))⁻¹ * s * rep x ∈ commutingConjugateSubgroup) :
    Subgroup.closure commutingConjugates = ⊤ := by
  have hle : centralizerA ≤ commutingConjugateSubgroup :=
    Theory.GroupAction.SchreierActionCertificate.centralizer_le_of_edges
      inclusion atlasGenerators atlasGenerators_closure commutingConjugateSubgroup
      rep root base atlasA hbase hrootBase hrootFiber hroot hedge
  apply top_unique
  intro t _
  obtain ⟨s, hs, hst⟩ := hle t.property
  have h : s = t := Subtype.ext hst
  exact h ▸ hs

/-- The singleton labels the identity; an isotropic line labels its actual
unitary transvection permutation. -/
noncomputable def pointTransvection : U6Two.PointWithSingleton →
    Equiv.Perm U6Two.PointWithSingleton
  | none => 1
  | some p => U6Two.transvectionPermutation p

theorem pointTransvection_none : pointTransvection none = 1 := rfl

theorem pointTransvection_some (p : U6Two.IsotropicPoint) :
    pointTransvection (some p) = U6Two.transvectionPermutation p := rfl

/-- Adjoining the singleton identity leaves the transvection-generated group unchanged. -/
theorem pointTransvection_closure :
    Subgroup.closure (Set.range pointTransvection) =
      U6Two.transvectionPermutationSubgroup := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨p, rfl⟩
    cases p with
    | none => exact Subgroup.one_mem _
    | some p => exact Subgroup.subset_closure ⟨p, rfl⟩
  · rw [U6Two.transvectionPermutationSubgroup, Subgroup.closure_le]
    rintro _ ⟨p, rfl⟩
    exact Subgroup.subset_closure ⟨some p, rfl⟩

end Sporadic.Fischer.Fi22.TransvectionComparison
