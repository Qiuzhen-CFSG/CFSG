module

public import Theory.SpecificGroups.PSL3Three.Generators
public import Theory.SpecificGroups.PSL3Three.FiniteModel

/-!
# Word certificates for maximal matrix subgroups

A right-coset transition table proves coverage using the explicit ambient
matrix generators. A second table reduces those cosets to double cosets.
For each double coset outside the candidate, words in its representative and
the candidate generators recover every ambient generator. Thus every proper
extension is the whole group. All equations and subgroup memberships refer to
the actual matrices and candidates, with no subgroup-classification assumption.

Source: the elementary extension criterion for maximality, applied to the
candidates of GLS III, Theorem 6.5.3(a–c).
-/

namespace Matrix.PSL3Three
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration

/-- The concrete certificate obligations for a maximal matrix subgroup. The
candidate generators need only lie in the candidate; equality with the
subgroup they generate is not assumed. -/
public theorem isCoatom_of_matrixCertificate {n r d : Nat}
    (K : Subgroup SL) (hproper : K ≠ ⊤)
    (gen : Fin n → SL) (inverse : Fin n → Fin n)
    (hinverse : ∀ i, gen (inverse i) = (gen i)⁻¹)
    (hgen : ∀ i, gen i ∈ K)
    (rep : Fin r → SL) (table : RightCosetTable 4 n r)
    (htable : table.Valid ambientGenerators gen rep)
    (doubleRep : Fin d → SL) (index : Fin r → Fin d)
    (left right : Fin r → List (Fin n))
    (hdouble : ∀ a, rep a = evalWord gen (left a) * doubleRep (index a) *
      evalWord gen (right a))
    (extension : Fin d → Fin 4 → List (Fin (n + 2)))
    (hextension : ∀ a, doubleRep a ∈ K ∨ ∀ i,
      evalWord (extensionGen gen (doubleRep a)) (extension a i) = ambientGenerators i) :
    IsCoatom K := by
  have hword : wordSubgroup gen inverse hinverse ≤ K := wordSubgroup_le _ _ _ _ hgen
  have hcover := table.sound ambientGenerators ambientInverse ambientGenerators_inverse
    ambient_wordSubgroup_eq_top gen inverse hinverse rep htable
  apply isCoatom_of_doubleCosetCover K doubleRep hproper
  · intro x
    obtain ⟨a, k, hk, hx⟩ := hcover x
    refine ⟨index a, k * evalWord gen (left a), evalWord gen (right a),
      K.mul_mem (hword hk) (evalWord_mem gen K hgen _), evalWord_mem gen K hgen _, ?_⟩
    rw [hx, hdouble]
    simp only [mul_assoc]
  · intro a ha
    obtain h | h := hextension a
    · exact (ha h).elim
    apply eq_top_of_ambientGenerators_mem
    intro i
    rw [← h i]
    apply evalWord_mem
    intro j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simpa only [extensionGen, Fin.addCases_left] using
        (Subgroup.mem_sup_left (hgen k) : gen k ∈ K ⊔ Subgroup.zpowers (doubleRep a))
    · simp only [extensionGen, Fin.addCases_right]
      split
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
      · exact Subgroup.mem_sup_right ((Subgroup.zpowers _).inv_mem (Subgroup.mem_zpowers _))

end Matrix.PSL3Three
