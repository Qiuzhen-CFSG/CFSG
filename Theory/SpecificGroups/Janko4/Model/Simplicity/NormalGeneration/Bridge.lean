module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.Words
public import Theory.SpecificGroups.Janko4.Model.Simplicity.Reduction
public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates

/-!
# Odd-order bridges for normal generation in the J₄ matrix group

For each ATLAS prime representative `r`, choose a product `y` of conjugates
of `r`. If `a*y` has odd order, killing `r` kills `a`: the image of `a` has
order dividing both two and an odd number. The certified generator relations
then kill `b`. This requires neither the group order nor a recognition theorem.

The representatives come from https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/J4/ .
The additional bridge words are explicit computational witnesses, whose matrix
identities are checked in the certificate modules importing this file.
-/

@[expose] public section
namespace Janko4.Simplicity.NormalGeneration

/-- Empty words select a single representative; other words conjugate a second copy. -/
def conjugator : Fin 12 → String :=
  !["", "bab", "bab", "", "b", "babb", "", "", "b", "bb", "babb", ""]

/-- Odd exponents of the twelve bridge words. -/
def bridgeExponent : Fin 12 → ℕ := ![1, 23, 15, 11, 31, 31, 33, 43, 15, 21, 11, 23]

/-- A product belonging to the normal closure of the selected representative. -/
def normalProduct {G : Type*} [Group G] (a b : G) (i : Fin 12) : G :=
  let r := primeRepresentative a b i
  if conjugator i = "" then r
  else r * (word a b (conjugator i) * r * (word a b (conjugator i))⁻¹)

theorem normalProduct_mem {G : Type*} [Group G] (a b : G) (i : Fin 12) :
    normalProduct a b i ∈ Subgroup.normalClosure ({primeRepresentative a b i} : Set G) := by
  let N := Subgroup.normalClosure ({primeRepresentative a b i} : Set G)
  have hr : primeRepresentative a b i ∈ N :=
    Subgroup.subset_normalClosure (Set.mem_singleton _)
  change (if conjugator i = "" then _ else _) ∈ N
  split
  · exact hr
  · exact N.mul_mem hr (Subgroup.Normal.conj_mem inferInstance _ hr _)

set_option maxRecDepth 10000 in
theorem bridgeExponent_coprime (i : Fin 12) : Nat.Coprime 2 (bridgeExponent i) := by
  fin_cases i <;> decide

theorem a_sq (hA : matrixA * matrixA = 1) : a hA ^ 2 = 1 := by
  apply toMatrix_injective
  rw [map_pow, map_one, toMatrix_a, pow_two]
  exact hA

theorem a_inv (hA : matrixA * matrixA = 1) : (a hA)⁻¹ = a hA := by
  apply inv_eq_of_mul_eq_one_left
  simpa only [pow_two] using a_sq hA

theorem b_inv (hB : matrixB ^ 4 = 1) : (b hB)⁻¹ = b hB ^ 3 := by
  apply inv_eq_of_mul_eq_one_left
  simpa only [← pow_succ] using b_pow_four hB

/-- A checked odd-order bridge suffices for one representative. -/
theorem normalClosure_eq_top_of_bridge
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) (i : Fin 12)
    (hbridge : (a hA * normalProduct (a hA) (b hB) i) ^ bridgeExponent i = 1) :
    Subgroup.normalClosure ({primeRepresentative (a hA) (b hB) i} : Set Model) = ⊤ := by
  let N := Subgroup.normalClosure ({primeRepresentative (a hA) (b hB) i} : Set Model)
  let q := QuotientGroup.mk' N
  have hy : q (normalProduct (a hA) (b hB) i) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (normalProduct_mem _ _ _)
  have ha2 : q (a hA) ^ 2 = 1 := by simpa using congrArg q (a_sq hA)
  have haodd : q (a hA) ^ bridgeExponent i = 1 := by
    simpa [hy] using congrArg q hbridge
  have haN : a hA ∈ N := (QuotientGroup.eq_one_iff _).mp
    ((pow_eq_one_iff_of_coprime (bridgeExponent_coprime i)).mp ⟨ha2, haodd⟩)
  have hle : Subgroup.normalClosure ({a hA} : Set Model) ≤ N :=
    Subgroup.normalClosure_le_normal (by simpa using haN)
  have hab37 : (a hA * b hB) ^ 37 = 1 := by
    apply toMatrix_injective
    simpa only [map_pow, map_mul, map_one, toMatrix_a, toMatrix_b] using matrixAB_pow_37
  rw [normalClosure_a_eq_top (toMatrix_a hA) (toMatrix_b hB) (b_pow_four hB) hab37] at hle
  exact top_unique hle

end Janko4.Simplicity.NormalGeneration
