module
public import Theory.SpecificGroups.ClassicalUnitary.OddFourRanks.Torus
public import Theory.SpecificGroups.ClassicalUnitary.EvenSmallRanks
public import Theory.GroupTheory.PrimeRankWitness
/-!
# Three independent signs in a special unitary four-space

The determinant-one diagonal torus retains all three binary coordinates before
projectivization. This supplies the SU4 block used inside every larger PSU,
where an unused coordinate makes the block map injective.
Source: Aschbacher--Smith A.2.12, printed p.36.
-/
public noncomputable section
open Matrix BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.ClassicalUnitary.TwoRank.Diagonal
variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 4 F) (hJ : J.form = 1)
variable {q : ℕ} (ho : Odd q) (hcard : Nat.card F = q^2) (hconj : ∀x,J.conj x=x^q)
include ho in
private theorem hd : 2 ∣ q+1 := by
  have h := Nat.odd_iff.mp ho
  omega

def embedding : (Fin 3 → rootsOfUnity 2 F) →* J.specialSubgroup :=
  OddFourRanks.torusSpecial J hJ (rootsOfUnity 2 F) (OddFourRanks.roots_norm J hconj (hd ho))
omit [Finite F] in
theorem embedding_injective : Function.Injective (embedding J hJ ho hconj) := by
  intro a b h
  have he (i : Fin 4) := congrArg (fun g : J.specialSubgroup => g.val.val i i) h
  funext i
  apply Subtype.ext
  apply Units.ext
  fin_cases i
  · exact he 0
  · exact he 1
  · exact he 2

include hJ ho hcard hconj in
theorem three_le : 3 ≤ primeRank 2 J.specialSubgroup := by
  let : Finite (GL (Fin 4) F) := Finite.of_injective Units.val Units.val_injective
  apply primeRank_ge_of_elementary_embedding (f:=embedding J hJ ho hconj)
  · intro a
    funext i
    exact Subtype.ext ((mem_rootsOfUnity 2 _).mp (a i).property)
  · rw [Nat.card_fun,Nat.card_fin,FiniteField.card_rootsOfUnity_of_dvd]
    rw [hcard]
    have hh := Nat.odd_iff.mp (ho.pow (n:=2))
    omega
  · exact embedding_injective J hJ ho hconj
end Theory.SpecificGroups.ClassicalUnitary.TwoRank.Diagonal
