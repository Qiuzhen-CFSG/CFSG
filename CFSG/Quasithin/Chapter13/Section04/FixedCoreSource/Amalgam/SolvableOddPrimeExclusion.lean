module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SolvableMatrixPair
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SolvableOddPrimeReduction
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SolvableTwoThree
public import Theory.GroupTheory.PrimeRootsNormalComplement

/-!
# Excluding the odd-prime obstruction in the original solvable pair

If both residuals move a prime core, the constructed matrix range is a
solvable Goldschmidt triple with distinct vertex two-cores. The faithful
range inclusion contradicts the prime-field matrix theorem. Thus the
second residual centralizes the rank-two prime core.

That core has full ambient p-rank, so its centralizer has a normal
p-complement. The p-residual of this normal centralizer contains the
second local residual and has order prime to p. Together with the first
vertex it generates the whole quotient, whose order is consequently prime
to p, contradicting the actual prime supplied by the obstruction.

The final applications discharge the two-three premise in the full
omega-action kernel and actual X/O₂(X) model theorems. The genuine source
relative-normality and prime-to-three residual clause remains explicit.
The six-dimensional module, ordinary Thompson normality and plane
exclusion of case (iii) are separate remaining source obligations.
Source: Aschbacher--Smith 13.4.7, printed pp.901--902.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem local_card_coprime_large_prime {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (A : Subgroup G) (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3)) :
    Nat.Coprime p (Nat.card A) := by
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := A)).exists_card_eq
  rw [SymmetricThreeTwoCore.card_eq eA,hn]
  have h2 := (Nat.coprime_primes (Fact.out : p.Prime) Nat.prime_two).mpr hp2
  have h3 := (Nat.coprime_primes (Fact.out : p.Prime) Nat.prime_three).mpr hp3
  exact (h2.mul_right h3).mul_right (h2.pow_right n)

/-- A local residual centralizing a full rank-two prime core excludes that prime
from the order of the whole pair, via the actual normal centralizer. -/
theorem pair_coprime_of_residual_centralizes_rank_two_core
    {A B : Subgroup G} (hg : ChapterF.IsGoldschmidtTriple A B)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hr : primeRank p G ≤ 2) (hU : primeRank p (pCore p G) = 2)
    (hB : (pResidual 2 B).map B.subtype ≤ centralizer (pCore p G : Set G)) :
    Nat.Coprime p (Nat.card G) := by
  let C := centralizer (pCore p G : Set G)
  let N := (pResidual p C).map C.subtype
  have hcomp := centralizer_hasNormalPComplement_of_rank_two hp2 (pCore p G) hr hU
  have hcopN : Nat.Coprime p (Nat.card N) := by
    rw [card_map_of_injective C.subtype_injective,
      pResidual_eq_pPrimeCore_of_hasNormalPComplement hcomp]
    exact pPrimeCore_coprime_card
  have hcopB := local_card_coprime_large_prime hp2 hp3 B hg.quotient_right.some
  have hBN : (pResidual 2 B).map B.subtype ≤ N := by
    intro b hb
    let x : C := ⟨b,hB hb⟩
    have hx : x ∈ pResidual p C := by
      apply mem_pResidual_of_orderOf_coprime
      apply hcopB.of_dvd_right
      rw [←Subgroup.orderOf_coe x]
      exact B.orderOf_dvd_natCard (map_subtype_le _ hb)
    exact mem_map_of_mem C.subtype hx
  have hgen : N ⊔ A = ⊤ := top_unique
    (hg.symm.left_residual_sup_right ▸ sup_le_sup_right hBN A)
  have hcard : Nat.card (N ⊓ A : Subgroup G) * Nat.card (N ⊔ A : Subgroup G) =
      Nat.card N * Nat.card A :=
    (card_mul_eq_card_inf_mul_card_sup_of_normalizes N A le_normalizer_of_normal).symm
  apply (hcopN.mul_right (local_card_coprime_large_prime hp2 hp3 A hg.quotient_left.some)).of_dvd_right
  rw [←hcard,hgen,card_top]
  exact dvd_mul_left _ _

/-- The odd-prime obstruction cannot occur in the literal original two-core
quotient. Both matrix-action branches are discharged. -/
theorem original_pair_solvable_twoThree_quotient
    {T : Sylow 2 G} {L V A B : Subgroup G}
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hcores : A.pCoreIn 2 ≠ B.pCoreIn 2) (hs : Group.IsSolvable (A ⊔ B : Subgroup G)) :
    IsPiGroup twoThreePrimes ((A ⊔ B : Subgroup G) ⧸ pCore 2 (A ⊔ B : Subgroup G)) := by
  by_contra hnot
  let X := A ⊔ B
  let Q := X ⧸ pCore 2 X
  let q := QuotientGroup.mk' (pCore 2 X)
  let A₀ := (A.subgroupOf X).map q
  let B₀ := (B.subgroupOf X).map q
  obtain ⟨p,hp2,hp3,hdiv,_,hU,f,hsf,_,_,_,_,_,_,hboth⟩ :=
    original_pair_solvable_odd_prime_obstruction h₀ D m hTA hTB eA eB hne
      hindexA hindexB hcores hs hnot
  let : Fact p.val.Prime := ⟨p.property⟩
  have hB : (pResidual 2 B₀).map B₀.subtype ≤ centralizer (pCore p.val Q : Set Q) := by
    by_contra hm
    obtain ⟨_,_,_,hne',hg'⟩ := hboth hm
    exact hne' (solvable_pair_matrix_cores_equal hg' hsf f.range.subtype f.range.subtype_injective)
  have hlocal := original_pair_local D m hTA hTB eA eB hne hindexA hindexB
  have hrX := (Chapter3.sqtk_of_mem_H h₀.qtke hlocal.1).stronglyQuasithin
    p.val p.property (p.property.odd_of_ne_two hp2)
  have hcop : Nat.Coprime p.val (Nat.card (pCore 2 X)) := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := X)).exists_card_eq
    rw [hn]
    exact ((Nat.coprime_primes p.property Nat.prime_two).mpr hp2).pow_right n
  have hrQ : primeRank p.val Q ≤ 2 :=
    (primeRank_quotient_le_of_coprime p.val (pCore 2 X) hcop).trans hrX
  have hg := (pair_goldschmidt hTA hTB eA eB hne).quotient_twoCore
  exact (p.property.coprime_iff_not_dvd.mp
    (pair_coprime_of_residual_centralizes_rank_two_core hg hp2 hp3 hrQ hU hB)) hdiv


variable {T : Sylow 2 G} {L V A B : Subgroup G}
variable (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hcentral : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      X ∈ Chapter1.HOver G (T : Set G) →
        (K₁.subgroupOf C₁).Normal ∧ (K₂.subgroupOf C₂).Normal ∧
        ((primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
          (primeToResidual 3 C₂).map C₂.subtype = K₂))
include h₀ D m hTA hTB eA eB hne hindexA hindexB hcentral


/-- The original solvable unequal-core pair has the actual two-core quotient
models and full action kernel, with the odd-prime premise discharged. -/
theorem original_pair_solvable_models
    (hcores : A.pCoreIn 2 ≠ B.pCoreIn 2) (hs : Group.IsSolvable (A ⊔ B : Subgroup G)) :
    let X := A ⊔ B
    let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
    X ⊓ centralizer (W : Set G) = X.pCoreIn 2 ∧
      (Nonempty ((X ⧸ pCore 2 X) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨
        Nonempty ((X ⧸ pCore 2 X) ≃* MarkedCubicRecognition.HeisenbergExtension)) := by
  exact original_pair_twoThree_models h₀ D m hTA hTB eA eB hne
    hindexA hindexB hcentral hcores hs
    (original_pair_solvable_twoThree_quotient h₀ D m hTA hTB eA eB hne
      hindexA hindexB hcores hs)

/-- Noncommuting residual actions select the literal Heisenberg extension
and identify the entire action kernel, without a two-three-group hypothesis. -/
theorem original_pair_solvable_noncommuting_model
    (hcores : A.pCoreIn 2 ≠ B.pCoreIn 2) (hs : Group.IsSolvable (A ⊔ B : Subgroup G))
    (hcomm : ¬ ⁅(pResidual 2 A).map A.subtype,(pResidual 2 B).map B.subtype⁆ ≤
      centralizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B) : Set G)) :
    let X := A ⊔ B
    let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
    X ⊓ centralizer (W : Set G) = X.pCoreIn 2 ∧
      Nonempty ((X ⧸ pCore 2 X) ≃* MarkedCubicRecognition.HeisenbergExtension) := by
  exact original_pair_twoThree_noncommuting_model h₀ D m hTA hTB eA eB hne
    hindexA hindexB hcentral hcores hs
    (original_pair_solvable_twoThree_quotient h₀ D m hTA hTB eA eB hne
      hindexA hindexB hcores hs) hcomm
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
