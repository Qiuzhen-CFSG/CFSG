module

public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.PairSylow
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFormTransport
public import Mathlib.GroupTheory.Frattini

/-!
# Inner action on the smallest binary unitary-four row

For the PSU₄(2) source row, transport an arbitrary source Sylow subgroup to
the explicit standard SU₄ Sylow.  Its cardinality is 64, so the Frattini
quotient has cardinality at most 64 and the pair Sylow restriction applies.
The higher binary unitary rows and PSU₅(4) require a separate full-Sylow
Frattini or outer-action calculation.
-/

public section
open Subgroup
open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04

private theorem binary_unitary_four_one_frattini_card
    {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 4 F) (hconj : ∀ x, J.conj x = x ^ (2 ^ 1))
    (hcard : Nat.card F = (2 ^ 1) ^ 2)
    [Finite (ProjectiveSpecialUnitaryMatrixGroup J)]
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    Nat.card (P ⧸ frattini P) ≤ 128 := by
  letI : CharP F 2 :=
    UnitaryFourFormTransport.charP_two 1 (by decide) hcard
  obtain ⟨j0⟩ := UnitaryFourFormTransport.nonempty_projectiveEquiv_standardSU
    J 1 (by decide) hcard hconj
  let t := j0
  letI : Finite ((UnitaryFourFormTransport.standardForm J).specialSubgroup) :=
    Finite.of_injective (fun x => t.symm x) (fun _ _ h => t.symm.injective h)
  let Q : Sylow 2 ((UnitaryFourFormTransport.standardForm J).specialSubgroup) :=
    Sylow.mapSurjective (p := 2) (G := ProjectiveSpecialUnitaryMatrixGroup J)
      (G' := (UnitaryFourFormTransport.standardForm J).specialSubgroup)
      (f := t.toMonoidHom) t.surjective P
  let Q0 := UnitaryFourSylow.sylow F J.conj J.conj_involutive
  have hPQ : Nat.card P = Nat.card Q := by
    exact Nat.card_congr
      (P.equivMapOfInjective t.toMonoidHom t.injective).toEquiv
  have hQQ0 : Nat.card Q = Nat.card Q0 := by
    exact Nat.card_congr (Sylow.equiv Q Q0).toEquiv
  have hQ0 : Nat.card Q0 = 64 := by
    rw [show Q0 = UnitaryFourSylow.sylow F J.conj J.conj_involutive from rfl]
    rw [UnitaryFourSylow.coe_sylow F J.conj J.conj_involutive]
    rw [UnitaryFourSylow.upper_card]
    norm_num [UnitaryFourSylow.FixedField]
    rw [hcard, UnitaryFourFormTransport.fixed_card J 1 (by decide) hcard hconj]
    norm_num
  have hPcard : Nat.card P ≤ 64 := by omega
  calc
    Nat.card (P ⧸ frattini P) ≤ Nat.card P :=
      Nat.le_of_dvd Nat.card_pos (card_quotient_dvd_card (frattini P))
    _ ≤ 64 := hPcard
    _ ≤ 128 := by decide

include D in
/-- The original residual acts innerly on a normal PSU₄(2) component. -/
theorem source_a5_oddNormalizer_inner_of_binary_unitary_four_one
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G))) [K.Normal] [IsQuasisimple K]
    (hm : ClassicalGroup.IsPSU (K ⧸ center K) 4 2) :
    ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf (normalizer (B : Set G)) ≤
      K ⊔ centralizer (K : Set (normalizer (B : Set G))) := by
  let P : Sylow 2 (K ⧸ center K) := Classical.choice inferInstance
  apply source_a5_oddNormalizer_inner_of_smallFrattini D e hn hp B hB hBC hperm K P
  obtain ⟨F, hF, hFfin, J, hcard, hconj, ⟨j⟩⟩ := hm
  letI : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective (fun x => j.symm x) (fun _ _ h => j.symm.injective h)
  let P' : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J) :=
    P.mapSurjective (f := j.toMonoidHom) j.surjective
  exact binary_unitary_four_one_frattini_card J (by simpa using hconj)
    (by simpa using hcard) P'

end CFSG.Quasithin.Chapter10
