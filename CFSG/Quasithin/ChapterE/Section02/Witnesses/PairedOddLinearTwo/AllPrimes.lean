module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedOddLinearTwo.Source
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedOddLinearTwo.Small

/-!
# All odd prime fields in the original paired source configuration

Fields of order three are excluded by component perfectness. Order five
uses the actual comparison with SL₂(4), preserving its binary witness
alternative. Every remaining odd prime is seven or greater than nine and
gives the genuine dihedral pair from the original V.

Source: Aschbacher–Smith E.2.7, printed pp.218–219.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Witnesses.PairedOddLinearTwo
variable {H : Type*} [Group H] [Finite H]

inductive OddPrimeAlternative (T : Sylow 2 H) (M V : Subgroup H) (p : ℕ) : Prop
  | dihedral : Nonempty (DihedralWitness T M V) → OddPrimeAlternative T M V p
  | five : p = 5 → PairedBender.LinearAlternative T M V 2 → OddPrimeAlternative T M V p

theorem source_odd_prime_pair
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p)
    (hH : IsStronglyQuasithin H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬Group.IsSolvable H)
    (hJ : ChapterB.minimalParabolicCore T hP = ⊥)
    {K : Subgroup H} (hK : IsComponent H K) (hC : K.IsCComponent)
    [IsSimpleGroup K] (hgen : K ⊔ (T : Subgroup H) = ⊤) (hnot : ¬K.Normal)
    (e : K ≃* PSL(2,F)) (V : Subgroup H) [IsElementaryAbelian 2 V]
    (hVT : V ≤ T) (hVN : (T : Subgroup H) ≤ normalizer (V : Set H))
    (hVM : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2) (hV : V ≠ ⊥) :
    OddPrimeAlternative T (ChapterB.minimalParabolicMax T hP) V p := by
  by_cases hp3 : p = 3
  · exact (component_not_equiv_field_three (hF.trans hp3) hK e).elim
  by_cases hp5 : p = 5
  · exact .five hp5 (source_five_pair (hF.trans hp5) hH T hP hs hJ hK hC hgen hnot e V hVT hVM hV)
  have hp : p = 7 ∨ 9 < p := by
    by_contra! hh
    have hle : p ≤ 9 := hh.2
    have hprime : p.Prime := Fact.out
    interval_cases p <;> norm_num at *
  exact .dihedral (source_pair ho hF hp hH T hP hs hJ hK hC hgen hnot e V hVT hVN hVM hV)

end CFSG.Quasithin.ChapterE.Witnesses.PairedOddLinearTwo
