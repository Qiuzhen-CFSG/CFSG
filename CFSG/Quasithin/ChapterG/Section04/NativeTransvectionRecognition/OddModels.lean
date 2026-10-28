module

public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.TwoGroupExclusion
public import Theory.SpecificGroups.SU3.OddInvolutionTwoGroupExclusion
public import Theory.SpecificGroups.SymplecticFour.SmallOddLinear
public import CFSG.Quasithin.ChapterA.Section02.Statements.Models

/-!
# The odd-characteristic rows in the native G.4.1 inspection

For the literal nonsolvable subgroup of Sp₄(F), one involution with a
two-group centralizer excludes both degree-three odd families in Theorem C.
The faithful symplectic representation bounds the remaining odd PSL₂ field,
leaving the actual A₅ or A₆ carrier. All model and centralizer transports
use the supplied multiplicative equivalence; there is no hypothesis about
other involutions or about a chosen Sylow subgroup.

This is a source-row reduction, not the later identification of the actual
four-dimensional module. In particular A₆ is retained as the binary derived
endpoint Sp₄(2)′, without declaring Sp₄(2) simple.
Source: Aschbacher--Smith G.4.1, final paragraph, printed p.342.
-/

@[expose] public noncomputable section
set_option linter.style.haveILetI false
open Matrix Subgroup BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section04.NativeTransvectionRecognition
open ChapterA.Section02 Theory.SpecificGroups.SymplecticFour
variable {H F : Type*} [Group H] [Field F] [CharP F 2]

theorem theoremCOdd_alternating_five_or_six
    (hns : ¬ Group.IsSolvable H) (hm : IsTheoremCOddModel H)
    (t : H) (ht : orderOf t = 2) (hc : IsPGroup 2 (centralizer ({t} : Set H)))
    (j : H →* Sp F) (hj : Function.Injective j) :
    Nonempty (H ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (H ≃* alternatingGroup (Fin 6)) := by
  cases hm with
  | linear_two p d hp ho _ iso =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := iso
    have hnsK : ¬ Group.IsSolvable PSL(2,K) := by
      intro hs
      letI := hs
      exact hns (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
    rcases odd_psl2_equiv_alternating_five_or_six
        (by rw [hK]; exact ho.pow) hnsK (j.comp e.symm.toMonoidHom)
        (hj.comp e.symm.injective) with hf | hf
    · exact .inl (hf.map fun f => e.trans f)
    · exact .inr (hf.map fun f => e.trans f)
  | linear_three p hp ho iso =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := iso
    have hoK : Odd (Nat.card K) := by rw [hK]; exact ho
    exact False.elim (Matrix.PSL3.OddInvolutionFixed.involution_centralizer_not_twoGroup
      hoK (GorensteinWalter.two_ne_zero_of_odd_card K hoK) (e t)
      ((e.orderOf_eq t).trans ht) (hc.of_equiv (Matrix.SU3.InnerThreeRank.centralizerEquiv e t)))
  | unitary_three p hp ho iso =>
    obtain ⟨K, _, _, J, hK, hconj, ⟨e⟩⟩ := iso
    letI : Fact p.Prime := ⟨hp⟩
    exact False.elim (Matrix.SU3.OddPrimeComponent.involution_centralizer_not_twoGroup
      p ho K J hK hconj (e t) ((e.orderOf_eq t).trans ht)
      (hc.of_equiv (Matrix.SU3.InnerThreeRank.centralizerEquiv e t)))
end CFSG.Quasithin.ChapterG.Section04.NativeTransvectionRecognition
