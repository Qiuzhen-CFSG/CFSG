module

public import CFSG.Quasithin.Chapter12.Section09.Hyperplanes

/-!
# The terminal commutator deduction in Section 12.9

The plane span U_H lies in the abelian point span. A conjugate A of V
inside H normalizes U_H. If U_H also normalizes A, their commutator lies
in U_H ∩ A, hence in C_A(V) ∩ M. The hyperplane conclusion of 12.9.9(2)
then kills that commutator, contradicting movement of the original plane.
The second theorem applies the Sylow placement result to obtain precisely
that hyperplane conclusion with the literal original subgroups.

The existence of H and its moving conjugate, and the preceding local and
fusion assertions, remain source obligations; this is not a proof of 12.9.1.
Source: Aschbacher--Smith, proof of 12.9.1, printed pp.863--864.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09
open Section02 Section08 Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The last commutator contradiction on printed p.864, with the literal
plane span and a conjugate of the original chosen seed. -/
theorem terminal_contradiction
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (habelian : IsMulCommutative F.U)
    (H : Subgroup G) (hH : H ≤ F.H) (g : G)
    (hA : conjugate V g ≤ H)
    (hnorm : conjugateSpanBy (F.Vi 2) H ≤ normalizer (conjugate V g : Set G))
    (hmove : ¬ conjugate V g ≤ normalizer (F.Vi 2 : Set G))
    (hfix : (conjugate V g ⊓ normalizer (L : Set G)) ⊓
      centralizer (V : Set G) = ⊥) : False := by
  let U := conjugateSpanBy (F.Vi 2) H
  let A := conjugate V g
  have hUU : U ≤ F.U := conjugateSpanBy_mono (F.le_seed 2) hH
  let :=  habelian
  have hUV : U ≤ centralizer (V : Set G) :=
    (hUU.trans (le_centralizer F.U)).trans
      (centralizer_le (le_conjugateSpanBy V F.H))
  have hcU : ⁅U, A⁆ ≤ U := le_normalizer_iff_commutator_le_left.mp
    (hA.trans (le_normalizer_conjugateSpanBy (F.Vi 2) H))
  have hcA : ⁅U, A⁆ ≤ A := le_normalizer_iff_commutator_le_right.mp hnorm
  have hc : ⁅U, A⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [← hfix]
    exact le_inf (le_inf hcA
      ((hcU.trans hUV).trans (h.seed_centralizer_le earlier.structural earlier.uniqueness)))
      (hcU.trans hUV)
  apply hmove
  exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)).trans
    ((centralizer_le (le_conjugateSpanBy (F.Vi 2) H)).trans (Subgroup.centralizer_le_normalizer _))

/-- The terminal source application uses 12.9.9(2) in its original
Sylow form, without supposing that the final H-conjugator normalizes T. -/
theorem terminal_contradiction_of_sylow_hyperplanes
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (habelian : IsMulCommutative F.U)
    (hyperplanes : SylowHyperplaneControl T L V)
    (H : Subgroup G) (hH : H ≤ F.H) (g : G)
    (hA : conjugate V g ≤ H)
    (hnorm : conjugateSpanBy (F.Vi 2) H ≤ normalizer (conjugate V g : Set G))
    (hmove : ¬ conjugate V g ≤ normalizer (F.Vi 2 : Set G))
    (hDN : conjugate V g ⊓ normalizer (L : Set G) ≤ normalizer (V : Set G))
    (hindex : (conjugate V g ⊓ normalizer (L : Set G)).relIndex (conjugate V g) = 2) :
    False :=
  terminal_contradiction h earlier F habelian H hH g hA hnorm hmove
    (hyperplane_control_of_normalizes h earlier hyperplanes g hDN hindex)

end CFSG.Quasithin.Chapter12.Section09
