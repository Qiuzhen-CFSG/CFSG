module

public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddTwoPrimary.InvolutionFusion.FixedSpace
public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddTwoPrimary.InvolutionFusion.SingularVector
public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddTwoPrimary.InvolutionFusion.PairReduction
import Mathlib.Algebra.CharP.CharAndCard

/-!
# Involution fusion in the odd-prime split-octonion G₂ model

Every nonidentity involution fixes four octonion dimensions. Chevalley–Warning
provides a nonzero trace-zero norm-zero vector in that fixed space. The explicit
root and partner reductions conjugate the involution into the opposite-pair
stabilizer SL₂, where it is the scalar minus identity. Thus any two involutions
are conjugate by an actual octonion automorphism.

This discharges exactly the fusion premise in
`OddTwoPrimary.universal_not_two_dvd_kernel_of_diagonal_map_and_fusion`.
The independent construction of that theorem's subgroup map is not used here.
Source context: Aschbacher–Smith I.1.1–I.1.4, printed pp.407–408 (PDF pp.418–419),
and GLS III §6.1. No multiplier value, involution classification or centralizer
coverage is assumed. The model and coordinate reductions are from Gerald Höhn
and the ATLAS contributors' licensed port; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

public section

namespace Atlas.G2.MultiplierOrdinary.OddTwoPrimary.InvolutionFusion
open Atlas.SplitOctonion
variable {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]

/-- All involutions of the split-octonion model over the indicated prime field are conjugate. -/
theorem involutions_isConj (hF : Nat.card F = p) (hp : 3 < p)
    (x y : Model F) (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y := by
  let _ := Fintype.ofFinite F
  let _ : CharP F p := charP_of_card_eq_prime (by
    simpa only [← Nat.card_eq_fintype_card] using hF)
  have htwo : (2 : F) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).mp h
    have hle := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  have hn (g : Model F) (hg : orderOf g = 2) : g ≠ 1 := by
    intro h; simp [h] at hg
  have hs (g : Model F) (hg : orderOf g = 2) : g ^ 2 = 1 := by
    simpa only [hg] using pow_orderOf_eq_one g
  have hc (g : Model F) (hg : orderOf g = 2) :
      IsConj g (PairStabilizer.blockHom (-1 : Matrix.SpecialLinearGroup (Fin 2) F)) := by
    obtain ⟨v, hv, ht, hm, hne⟩ := exists_singular_of_finrank_four (p := p)
      (fixedSpace g) (fixedSpace_finrank htwo g (hs g hg) (hn g hg))
    exact isConj_iff.mpr (conjugate_of_fixed_singular htwo g (hs g hg) (hn g hg)
      v ht hm hne hv)
  exact (hc x hx).trans (hc y hy).symm
end Atlas.G2.MultiplierOrdinary.OddTwoPrimary.InvolutionFusion
end
