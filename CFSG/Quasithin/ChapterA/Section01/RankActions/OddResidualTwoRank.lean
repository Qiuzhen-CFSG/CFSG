module
public import CFSG.Quasithin.ChapterA.Section01.RankActions.AutomorphismQuotient
public import Theory.SpecificGroups.GL2.OddCharacteristicTwoRank
public import Theory.GroupTheory.GeneralizedFitting.ResidualCentralizer
public import Theory.Quasithin.CoprimeRank
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Two-rank controlled by a small odd-prime residual

When O₂(H) is trivial and O²(H) is an odd prime core of prime rank at most
two, the residual is self-centralizing. Its conjugation action, followed by
A.1.25's actual two-dimensional automorphism representation, has odd-order
kernel. Thus the binary rank is bounded by that of GL₂ in odd characteristic.
No bound on the rank of an arbitrary quotient is used.

Source: Aschbacher--Smith, A.1.25(2), p.25, and the solvable rank argument
in 12.2.18, p.801. The H-star consumer supplies the odd residual via B.6.8.
-/

public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.ChapterA.RankActions

variable {H : Type*} [Group H] [Finite H]

theorem odd_residual_twoRank_le_two {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (hcore : pCore 2 H = ⊥)
    (hR : pResidual 2 H = pCore p H) (hr : primeRank p (pCore p H) ≤ 2) :
    primeRank 2 H ≤ 2 := by
  let P := pCore p H
  let a : H →* MulAut P := MulAut.conjNormal
  have ha : IsPGroup p a.ker := by
    have hc : centralizer (P : Set H) ≤ P := by
      change centralizer (pCore p H : Set H) ≤ pCore p H
      rw [← hR]
      exact centralizer_pResidual_le_of_pCore_eq_bot hcore
    rw [show a.ker = centralizer (P : Set H) from MulAut.conjNormal_ker_eq_centralizer P]
    exact (pCore_isPGroup (p := p) (G := H)).to_le hc
  obtain ⟨f, hf⟩ := smallRankAutomorphismRepresentation p hp P pCore_isPGroup hr
  have hk : IsPGroup p (f.comp a).ker := by
    rw [← MonoidHom.comap_ker]
    exact hf.comap_of_ker_isPGroup a ha
  have hc : Nat.Coprime 2 (Nat.card (f.comp a).ker) := by
    obtain ⟨n, hn⟩ := hk.exists_card_eq
    rw [hn]
    exact (Nat.coprime_two_left.mpr hp).pow_right n
  apply (primeRank_le_of_coprime_ker 2 (f.comp a) hc).trans
  apply Matrix.GeneralLinearGroup.twoRank_le_two_of_two_ne_zero
  intro hz
  have hd := (ZMod.natCast_eq_zero_iff 2 p).mp hz
  have he := ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left
    (Fact.out : p.Prime).ne_one
  subst p
  exact (by decide : ¬ Odd 2) hp

end CFSG.Quasithin.ChapterA.RankActions

