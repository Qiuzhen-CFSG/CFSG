module

public import CFSG.Quasithin.ChapterA.Section03.RankThreeInvolutions
public import Theory.GroupTheory.SolvableResidual
public import GorensteinWalter.SL2ProjectiveCover

/-!
# The terminal derived subgroup of a rank-three involution centralizer

For q > 3, the actual SL₂(q) is perfect. The prime-to-q residual of an
involution centralizer in SL₃(q) or SU₃(q) is therefore its solvable residual,
not merely a subgroup containing the terminal derived subgroup. This gives
an actual SL₂(ZMod q) isomorphism. The unitary matrices are over GF(q²).

These are calculations in the special matrix groups. Applying them to the
source's projective D and its entire Sylow center still requires central
quotient transport and the position of the source cyclic factors.

Source: Aschbacher–Smith, A.3.21(a), printed p. 55, and the canonical choice
in the proof of 1.3.4, printed pp. 510–511.
-/

public section

open Subgroup
open CFSG.Quasithin.ChapterA.Section03
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan

/-- Perfectness upgrades the linear prime-to-q residual to the solvable residual. -/
theorem sl3_involution_solvableResidual_eq (q : ℕ) [Fact q.Prime]
    (hq : Odd q) (hlarge : 3 < q)
    (z : Matrix.SpecialLinearGroup (Fin 3) (ZMod q)) (hz : orderOf z = 2) :
    solvableResidual (centralizer ({z} : Set (Matrix.SpecialLinearGroup (Fin 3) (ZMod q)))) =
      primeToResidual q (centralizer ({z} : Set (Matrix.SpecialLinearGroup (Fin 3) (ZMod q)))) := by
  let e := sl3_involution_primeToResidual_equiv q hq z hz
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) :=
    GorensteinWalter.sl2_isPerfect_of_card_gt_three (ZMod q) (by
      simpa only [Nat.card_eq_fintype_card, ZMod.card] using hlarge)
  let : Group.IsPerfect (primeToResidual q
      (centralizer ({z} : Set (Matrix.SpecialLinearGroup (Fin 3) (ZMod q))))) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact le_antisymm (sl3_involution_terminalDerived_le_primeToResidual q hq z hz)
    (le_solvableResidual_of_isPerfect _)

/-- Perfectness upgrades the unitary prime-to-q residual to the solvable residual. -/
theorem su3_involution_solvableResidual_eq (q : ℕ) [Fact q.Prime]
    (hq : Odd q) (hlarge : 3 < q) (z : RankThreeSU q) (hz : orderOf z = 2) :
    solvableResidual (centralizer ({z} : Set (RankThreeSU q))) =
      primeToResidual q (centralizer ({z} : Set (RankThreeSU q))) := by
  let e := su3_involution_primeToResidual_equiv q hq z hz
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) :=
    GorensteinWalter.sl2_isPerfect_of_card_gt_three (ZMod q) (by
      simpa only [Nat.card_eq_fintype_card, ZMod.card] using hlarge)
  let : Group.IsPerfect (primeToResidual q
      (centralizer ({z} : Set (RankThreeSU q)))) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact le_antisymm (su3_involution_terminalDerived_le_primeToResidual q hq z hz)
    (le_solvableResidual_of_isPerfect _)

/-- The linear involution centralizer has terminal derived subgroup SL₂(q). -/
noncomputable def sl3_involution_solvableResidual_equiv (q : ℕ) [Fact q.Prime]
    (hq : Odd q) (hlarge : 3 < q)
    (z : Matrix.SpecialLinearGroup (Fin 3) (ZMod q)) (hz : orderOf z = 2) :
    solvableResidual (centralizer ({z} : Set (Matrix.SpecialLinearGroup (Fin 3) (ZMod q)))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod q) :=
  (MulEquiv.subgroupCongr (sl3_involution_solvableResidual_eq q hq hlarge z hz)).trans
    (sl3_involution_primeToResidual_equiv q hq z hz)

/-- The unitary involution centralizer has terminal derived subgroup SL₂(q). -/
noncomputable def su3_involution_solvableResidual_equiv (q : ℕ) [Fact q.Prime]
    (hq : Odd q) (hlarge : 3 < q) (z : RankThreeSU q) (hz : orderOf z = 2) :
    solvableResidual (centralizer ({z} : Set (RankThreeSU q))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod q) :=
  (MulEquiv.subgroupCongr (su3_involution_solvableResidual_eq q hq hlarge z hz)).trans
    (su3_involution_primeToResidual_equiv q hq z hz)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan
