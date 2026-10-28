module

public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.EightPointLine.Contracts
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.EightPointLine.Coverage.Adjacent

/-!
# Exhaustive coverage of order-nine subgroups in A₈

The three-part of the order of A₈ is nine. Sylow conjugacy therefore makes
any subgroup of order nine a conjugate of `nineGroup 0`. The candidate family
is closed under every adjacent transposition, by the checked generator
identities in `Coverage.Adjacent`. These transpositions generate S₈, so the
family contains the required conjugate. The final conjugator comes from A₈;
using S₈ to enumerate supports does not enlarge the line stabilizer.

Source application: Aschbacher–Smith, proof of 1.3.4, printed p.511 (PDF p.528);
GLS3, Table 5.3e, the octad stabilizer `E₁₆.A₈`.
-/

open Subgroup
namespace Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement.EightPoint

private theorem conjugate_nineGroup_all (g : Sym) (i : Fin 280) :
    ∃ j : Fin 280, (nineGroup i).map (MulAut.conjNormal g).toMonoidHom = nineGroup j := by
  let M : Submonoid Sym :=
    { carrier := {g | ∀ i : Fin 280, ∃ j : Fin 280,
        (nineGroup i).map (MulAut.conjNormal g).toMonoidHom = nineGroup j}
      one_mem' := by
        intro i
        refine ⟨i, ?_⟩
        rw [map_one]
        exact Subgroup.map_id _
      mul_mem' := by
        intro g h hg hh i
        obtain ⟨j, hj⟩ := hh i
        obtain ⟨k, hk⟩ := hg j
        refine ⟨k, ?_⟩
        have hcomp : (MulAut.conjNormal (g * h) : MulAut Alt).toMonoidHom =
            (MulAut.conjNormal g : MulAut Alt).toMonoidHom.comp
              (MulAut.conjNormal h).toMonoidHom := by
          rw [map_mul]
          rfl
        rw [hcomp, ← Subgroup.map_map, hj, hk] }
  have hM : (⊤ : Submonoid Sym) ≤ M := by
    rw [← Equiv.Perm.mclosure_swap_castSucc_succ 7, Submonoid.closure_le]
    rintro _ ⟨r, rfl⟩
    exact Coverage.conjugate_nineGroup_adjacent r
  exact hM (Submonoid.mem_top g) i

private theorem three_multiplicity : 3 ^ (Nat.card Alt).factorization 3 = 9 := by
  rw [card_alt, show 20160 = 3 ^ 2 * 2240 by decide,
    Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow]
  norm_num [(by decide : Nat.Prime 3).factorization,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 2240)]

/-- Every order-nine subgroup of the literal A₈ is one of the 280 candidates. -/
public theorem nineCoverage : NineCoverage := by
  intro D hcard
  let Q : Sylow 3 Alt := Sylow.ofCard (nineGroup 0)
    ((card_nineGroup 0).trans three_multiplicity.symm)
  let R : Sylow 3 Alt := Sylow.ofCard D (hcard.trans three_multiplicity.symm)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Alt Q R
  have hD : (nineGroup 0).map (MulAut.conj g).toMonoidHom = D :=
    congrArg Sylow.toSubgroup hg
  obtain ⟨j, hj⟩ := conjugate_nineGroup_all g.val 0
  rw [MulAut.conjNormal_val, hD] at hj
  exact ⟨j, hj⟩

end Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement.EightPoint
