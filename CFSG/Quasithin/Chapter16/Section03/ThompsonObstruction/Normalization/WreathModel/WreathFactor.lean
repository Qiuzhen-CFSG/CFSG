module
public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.Normalization.WreathModel.SylowIntersection
public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.TreeWreathModel

/-!
# The actual wreath factor in the marked S₈

The subgroup Q = (P ∩ K)⟨z⟩ lies in the marked S₈ extension and has order 128.
Transporting Q along the given marking therefore gives a Sylow two-subgroup
of S₈. Sylow conjugacy identifies it with the actual binary-tree subgroup,
whose dihedral wreath-product equivalence supplies the required model of Q.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, completion of
the proof of Theorem 16.3.7, printed p.1182 / PDF p.1199.
-/

public section
open Subgroup Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
namespace CFSG.Quasithin.Chapter16.ThompsonObstruction
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z t : G} {L : Subgroup G}

/-- The actual marked Sylow factor is D₈ wreath C₂. -/
noncomputable def Selected.wreathFactorEquiv (s : Selected T z t L) :
    ((localSylow s.P ⊓ enlargement t L) ⊔ zpowers z : Subgroup G) ≃*
      RegularWreathProduct (DihedralGroup 4) (Multiplicative (ZMod 2)) := by
  let Q := (localSylow s.P ⊓ enlargement t L) ⊔ zpowers z
  let E := enlargement t L ⊔ zpowers z
  let U := (Q.subgroupOf E).map s.marked.equiv.toMonoidHom
  let e : Q ≃* U := (subgroupOfEquivOfLe s.wreath_factor_le_extension).symm.trans
    (s.marked.equiv.subgroupMap _)
  have hcU : Nat.card U = 128 :=
    (Nat.card_congr e.toEquiv).symm.trans s.wreath_factor_card
  have hcard : Nat.card U = 2 ^ (Nat.card (Equiv.Perm (Fin 8))).factorization 2 := by
    rw [hcU, card_s8, show 40320 = 2 ^ 7 * 315 by rfl,
      Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow]
    norm_num [Nat.prime_two.factorization,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 315)]
  let US := Sylow.ofCard U hcard
  exact e.trans ((US.equiv treeSylow).trans treeWreathEquiv)

end CFSG.Quasithin.Chapter16.ThompsonObstruction
