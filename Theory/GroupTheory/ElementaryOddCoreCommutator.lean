module
public import Theory.GroupTheory.OddIndexCoreCentralizes
public import Theory.ElementaryAbelian.Basic
public import Theory.PGroupCore

/-!
# Elementary subgroups with an odd two-core quotient action

Let E normalize an elementary abelian two-subgroup V of a finite group.
If the two-core of E centralizes V, E/O₂(E) has odd order, and the common
fixed subgroup in V is trivial, then V equals the ambient commutator [V,E].
The two-core is its literal image under the subgroup inclusion; there is no
replacement action or quotient module in the statement.

This specializes the existing odd-index core-centralizer splitting theorem.
The subgroup-of-E of the mapped two-core is exactly the native two-core,
so its index is the supplied odd quotient order. Elementary abelianness
supplies the solvable two-group hypotheses; normalization supplies the
reverse commutator inclusion. The imported splitting proof uses an odd
Schur–Zassenhaus complement and the established coprime decomposition.

This general auxiliary theorem was isolated from the ambient splitting
argument in Stellmacher (9.4)(6), Journal of Algebra 190 (1997). The local
formalization also admits a direct core-center argument and does not require
this wrapper.
-/

namespace Subgroup
open scoped IsMulCommutative

public theorem eq_commutator_of_elementary_odd_core_quotient
    {G : Type*} [Group G] [Finite G]
    (V E : Subgroup G) [IsElementaryAbelian 2 V]
    (hEV : E ≤ normalizer (V : Set G))
    (hodd : Odd (Nat.card (E ⧸ pCore 2 E)))
    (hcentral : ⁅V,(pCore 2 E).map E.subtype⁆ = ⊥)
    (hfixed : V ⊓ centralizer (E : Set G) = ⊥) : V = ⁅V,E⁆ := by
  let core := (pCore 2 E).map E.subtype
  have hcore : core ≤ E := map_subtype_le _
  have hnative : core.subgroupOf E = pCore 2 E :=
    comap_map_eq_self_of_injective E.subtype_injective _
  let _ : (core.subgroupOf E).Normal := hnative ▸ inferInstance
  have hindex : Odd (core.subgroupOf E).index := by
    rw [hnative, index_eq_card]
    exact hodd
  have hsolv : Group.IsSolvable V := Group.isSolvable_of_comm fun x y => mul_comm x y
  have hC : core ≤ centralizer (V : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcentral)
  apply le_antisymm ?_ (le_normalizer_iff_commutator_le_left.mp hEV)
  exact le_of_odd_index_core_centralizes E core V ⁅V,E⁆ hcore
    ((pCore_isPGroup (p := 2) (G := E)).map E.subtype) hindex
    (IsElementaryAbelian.isPGroup 2 V) hsolv hEV hC hfixed le_rfl

end Subgroup
