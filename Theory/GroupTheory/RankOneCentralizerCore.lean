module

public import Theory.GroupTheory.PGroup.CentralProductCore
public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.SolvableRankOneStructure
public import Theory.GroupTheory.QuaternionCentralizerCoreTransfer

/-!
# Core-free binary centralizer transport

Let a finite solvable group be the product of a two-subgroup and its
centralizer. If the centralizer has trivial odd core and no elementary four,
then an elementary subgroup of order at least eight can be transferred into
the ambient two-core.

The rank-one structure theorem makes the centralizer a two-group or gives
it a quaternion-eight two-core. In the first case the whole product is its
own two-core. In the second case quaternion-core transfer places an
elementary subgroup of the required order in the product with the
centralizer's two-core. Both factors of this latter product are normal
two-subgroups, so it lies in the ambient two-core.

This assembles the core-free residue for the binary remark following GLS,
Number 2, Proposition 22.4 (`refs/KGroup/GLS2/ChapterF.tex`). The elementary
four and rank-two hypotheses on the first factor are unnecessary for this
residue. The recognition module retains its original interface as a wrapper.
-/

namespace Subgroup

/-- The two-group-centralizer case of binary centralizer transport. -/
public theorem exists_elementary_eight_le_pCore_of_isPGroup_centralizer
    {H : Type*} [Group H] [Finite H] (Q B : Subgroup H)
    (hQ : IsPGroup 2 Q)
    (hC : IsPGroup 2 (Subgroup.centralizer (Q : Set H)))
    (hgen : Q ⊔ Subgroup.centralizer (Q : Set H) = ⊤)
    (hB : IsElementaryAbelian 2 B) (hcard : 8 ≤ Nat.card B) :
    ∃ D : Subgroup H, D ≤ pCore 2 H ∧ IsElementaryAbelian 2 D ∧ 8 ≤ Nat.card D := by
  have hcore := Subgroup.pCore_eq_top_of_centralizing_sup_eq_top 2 Q
    (Subgroup.centralizer (Q : Set H)) hQ hC hgen le_rfl
  exact ⟨B, hcore.symm ▸ le_top, hB, hcard⟩

/-- An elementary subgroup of order at least eight transfers into the two-core
when a solvable centralizer product has rank-one centralizer and trivial odd core. -/
public theorem exists_elementary_eight_le_pCore_of_rank_one_centralizer
    {H : Type*} [Group H] [Finite H] [Group.IsSolvable H]
    (Q B : Subgroup H) (hQ : IsPGroup 2 Q)
    (hgen : Q ⊔ Subgroup.centralizer (Q : Set H) = ⊤)
    (hodd : pPrimeCore 2 (Subgroup.centralizer (Q : Set H)) = ⊥)
    (hCrank : ∀ F : Subgroup (Subgroup.centralizer (Q : Set H)),
      IsElementaryAbelian 2 F → Nat.card F < 4)
    (hB : IsElementaryAbelian 2 B) (hcard : 8 ≤ Nat.card B) :
    ∃ D : Subgroup H, D ≤ pCore 2 H ∧ IsElementaryAbelian 2 D ∧ 8 ≤ Nat.card D := by
  rcases Group.isPGroup_or_pCore_quaternion_of_rank_one
    inferInstance hodd hCrank with hC | hcore
  · exact exists_elementary_eight_le_pCore_of_isPGroup_centralizer
      Q B hQ hC hgen hB hcard
  · let := hB
    obtain ⟨D, hD, he, hc⟩ :=
      exists_elementary_eight_quaternion_core Q B hQ hgen hCrank hcore hcard
    exact ⟨D, hD.trans (Subgroup.sup_map_pCore_le_of_centralizing_sup_eq_top
      2 Q (Subgroup.centralizer (Q : Set H)) hQ hgen le_rfl), he, hc⟩

end Subgroup
