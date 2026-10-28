module

public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# Elementary abelian joins of commuting families

The join of a pairwise commuting family of elementary abelian p-subgroups
is elementary abelian. Its generators commute, and induction on the subgroup
closure preserves exponent dividing p.

Source application: Aschbacher--Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), F.7.11(4), printed p.313: the neighboring
conjugates commute when the track exceeds two.
-/

open Subgroup
open scoped IsMulCommutative

namespace IsElementaryAbelian

/-- A pairwise commuting family of elementary abelian subgroups generates an
elementary abelian subgroup, with no finiteness assumption on the family. -/
public theorem iSup_of_le_centralizer {p : ℕ} {G : Type*} [Group G] {ι : Type*}
    (E : ι → Subgroup G) [∀ i, IsElementaryAbelian p (E i)]
    (hcomm : ∀ i j, E i ≤ centralizer (E j : Set G)) :
    IsElementaryAbelian p (⨆ i, E i : Subgroup G) := by
  rw [iSup_eq_closure]
  let : IsMulCommutative (closure (⋃ i, (E i : Set G))) :=
    isMulCommutative_closure (by
      intro x hx y hy
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      obtain ⟨j, hyj⟩ := Set.mem_iUnion.mp hy
      exact (mem_centralizer_iff.mp (hcomm j i hyj)) x hxi)
  apply IsElementaryAbelian.closure_of_isMulCommutative
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  exact elemPow_eq_one_of_isElementaryAbelian x hxi

end IsElementaryAbelian
