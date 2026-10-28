module

public import Theory.GroupTheory.QuasithinBasic
public import Theory.Quasithin.EvenCharacteristic

/-!
# Local bounds from a family of conjugate overgroups

If every two-local lies in a conjugate of a member of a given family,
prime-rank bounds on that family bound every two-local. If the family
members are themselves two-local, maximal two-locals equal such conjugates.
Consequently self-centralization of the two-core transfers to all maximal
two-locals. Normality and cores in this criterion are intrinsic to each
local subgroup.

This is the group-theoretic assembly step in the parabolic route to the
local conditions of Aschbacher–Smith, Theorem 0.1.2, printed pp.4 and 482.
The geometric coverage and the properties of the family are explicit inputs.
-/

namespace Theory.GroupTheory
open Subgroup

variable {G ι : Type*} [Group G] (P : ι → Subgroup G)

/-- Rank monotonicity and conjugacy transfer bounds from a covering family. -/
public theorem primeRank_le_of_twoLocal_conjugate_cover [Finite G] (p b : ℕ)
    (hbound : ∀ i, primeRank p (P i) ≤ b)
    (hcover : ∀ M : Subgroup G, IsTwoLocal M →
      ∃ i g, M ≤ (P i).map (MulAut.conj g).toMonoidHom)
    (M : Subgroup G) (hM : IsTwoLocal M) : primeRank p M ≤ b := by
  obtain ⟨i, g, hle⟩ := hcover M hM
  have hr := primeRank_le_of_injective p (inclusion hle) (inclusion_injective hle)
  rw [← primeRank_equiv p (equivMapOfInjective (P i)
    (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)] at hr
  exact hr.trans (hbound i)

/-- Maximality among two-locals turns a covering inclusion into equality. -/
public theorem maximalTwoLocal_eq_of_conjugate_cover
    (hlocal : ∀ i, IsTwoLocal (P i))
    (hcover : ∀ M : Subgroup G, IsTwoLocal M →
      ∃ i g, M ≤ (P i).map (MulAut.conj g).toMonoidHom)
    (M : Subgroup G) (hM : IsMaximalTwoLocal M) :
    ∃ i g, M = (P i).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨i, g, hle⟩ := hcover M hM.1
  exact ⟨i, g, le_antisymm hle (hM.2 (isTwoLocal_map (MulAut.conj g) (hlocal i)) hle)⟩

/-- Self-centralization of the family cores gives characteristic two in
every maximal two-local, with no ambient normality assumption. -/
public theorem centralizer_pCore_le_of_twoLocal_conjugate_cover
    (hlocal : ∀ i, IsTwoLocal (P i))
    (hcore : ∀ i, centralizer (pCore 2 (P i) : Set (P i)) ≤ pCore 2 (P i))
    (hcover : ∀ M : Subgroup G, IsTwoLocal M →
      ∃ i g, M ≤ (P i).map (MulAut.conj g).toMonoidHom)
    (M : Subgroup G) (hM : IsMaximalTwoLocal M) :
    centralizer (pCore 2 M : Set M) ≤ pCore 2 M := by
  obtain ⟨i, g, rfl⟩ := maximalTwoLocal_eq_of_conjugate_cover P hlocal hcover M hM
  exact (Theory.Quasithin.centralizer_pCore_map_le_iff 2 (MulAut.conj g) (P i)).mpr
    (hcore i)

end Theory.GroupTheory
