module

public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Core centralizers in relative normalizers

The centralizer of a subgroup in O_p(M) is a normal p-subgroup of its
normalizer in M. Consequently it lies in every Sylow p-subgroup of that
relative normalizer. This is the relative-normality step used in
Aschbacher–Smith, Lemmas 2.3.8(5–6) and 2.3.9(2), printed pp.524–525.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] {p : ℕ}

theorem pCoreIn_inf_centralizer_le_normalizer_core (M Q : Subgroup G) :
    M.pCoreIn p ⊓ centralizer (Q : Set G) ≤
      (M ⊓ normalizer (Q : Set G)).pCoreIn p := by
  have hM : M ≤ normalizer (M.pCoreIn p : Set G) := by
    simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using (pCore p M).le_normalizer_map M.subtype
  have hQ : normalizer (Q : Set G) ≤ normalizer (centralizer (Q : Set G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer _)).mp inferInstance
  exact le_pCoreIn_of_normalizes ((isPGroup_pCoreIn p M).to_le inf_le_left)
    (inf_le_inf (pCoreIn_le p M) (centralizer_le_normalizer _))
    ((inf_le_inf hM hQ).trans inf_normalizer_le_normalizer_inf)

theorem pCoreIn_inf_centralizer_le_sylow (M Q : Subgroup G)
    (P : Sylow p ↥(M ⊓ normalizer (Q : Set G))) :
    M.pCoreIn p ⊓ centralizer (Q : Set G) ≤
      (P : Subgroup ↥(M ⊓ normalizer (Q : Set G))).map
        (M ⊓ normalizer (Q : Set G)).subtype :=
  (pCoreIn_inf_centralizer_le_normalizer_core M Q).trans (pCoreIn_le_sylow _ P)

end Subgroup
