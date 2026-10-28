module

public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# Images and relative containment of embedded prime cores

Restrict a homomorphism with p-group kernel to a subgroup and its actual
image. The restricted kernel is still a p-group, so the p-core lifting
lemma identifies the image of the local core. We also record core
containment for a relatively normal subgroup, without ambient normality.

Source application: Aschbacher–Smith, *The Classification of Quasithin
Groups*, final proof of Theorem 15.3.1, printed p.1155 (PDF p.1172).
-/

public section
namespace Subgroup
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

/-- The embedded prime core commutes with any map whose kernel is a prime group. -/
theorem map_pCoreIn_of_ker_isPGroup {p : ℕ} [Fact p.Prime]
    (f : G →* H) (hker : IsPGroup p f.ker) (Y : Subgroup G) :
    (Y.pCoreIn p).map f = (Y.map f).pCoreIn p := by
  have hk : IsPGroup p (f.subgroupMap Y).ker := by
    rw [Subgroup.ker_subgroupMap]
    exact hker.comap_subtype
  have he := (f.subgroupMap Y).comap_pCore_of_ker_isPGroup
    (f.subgroupMap_surjective Y) hk
  have hm : (pCore p Y).map (f.subgroupMap Y) = pCore p (Y.map f) := by
    rw [← he, map_comap_eq_self]
    rw [MonoidHom.range_eq_top_of_surjective _ (f.subgroupMap_surjective Y)]
    exact le_top
  calc
    _ = ((pCore p Y).map (f.subgroupMap Y)).map (Y.map f).subtype := by
      rw [pCoreIn, map_map, map_map]
      rfl
    _ = _ := by rw [hm]; rfl

omit [Finite G] [Finite H] in
/-- Relative normality makes embedded prime cores monotone. -/
theorem pCoreIn_mono_of_normalizes {p : ℕ} {Y L : Subgroup G}
    (hYL : Y ≤ L) (hn : L ≤ normalizer (Y : Set G)) :
    Y.pCoreIn p ≤ L.pCoreIn p :=
  le_pCoreIn_of_normalizes (isPGroup_pCoreIn p Y) ((pCoreIn_le p Y).trans hYL)
    (hn.trans (normalizer_le_normalizer_characteristic_image Y (pCore p Y)))

end Subgroup
