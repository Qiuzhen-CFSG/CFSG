module

public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.ConjugateSpanOrder
public import Mathlib.GroupTheory.PGroup

/-!
# Intersection bounds and local prime-core transfer

A subspace larger than every distinct-conjugate intersection has its
normalizer in that of the full module. Intersecting a local prime-core
with a smaller group gives a normal prime-subgroup of that smaller group.
If that smaller group is itself relatively normal in another local group,
its core, and every conjugate of a seed in it, lie in the latter core.

These are the ambient-subgroup steps in Aschbacher–Smith, combined
manuscript (1 March 2004), Lemma 12.6.24(3–5), printed pp.830–831.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G]

/-- A subgroup too large for a distinct-conjugate intersection controls
its own normalizer. No centralizer is substituted for this normalizer. -/
theorem normalizer_le_of_conjugate_intersection_card_bound [Finite G]
    {V W : Subgroup G} {b : ℕ} (hWV : W ≤ V) (hW : b < Nat.card W)
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ b) :
    normalizer (W : Set G) ≤ normalizer (V : Set G) := by
  intro g hg
  by_contra hn
  have hwg : W.map (MulAut.conj g).toMonoidHom = W :=
    mem_normalizer_iff_map_conj_eq.mp hg
  have hi : W ≤ V ⊓ V.map (MulAut.conj g).toMonoidHom :=
    le_inf hWV (hwg ▸ map_mono hWV)
  exact (not_lt_of_ge ((Nat.card_le_card_of_injective (inclusion hi) (inclusion_injective hi)).trans (hbound g hn))) hW

/-- Pull the core of a larger group into a subgroup, then push it into
a group in which that subgroup is relatively normal. -/
theorem inf_pCoreIn_le_of_normalizes {p : ℕ} {A B C : Subgroup G}
    (hBA : B ≤ A) (hBC : B ≤ C) (hCB : C ≤ normalizer (B : Set G)) :
    A.pCoreIn p ⊓ B ≤ C.pCoreIn p := by
  have hAn : A ≤ normalizer (A.pCoreIn p : Set G) :=
    A.le_normalizer.trans (normalizer_le_normalizer_characteristic_image A (pCore p A))
  have hBn : B ≤ normalizer (A.pCoreIn p ⊓ B : Set G) :=
    (le_inf (hBA.trans hAn) B.le_normalizer).trans inf_normalizer_le_normalizer_inf
  exact (le_pCoreIn_of_normalizes ((isPGroup_pCoreIn p A).to_le inf_le_left)
    inf_le_right hBn).trans (pCoreIn_mono_of_normalizes hBC hCB)

/-- The version used when the intermediate group is the full centralizer
of a source subspace. -/
theorem conjugateSpanBy_le_pCoreIn_of_centralizer_le {p : ℕ}
    {V W A U J : Subgroup G} (hspan : V = conjugateSpanBy W J)
    (hWA : W ≤ A.pCoreIn p) (hWU : W ≤ centralizer (U : Set G))
    (hUA : centralizer (U : Set G) ≤ A)
    (hJ : J ≤ normalizer (U : Set G)) :
    V ≤ (normalizer (U : Set G)).pCoreIn p := by
  have hw : W ≤ (normalizer (U : Set G)).pCoreIn p :=
    (le_inf hWA hWU).trans (inf_pCoreIn_le_of_normalizes hUA
      (centralizer_le_normalizer _)
      ((normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer _)).mp inferInstance))
  rw [hspan]
  exact conjugateSpanBy_le hw (hJ.trans
    ((normalizer (U : Set G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore p _))))

/-- A p-subgroup and a p-subgroup of the local core generate a p-group.
The normality used here is inside J. -/
theorem isPGroup_sup_of_le_pCoreIn {p : ℕ} {V A J : Subgroup G}
    (hV : V ≤ J.pCoreIn p) (hA : A ≤ J) (hp : IsPGroup p A) :
    IsPGroup p (V ⊔ A : Subgroup G) := by
  have hn : A ≤ normalizer (J.pCoreIn p : Set G) := hA.trans
    (J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore p J)))
  exact ((isPGroup_pCoreIn p J).to_sup_of_normal_left' hp hn).to_le
    (sup_le_sup hV le_rfl)

end Subgroup
