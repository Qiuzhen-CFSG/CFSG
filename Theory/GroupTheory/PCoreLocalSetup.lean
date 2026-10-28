module

public import Theory.PGroupCore
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Prime cores in a common ambient group

The image of `O_p(H)` in an ambient group contains every normal `p`-subgroup
of `H`, and is contained in every Sylow `p`-subgroup of `H`. These two facts
give the centralizer bound used in Aschbacher–Smith, *The Classification of
Quasithin Groups*, Lemma 1.1.6 (combined manuscript, 1 March 2004).
-/

@[expose] public section

namespace Subgroup

variable {G : Type*} [Group G]

/-- The core `O_p(H)`, viewed as a subgroup of the ambient group. -/
def pCoreIn (p : ℕ) (H : Subgroup G) : Subgroup G :=
  (pCore p H).map H.subtype

theorem pCoreIn_le (p : ℕ) (H : Subgroup G) : H.pCoreIn p ≤ H :=
  map_subtype_le _

theorem isPGroup_pCoreIn (p : ℕ) (H : Subgroup G) : IsPGroup p (H.pCoreIn p) :=
  pCore_isPGroup.map H.subtype

theorem le_pCoreIn_of_normalizes {p : ℕ} {B H : Subgroup G}
    (hB : IsPGroup p B) (hBH : B ≤ H) (hH : H ≤ normalizer (B : Set G)) :
    B ≤ H.pCoreIn p := by
  have hn : (B.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hBH).mpr hH
  have hp : IsPGroup p (B.subgroupOf H) :=
    hB.of_equiv (subgroupOfEquivOfLe hBH).symm
  have hc : B.subgroupOf H ≤ pCore p H := le_sSup ⟨hn, hp⟩
  have hm := map_mono (f := H.subtype) hc
  rwa [map_subgroupOf_eq_of_le hBH] at hm

theorem pCoreIn_le_sylow {p : ℕ} (H : Subgroup G) (S : Sylow p H) :
    H.pCoreIn p ≤ (S : Subgroup H).map H.subtype :=
  map_mono (pCore_isPGroup.le_sylow_of_normal S)

/-- A normal `p`-subgroup contained in both factors lies in the core of
their intersection. -/
theorem le_pCoreIn_inf {p : ℕ} {B H M : Subgroup G}
    (hB : IsPGroup p B) (hBH : B ≤ H) (hBM : B ≤ M)
    (hH : H ≤ normalizer (B : Set G)) : B ≤ (H ⊓ M).pCoreIn p :=
  le_pCoreIn_of_normalizes hB (le_inf hBH hBM) (inf_le_left.trans hH)

/-- The centralizer bound at the heart of the local setup: it suffices for
`H` to contain the ambient centralizer of its normal `p`-subgroup `B`. -/
theorem centralizer_pCoreIn_inf_le {p : ℕ} {B H M : Subgroup G}
    (hB : IsPGroup p B) (hBH : B ≤ H) (hBM : B ≤ M)
    (hH : H ≤ normalizer (B : Set G)) (hC : centralizer (B : Set G) ≤ H) :
    M.pCoreIn p ⊓ centralizer ((H ⊓ M).pCoreIn p : Set G) ≤ H :=
  inf_le_right.trans ((centralizer_le (le_pCoreIn_inf hB hBH hBM hH)).trans hC)

/-- A Sylow subgroup of `H` contained in a `p`-subgroup `T` is exactly
`T ∩ H`, with both sides viewed in the ambient group. -/
theorem inf_eq_sylow_map {p : ℕ} {H T : Subgroup G}
    (S : Sylow p H) (hT : IsPGroup p T)
    (hST : (S : Subgroup H).map H.subtype ≤ T) :
    T ⊓ H = (S : Subgroup H).map H.subtype := by
  have hp : IsPGroup p (T.subgroupOf H) := hT.comap_subtype
  have he : T.subgroupOf H = (S : Subgroup H) :=
    S.is_maximal' hp (by
      intro x hx
      exact hST (mem_map.mpr ⟨x, hx, rfl⟩))
  have hm := congrArg (fun K : Subgroup H => K.map H.subtype) he
  simpa only [subgroupOf_map_subtype] using hm

end Subgroup
