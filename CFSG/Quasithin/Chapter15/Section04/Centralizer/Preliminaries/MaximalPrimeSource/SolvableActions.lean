module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.PrimeComparison
public import CFSG.Quasithin.ChapterA.Section01.Linear.SolvablePClosed

/-!
# The defining-prime action in the maximal-prime argument

Corrected Dickson gives p-closedness of the actual solvable linear image.
Its p-core quotient is a two-group, killed by two-perfectness. Lifting
through the p-group kernel of A.1.25 therefore makes the original
conjugation image a p-group. The kernel is not discarded.

Source: Aschbacher–Smith, printed p.1157, the first paragraph of 15.4.3.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource

theorem solvable_small_rank_action_isPGroup {A P : Type*} [Group A] [Finite A]
    [Group P] [Finite P] {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hA : IsPPerfect 2 A) (hsolv : Group.IsSolvable A)
    (hs : ∀ q : ℕ, q.Prime → q ∣ Nat.card A → q = 2 ∨ q = p)
    (hP : IsPGroup p P) (hr : primeRank p P ≤ 2)
    (a : A →* MulAut P) : IsPGroup p a.range := by
  let : Group.IsSolvable A := hsolv
  have ho := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  obtain ⟨f, hf⟩ := ChapterA.RankActions.smallRankAutomorphismRepresentation p ho P hP hr
  let b := f.comp a
  let L := b.range
  have hLsolv : Group.IsSolvable L := Group.isSolvable_of_surjective b.rangeRestrict_surjective
  let S : Sylow p L := default
  have hcore : pCore p L = (S : Subgroup L) := le_antisymm
    (pCore_isPGroup.le_sylow_of_normal S)
    (ChapterA.solvable_GL₂_pGroup_le_core hp L hLsolv S S.isPGroup')
  have hindex : ¬ p ∣ Nat.card (L ⧸ pCore p L) := by
    change ¬ p ∣ (pCore p L).index
    rw [hcore]
    exact S.not_dvd_index
  let c := (QuotientGroup.mk' (pCore p L)).comp b.rangeRestrict
  have hc : c = 1 := hom_eq_one_of_prime_not_dvd hA hs hindex c
  have htop : pCore p L = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨y, rfl⟩ := b.rangeRestrict_surjective x
    exact (QuotientGroup.eq_one_iff _).mp (DFunLike.congr_fun hc y)
  have hLp : IsPGroup p L := by
    have ht : IsPGroup p (⊤ : Subgroup L) := htop ▸ pCore_isPGroup
    exact ht.of_equiv Subgroup.topEquiv
  have hle : a.range ≤ L.comap f := by
    rintro _ ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  exact (hLp.comap_of_ker_isPGroup f hf).to_le hle

/-- P-closedness also lifts to the whole solvable automorphism image through
the actual p-group representation kernel. -/
theorem solvable_small_rank_pGroup_le_core {P : Type*} [Group P] [Finite P]
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) (hP : IsPGroup p P)
    (hr : primeRank p P ≤ 2) (H : Subgroup (MulAut P)) (hs : Group.IsSolvable H)
    (U : Subgroup H) (hU : IsPGroup p U) : U ≤ pCore p H := by
  let : Group.IsSolvable H := hs
  have ho := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  obtain ⟨f, hf⟩ := ChapterA.RankActions.smallRankAutomorphismRepresentation p ho P hP hr
  let g := f.subgroupMap H
  have hsI : Group.IsSolvable (H.map f) := Group.isSolvable_of_surjective (f.subgroupMap_surjective H)
  have hk : IsPGroup p g.ker := by
    rw [ker_subgroupMap]
    exact hf.comap_subtype
  have hle := ChapterA.solvable_GL₂_pGroup_le_core hp (H.map f) hsI (U.map g) (hU.map g)
  exact (map_le_iff_le_comap.mp hle).trans
    (le_sSup ⟨inferInstance, pCore_isPGroup.comap_of_ker_isPGroup g hk⟩)

/-- Application to the actual source actor in any solvable overgroup: its
action on a p-core of rank at most two has p-group image. -/
theorem xi_defining_prime_action_isPGroup {G P : Type*} [Group G] [Finite G]
    [Group P] [Finite P] {T X M : Subgroup G} (hX : X ∈ Xi T)
    (hXM : X ≤ M) (hM : Group.IsSolvable M) (hp : 3 < (pCore 2 X).index)
    (hP : IsPGroup (pCore 2 X).index P) (hr : primeRank (pCore 2 X).index P ≤ 2)
    (a : X →* MulAut P) : IsPGroup (pCore 2 X).index a.range := by
  let : Fact (pCore 2 X).index.Prime := ⟨hX.2.2.2.1⟩
  let : Group.IsSolvable M := hM
  exact solvable_small_rank_action_isPGroup hp hX.2.1
    (Group.isSolvable_of_isSolvable_injective (inclusion_injective hXM))
    (xi_prime_support hX) hP hr a
end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource
