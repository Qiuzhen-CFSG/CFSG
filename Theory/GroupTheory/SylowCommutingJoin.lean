module

public import Theory.GroupTheory.SylowNormalizedSupIndex
public import Mathlib.GroupTheory.NoncommPiCoprod

/-!
# Specified Sylow intersections in commuting joins

The product of chosen Sylow subgroups is Sylow in the direct product:
maximality can be checked in each coordinate. The multiplication map from
a finite commuting family then sends this product to a Sylow subgroup of
the join, preserving containment in a specified ambient subgroup.

A normalized-supplement index calculation extends the result across a
normalizing p-subgroup. Both conclusions retain the actual embeddings.

Source application: Aschbacher--Smith, *The Classification of Quasithin
Groups*, E.1.11, printed p.213, the Sylow intersection R_A=T∩K_A.
-/

public section
open Subgroup

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Sylow subgroups in the commuting factors, all embedded in T, give a
Sylow subgroup of their join embedded in T. Central intersections are allowed. -/
theorem exists_sylow_iSup_le_of_commuting {p : ℕ} [Fact p.Prime]
    {ι : Type*} [Finite ι] (C : ι → Subgroup G)
    (hc : Pairwise fun i j => ∀ x y : G, x ∈ C i → y ∈ C j → Commute x y)
    (S : ∀ i, Sylow p (C i)) (T : Subgroup G)
    (hST : ∀ i, (S i : Subgroup (C i)).map (C i).subtype ≤ T) :
    ∃ R : Sylow p (⨆ i, C i : Subgroup G),
      (R : Subgroup (⨆ i, C i : Subgroup G)).map (⨆ i, C i : Subgroup G).subtype ≤ T := by
  classical
  let _ := Fintype.ofFinite ι
  let D : Subgroup (∀ i, C i) := Subgroup.pi Set.univ (fun i => (S i : Subgroup (C i)))
  have hp : IsPGroup p D := by
    intro y
    choose n hn using fun i => (S i).isPGroup' ⟨y.val i, y.property i (Set.mem_univ i)⟩
    refine ⟨∑ i, n i, Subtype.ext (funext fun i => ?_)⟩
    have hi : n i ≤ ∑ j, n j := Finset.single_le_sum
      (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)
    have he : y.val i ^ (p ^ n i) = 1 := congrArg Subtype.val (hn i)
    exact orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_pow_eq_one he).trans
      (pow_dvd_pow p hi))
  obtain ⟨Q, hDQ⟩ := hp.exists_le_sylow
  have hcoord (i : ι) : Q.map (Pi.evalMonoidHom (fun j => C j) i) = (S i : Subgroup (C i)) := by
    apply (S i).is_maximal' (Q.isPGroup'.map _)
    intro x hx
    refine ⟨Pi.mulSingle i x, hDQ ?_, by simp⟩
    intro j _
    change (Pi.mulSingle i x : ∀ k, C k) j ∈ (S j : Subgroup (C j))
    by_cases hij : i = j
    · subst j
      simpa only [Pi.mulSingle_eq_same] using hx
    · simpa only [Pi.mulSingle_eq_of_ne (Ne.symm hij)] using (S j).one_mem
  let f := Subgroup.noncommPiCoprod hc
  let N : Subgroup G := ⨆ i, C i
  have hf : f.range = N := Subgroup.noncommPiCoprod_range
  let g : (∀ i, C i) →* N := f.codRestrict N (fun x => hf.le ⟨x, rfl⟩)
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨y, hy⟩ := hf.ge x.property
    exact ⟨y, Subtype.ext hy⟩
  refine ⟨Q.mapSurjective (f := g) hg, ?_⟩
  rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩
  change f z ∈ T
  rw [Subgroup.noncommPiCoprod_apply]
  apply Subgroup.noncommProd_mem
  intro i _
  apply hST i
  apply mem_map_of_mem
  rw [← hcoord i]
  exact mem_map_of_mem _ hz

/-- Adjoining a normalizing p-subgroup preserves the actual Sylow intersection
when the ambient p-group already contains a Sylow subgroup of the seed. -/
theorem exists_sylow_join_eq_intersection {p : ℕ} [Fact p.Prime]
    (N D T : Subgroup G) (hT : IsPGroup p T) (hDT : D ≤ T)
    (hn : D ≤ normalizer (N : Set G))
    (S : Sylow p N) (hST : (S : Subgroup N).map N.subtype ≤ T) :
    ∃ R : Sylow p (N ⊔ D : Subgroup G),
      (R : Subgroup (N ⊔ D : Subgroup G)) = T.subgroupOf (N ⊔ D) := by
  let K := N ⊔ D
  let U := T ⊓ K
  have hnK : K ≤ normalizer (N : Set G) := sup_le N.le_normalizer hn
  have hNU : N ⊔ U = K := by
    apply le_antisymm (sup_le le_sup_left inf_le_right)
    exact sup_le le_sup_left ((le_inf hDT le_sup_right).trans le_sup_right)
  obtain ⟨R, hR⟩ := IsPGroup.exists_sylow_sup_of_coprime_index N U
    (hT.to_le inf_le_left) (inf_le_right.trans hnK) (S : Subgroup N) S.not_dvd_index
    (le_inf hST ((map_subtype_le _).trans le_sup_left))
  let e := MulEquiv.subgroupCongr hNU
  refine ⟨R.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  apply map_injective K.subtype_injective
  change ((R : Subgroup (N ⊔ U : Subgroup G)).map e.toMonoidHom).map K.subtype = _
  rw [map_map, subgroupOf_map_subtype]
  change (R : Subgroup (N ⊔ U : Subgroup G)).map (N ⊔ U : Subgroup G).subtype = _
  exact hR
end Subgroup

