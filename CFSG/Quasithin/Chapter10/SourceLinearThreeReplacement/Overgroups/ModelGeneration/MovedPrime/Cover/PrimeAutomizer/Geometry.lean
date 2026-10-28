module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.MovedPrime.Cover.Inputs
public import Theory.GroupTheory.UniqueMaximalNormalExtension

/-!
# Invariant seeds and Sylow overgroup geometry

Intersecting a Sylow overgroup with its normal supplement recovers the
original overgroup. Two distinct maximal overgroups with solvable
intersections therefore give a generating invariant cover. A maximal
invariant subgroup of the supplement also suffices when another solvable
seed escapes it. These lattice arguments retain the prescribed embeddings.

Source application: Aschbacher--Smith E.1.12 and 10.3.3, pp.214 and 756.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Cover.PrimeAutomizer
variable {G : Type*} [Group G]

private theorem product {A B : Subgroup G} (hn : B ≤ normalizer (A : Set G))
    {x : G} (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  have hh : x ∈ (A : Set G) * (B : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left A B hn]
    exact hx
  exact hh

/-- The actual intersection with the normal factor recovers each Sylow overgroup. -/
theorem overgroup_eq_inf_sup (L R U : Subgroup G) [L.Normal]
    (hgen : L ⊔ R = ⊤) (hRU : R ≤ U) : (U ⊓ L) ⊔ R = U := by
  apply le_antisymm (sup_le inf_le_left hRU)
  intro x hx
  obtain ⟨l, hl, r, hr, he⟩ := mem_sup_of_normal_left.mp
    (show x ∈ L ⊔ R from hgen.symm ▸ mem_top x)
  have hlU : l ∈ U := by
    have hh := U.mul_mem hx (U.inv_mem (hRU hr))
    rwa [← he, mul_inv_cancel_right] at hh
  rw [← he]
  exact mul_mem_sup ⟨hlU, hl⟩ hr

/-- Intersecting an invariant supplement back into L introduces no extra elements. -/
theorem inf_sup_eq_of_contains_intersection (L R B : Subgroup G)
    (hBL : B ≤ L) (hRB : R ≤ normalizer (B : Set G))
    (hI : L ⊓ R ≤ B) : L ⊓ (B ⊔ R) = B := by
  apply le_antisymm ?_ (le_inf hBL le_sup_left)
  rintro x ⟨hxL, hx⟩
  obtain ⟨b, hb, r, hr, he⟩ := product hRB hx
  have hrL : r ∈ L := by
    have hh := L.mul_mem (L.inv_mem (hBL hb)) hxL
    rwa [← he, inv_mul_cancel_left] at hh
  rw [← he]
  exact B.mul_mem hb (hI ⟨hrL, hr⟩)

/-- Two invariant solvable seeds generating L form the exact required cover. -/
theorem cover_of_pair (L R A B : Subgroup G)
    (hA : A ≤ L) (hB : B ≤ L) (hsA : Group.IsSolvable A) (hsB : Group.IsSolvable B)
    (hnA : R ≤ normalizer (A : Set G)) (hnB : R ≤ normalizer (B : Set G))
    (hgen : A ⊔ B = L) : HasSolvableNormalizedCover L R := by
  refine ⟨{A, B}, ?_, by simpa only [sSup_pair] using hgen⟩
  intro C hC
  rcases Set.mem_insert_iff.mp hC with rfl | hC
  · exact ⟨hA, hsA, hnA⟩
  · have he : C = B := Set.mem_singleton_iff.mp hC
    subst C
    exact ⟨hB, hsB, hnB⟩

/-- Two distinct maximal Sylow overgroups generate through their literal intersections. -/
theorem cover_of_two_solvable_intersections (L : Subgroup G) [L.Normal]
    (R M N : Subgroup G) (hgen : L ⊔ R = ⊤)
    (hRM : R ≤ M) (hRN : R ≤ N) (hM : IsCoatom M) (hN : IsCoatom N) (hne : M ≠ N)
    (hsolM : Group.IsSolvable (M ⊓ L : Subgroup G))
    (hsolN : Group.IsSolvable (N ⊓ L : Subgroup G)) : HasSolvableNormalizedCover L R := by
  have hnM : R ≤ normalizer ((M ⊓ L : Subgroup G) : Set G) :=
    (le_inf (hRM.trans M.le_normalizer) le_normalizer_of_normal).trans
      inf_normalizer_le_normalizer_inf
  have hnN : R ≤ normalizer ((N ⊓ L : Subgroup G) : Set G) :=
    (le_inf (hRN.trans N.le_normalizer) le_normalizer_of_normal).trans
      inf_normalizer_le_normalizer_inf
  have hMN : M ⊔ N = ⊤ := by
    by_contra h
    have he : M ⊔ N = M := (hM.le_iff_eq h).mp le_sup_left
    have he' : M = N := (hN.le_iff_eq hM.1).mp (he ▸ le_sup_right)
    exact hne he'
  let B := (M ⊓ L) ⊔ (N ⊓ L)
  have hBR : B ⊔ R = ⊤ := by
    calc
      B ⊔ R = ((M ⊓ L) ⊔ R) ⊔ ((N ⊓ L) ⊔ R) := by
        simp only [B, sup_assoc, sup_comm, sup_left_comm, sup_left_idem]
      _ = M ⊔ N := by rw [overgroup_eq_inf_sup L R M hgen hRM,
          overgroup_eq_inf_sup L R N hgen hRN]
      _ = ⊤ := hMN
  have hBL : B ≤ L := sup_le inf_le_right inf_le_right
  have hnB : R ≤ normalizer (B : Set G) :=
    (le_inf hnM hnN).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hIB : L ⊓ R ≤ B :=
    (le_inf (inf_le_right.trans hRM) inf_le_left).trans le_sup_left
  have hB : B = L := by
    have h := inf_sup_eq_of_contains_intersection L R B hBL hnB hIB
    simpa only [hBR, inf_top_eq] using h.symm
  exact cover_of_pair L R (M ⊓ L) (N ⊓ L) inf_le_right inf_le_right
    hsolM hsolN hnM hnN hB

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Cover.PrimeAutomizer

namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Cover.PrimeAutomizer
variable {G : Type*} [Group G]

/-- A maximal invariant subgroup of the normal factor gives a maximal Sylow overgroup. -/
theorem coatom_sup_of_coatom_subgroupOf (L R D : Subgroup G) [L.Normal]
    (hgen : L ⊔ R = ⊤) (hDL : D ≤ L) (hnD : R ≤ normalizer (D : Set G))
    (hI : L ⊓ R ≤ D) (hD : IsCoatom (D.subgroupOf L)) : IsCoatom (D ⊔ R) := by
  have hproper : D ⊔ R ≠ ⊤ := by
    intro ht
    have he := inf_sup_eq_of_contains_intersection L R D hDL hnD hI
    rw [ht, inf_top_eq] at he
    exact hD.1 (he ▸ subgroupOf_self L)
  refine ⟨hproper, ?_⟩
  intro U hU
  have hRU : R ≤ U := le_sup_right.trans hU.le
  have hdU : D.subgroupOf L ≤ U.subgroupOf L := comap_mono (le_sup_left.trans hU.le)
  have he : U.subgroupOf L = ⊤ := by
    apply hD.2
    refine lt_of_le_of_ne hdU ?_
    intro he
    have hmap := congrArg (Subgroup.map L.subtype) he
    rw [map_subgroupOf_eq_of_le hDL, subgroupOf_map_subtype] at hmap
    have hUU := overgroup_eq_inf_sup L R U hgen hRU
    rw [← hmap] at hUU
    exact hU.ne hUU
  have hLU : L ≤ U := subgroupOf_eq_top.mp he
  exact top_unique (hgen ▸ sup_le hLU hRU)

/-- Maximality inside L turns one escaping solvable seed into a cover. -/
theorem cover_of_coatom_escape (L R D B : Subgroup G)
    (hDL : D ≤ L) (hBL : B ≤ L) (hD : IsCoatom (D.subgroupOf L))
    (hsD : Group.IsSolvable D) (hsB : Group.IsSolvable B)
    (hnD : R ≤ normalizer (D : Set G)) (hnB : R ≤ normalizer (B : Set G))
    (hescape : ¬ B ≤ D) : HasSolvableNormalizedCover L R := by
  have hjoin : D ⊔ B = L := by
    have ht : (D ⊔ B).subgroupOf L = ⊤ := by
      apply hD.2
      refine lt_of_le_of_ne (comap_mono le_sup_left) ?_
      intro he
      have hm := congrArg (Subgroup.map L.subtype) he
      rw [map_subgroupOf_eq_of_le hDL,
        map_subgroupOf_eq_of_le (sup_le hDL hBL)] at hm
      exact hescape (hm ▸ (le_sup_right : B ≤ D ⊔ B))
    exact le_antisymm (sup_le hDL hBL) (subgroupOf_eq_top.mp ht)
  exact cover_of_pair L R D B hDL hBL hsD hsB hnD hnB hjoin

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Cover.PrimeAutomizer
