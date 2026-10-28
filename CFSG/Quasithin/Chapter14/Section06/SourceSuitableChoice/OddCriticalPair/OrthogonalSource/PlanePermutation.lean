module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Support
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Setup

/-!
# Permutation of the two actual moved planes

The index-two subgroup normalizes both factors. Every other element lies in
the exchange coset, so it interchanges them. Conjugation transport then gives
the same pair permutation on their literal moved subspaces in U/Z.

Source: Aschbacher--Smith 14.6.12--13, printed pp.1031--1032.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair.OrthogonalSource
open OddNormalizer Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne

private theorem pair_permuted {K : Type*} [Group K] (D A B : Subgroup K)
    (hi : D.index = 2) (hA : D ≤ normalizer (A : Set K))
    (hB : D ≤ normalizer (B : Set K)) (x : K) (hx : x ∉ D)
    (hex : A.map (MulAut.conj x).toMonoidHom = B) (g : K) :
    (A.map (MulAut.conj g).toMonoidHom = A ∧ B.map (MulAut.conj g).toMonoidHom = B) ∨
    (A.map (MulAut.conj g).toMonoidHom = B ∧ B.map (MulAut.conj g).toMonoidHom = A) := by
  have hxx : x*x ∈ D := (D.mul_mem_iff_of_index_two hi).mpr (by simp)
  have hswap : B.map (MulAut.conj x).toMonoidHom = A := by
    rw [← hex, map_map]
    have hc : (MulAut.conj x).toMonoidHom.comp (MulAut.conj x).toMonoidHom =
        (MulAut.conj (x*x)).toMonoidHom := by
      ext z
      simp [MulAut.conj_apply,mul_assoc]
    rw [hc]
    exact mem_normalizer_iff_map_conj_eq.mp (hA hxx)
  by_cases hg : g ∈ D
  · exact Or.inl ⟨mem_normalizer_iff_map_conj_eq.mp (hA hg),
      mem_normalizer_iff_map_conj_eq.mp (hB hg)⟩
  · exact Or.inr ⟨(map_conj_eq_of_index_two D A hi hA g x hg hx).trans hex,
      (map_conj_eq_of_index_two D B hi hB g x hg hx).trans hswap⟩

variable {G : Type*} [Group G] {H U Z : Subgroup G} [IsElementaryAbelian 2 U]

theorem exchanged_factors_permuted (a : LocalQuotientAction H U Z)
    (T : Subgroup G) (hTH : T ≤ H) (p : ℕ) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a T p H0 H1 H2) (g : H) :
    (H1.map (MulAut.conj (g:G)).toMonoidHom = H1 ∧
     H2.map (MulAut.conj (g:G)).toMonoidHom = H2) ∨
    (H1.map (MulAut.conj (g:G)).toMonoidHom = H2 ∧
     H2.map (MulAut.conj (g:G)).toMonoidHom = H1) := by
  have h1H := d.first_le.trans d.zero_le
  have h2H := d.second_le.trans d.zero_le
  have hmap (A : Subgroup G) (hAH : A ≤ H) (g : H) :
      ((A.subgroupOf H).map (MulAut.conj g).toMonoidHom).map H.subtype =
        A.map (MulAut.conj (g:G)).toMonoidHom := by
    calc
      _ = ((A.subgroupOf H).map H.subtype).map (MulAut.conj (g:G)).toMonoidHom := by
        rw [map_map,map_map]
        rfl
      _ = A.map (MulAut.conj (g:G)).toMonoidHom := by
        rw [map_subgroupOf_eq_of_le hAH]
  obtain ⟨x,hx,hxN,hex⟩ := d.exchanged
  let y : H := ⟨x⁻¹,H.inv_mem (hTH hx)⟩
  have hy : y ∉ H0.subgroupOf H := by
    intro hy
    exact hxN (inv_mem_iff.mp (d.normalizes_first hy))
  have hn1 : H0.subgroupOf H ≤ normalizer (H1.subgroupOf H : Set H) := by
    rw [← subgroupOf_normalizer_eq h1H]
    exact fun _ h => d.normalizes_first h
  have hn2 : H0.subgroupOf H ≤ normalizer (H2.subgroupOf H : Set H) := by
    rw [← subgroupOf_normalizer_eq h2H]
    exact fun _ h => d.normalizes_second h
  have hex' : (H1.subgroupOf H).map (MulAut.conj y).toMonoidHom = H2.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hmap H1 h1H, map_subgroupOf_eq_of_le h2H]
    exact hex
  have hp := pair_permuted (H0.subgroupOf H) (H1.subgroupOf H) (H2.subgroupOf H)
    d.index hn1 hn2 y hy hex' g
  have ht {A B : Subgroup G} (hAH : A ≤ H) (hBH : B ≤ H)
      (hh : (A.subgroupOf H).map (MulAut.conj g).toMonoidHom = B.subgroupOf H) :
      A.map (MulAut.conj (g:G)).toMonoidHom = B := by
    have hh' := congrArg (fun X : Subgroup H => X.map H.subtype) hh
    rwa [hmap A hAH, map_subgroupOf_eq_of_le hBH] at hh'
  rcases hp with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact Or.inl ⟨ht h1H h1H ha,ht h2H h2H hb⟩
  · exact Or.inr ⟨ht h1H h2H ha,ht h2H h1H hb⟩

theorem exchanged_spaces_permuted (a : LocalQuotientAction H U Z)
    (T : Subgroup G) (hTH : T ≤ H) (p : ℕ) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a T p H0 H1 H2) (g : H ⧸ pCore 2 H) :
    let A := subspaceCommutator a.representation ⊤ (actorImage H H1)
    let B := subspaceCommutator a.representation ⊤ (actorImage H H2)
    (A.map (a.representation g) = A ∧ B.map (a.representation g) = B) ∨
    (A.map (a.representation g) = B ∧ B.map (a.representation g) = A) := by
  dsimp only
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) g
  rw [moved_map_conjugate,moved_map_conjugate,
    ← actorImage_conjugate H1 (d.first_le.trans d.zero_le) g,
    ← actorImage_conjugate H2 (d.second_le.trans d.zero_le) g]
  rcases exchanged_factors_permuted a T hTH p H0 H1 H2 d g with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact Or.inl ⟨by rw [h1],by rw [h2]⟩
  · exact Or.inr ⟨by rw [h1],by rw [h2]⟩

end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair.OrthogonalSource
