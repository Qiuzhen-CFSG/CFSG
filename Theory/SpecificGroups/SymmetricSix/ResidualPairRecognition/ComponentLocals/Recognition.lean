module

public import Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition.ComponentLocals
public import Theory.GroupTheory.DisjointCommutingProduct
/-!
# Intrinsic local centralizers and complements in S₆

An index-three overgroup of a Sylow two-subgroup is conjugate to a duad
or syntheme parabolic. Transporting the canonical calculation along that
same conjugation identifies its residual centralizer, its even S₄ subgroup,
and their product. The alternating subgroup has trivial centralizer.

These are the model calculations used to lift the surviving component case
of Aschbacher–Smith 15.4.18, printed p.1163 (combined 1 March 2004 manuscript).
The central line is the odd residual centralizer; it is disjoint from A₆.
-/

@[expose] public section

open Subgroup Equiv
namespace Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition.ComponentLocals

private theorem map_centralizer (Y : Subgroup S6) (e : S6 ≃* S6) :
    (centralizer (Y : Set S6)).map e.toMonoidHom =
      centralizer (Y.map e.toMonoidHom : Set S6) := by
  apply le_antisymm (map_centralizer_le_centralizer_image _ _)
  intro x hx
  refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
  intro y hy
  apply e.injective
  simpa only [map_mul, e.apply_symm_apply] using hx (e y) (mem_map_of_mem _ hy)

/-- The alternating subgroup has trivial centralizer in the six-letter model. -/
theorem centralizer_alternating : centralizer (A6 : Set S6) = ⊥ := by
  apply le_bot_iff.mp
  intro g hg
  have hd : duadHom.range ≤ A6 := by
    rintro _ ⟨a, rfl⟩
    exact (show ∀ a : A, duadHom a ∈ A6 by decide +kernel) a
  have hc := centralizer_le hd hg
  rw [centralizer_duad] at hc
  have ho := mem_zpowers_iff_mem_range_orderOf.mp hc
  rw [duadFlip_order] at ho
  obtain ⟨n, hn, he⟩ := Finset.mem_image.mp ho
  have hn' : n = 0 ∨ n = 1 := by have hn2 := Finset.mem_range.mp hn; omega
  rcases hn' with rfl | rfl
  · simpa using he.symm
  · have hg' : g = duadFlip := by simpa using he.symm
    subst g
    have hm : (Equiv.swap 0 2 * Equiv.swap 2 3 : S6) ∈ A6 := by decide
    have hh := hg _ hm
    exact (by decide : (Equiv.swap 0 2 * Equiv.swap 2 3 : S6) * duadFlip ≠
      duadFlip * (Equiv.swap 0 2 * Equiv.swap 2 3)) hh |>.elim

/-- Intrinsic centralizer and even-parabolic calculations for an index-three
Sylow overgroup. All subgroups are transported by the same conjugation. -/
theorem local_structure (T : Sylow 2 S6) (H : Subgroup S6)
    (hT : (T : Subgroup S6) ≤ H) (hi : (T : Subgroup S6).relIndex H = 3) :
    let Y := (pResidual 2 H).map H.subtype
    Nat.card (centralizer (Y : Set S6)) = 2 ∧
      centralizer (Y : Set S6) ≤ (T : Subgroup S6) ∧
      centralizer (Y : Set S6) ≤ centralizer (H : Set S6) ∧
      Disjoint (centralizer (Y : Set S6)) A6 ∧
      Nonempty (↥(H ⊓ A6) ≃* Equiv.Perm (Fin 4)) ∧ Nat.card H = 48 := by
  obtain ⟨g, hg, _⟩ := coatoms_over_sylow T
  let e := MulAut.conj g
  let H₀ := e.mapSubgroup.symm H
  have hb : borel ≤ H₀ := by
    have hh := e.mapSubgroup.symm.monotone hT
    rwa [← hg, e.mapSubgroup.symm_apply_apply] at hh
  have hii : borel.relIndex H₀ = 3 := by
    have hh := relIndex_map_map_of_injective (f := e.toMonoidHom) borel H₀ e.injective
    change (e.mapSubgroup borel).relIndex (e.mapSubgroup H₀) = _ at hh
    rw [hg, e.mapSubgroup.apply_symm_apply] at hh
    exact hh.symm.trans hi
  have hchoice := index_three_over_borel H₀ hb hii
  obtain ⟨_, hc, hcb, hch, hd, heven⟩ := canonical_local_structure H₀ hchoice
  have hcard : Nat.card H₀ = 48 := by
    rcases hchoice with he | he
    · rw [he]; exact duadStabilizer_order
    · rw [he]; exact synthemeStabilizer_order
  have hH : H = H₀.map e.toMonoidHom := (e.mapSubgroup.apply_symm_apply H).symm
  have hA : A6.map e.toMonoidHom = A6 := Normal.map_conj_eq _ _
  dsimp only
  rw [hH, ← map_embedded_pResidual]
  simp only [← map_centralizer]
  refine ⟨(Nat.card_congr (e.subgroupMap _).toEquiv).symm.trans hc, ?_, ?_, ?_, ?_, ?_⟩
  · exact (map_mono hcb).trans_eq hg
  · exact map_mono hch
  · rw [← hA, disjoint_iff, ← Subgroup.map_inf _ _ e.toMonoidHom e.injective,
      disjoint_iff.mp hd, Subgroup.map_bot]
  · rw [← hA, ← Subgroup.map_inf _ _ e.toMonoidHom e.injective]
    exact heven.map fun j => (e.subgroupMap _).symm.trans j
  · exact (Nat.card_congr (e.subgroupMap H₀).toEquiv).symm.trans hcard

/-- The centralizer line and even parabolic generate the whole parabolic. -/
theorem local_product (T : Sylow 2 S6) (H : Subgroup S6)
    (hT : (T : Subgroup S6) ≤ H) (hi : (T : Subgroup S6).relIndex H = 3) :
    let Y := (pResidual 2 H).map H.subtype
    centralizer (Y : Set S6) ⊔ (H ⊓ A6) = H := by
  obtain ⟨hc, hct, hch, hd, ⟨e⟩, hh⟩ := local_structure T H hT hi
  dsimp only at hc hct hch hd e ⊢
  have hdis := hd.mono_right (show H ⊓ A6 ≤ A6 from inf_le_right)
  obtain ⟨j, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting _ _ hdis
    (hch.trans (centralizer_le (show H ⊓ A6 ≤ H from inf_le_left)))
  apply eq_of_le_of_card_ge (sup_le (hct.trans hT) inf_le_left)
  rw [← Nat.card_congr j.toEquiv, Nat.card_prod, hc, Nat.card_congr e.toEquiv, hh]
  rw [Nat.card_eq_fintype_card]
  decide

end Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition.ComponentLocals
