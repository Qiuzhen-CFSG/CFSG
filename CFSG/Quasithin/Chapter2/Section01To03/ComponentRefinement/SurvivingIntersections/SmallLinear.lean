module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.Setup
public import Theory.SpecificGroups.SL2.PrimeFiveEquiv
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Theory.SpecificGroups.SymmetricFourSolvable

/-!
# The overlapping small prime-field linear cases

A component identified with PSL₂(p) cannot have p ≤ 3: its faithful
projective-line action embeds it in the solvable group S₄, contradicting
its nontrivial perfectness. Primality then leaves parameters five and
seven, or p > 7. At five the actual matrix group is isomorphic to PSL₂(4),
and at seven it is isomorphic to PSL₃(2), by the exceptional comparison.
Thus the surviving prime-field calculation may restrict to p > 7 after
these genuine Bender and characteristic-two identifications.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
1.1.5(3)(e) and the reductions in 2.3.9(7), printed pp.502 and 525–526.
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization MatrixGroups
open Subgroup
namespace CFSG.Quasithin.Chapter2.ComponentRefinement

private theorem small_psl2_solvable (F : Type*) [Field F] [Finite F]
    (hF : Nat.card F ≤ 3) : Group.IsSolvable (PSL(2,F)) := by
  classical
  let Ω := ℙ F (Fin 2 → F)
  let : Fintype Ω := Fintype.ofFinite Ω
  have hΩ : Fintype.card Ω ≤ 4 := by
    rw [← Nat.card_eq_fintype_card]
    change Nat.card (ℙ F (Fin 2 → F)) ≤ 4
    rw [Projectivization.card_of_finrank_two F (Fin 2 → F) (by simp)]
    omega
  let i : Ω ↪ Fin 4 :=
    (Fintype.equivFin Ω).toEmbedding.trans (Fin.castLEEmb hΩ)
  let act : PSL(2,F) →* Equiv.Perm Ω := MulAction.toPermHom _ _
  let a : PSL(2,F) →* Equiv.Perm (Fin 4) :=
    (Equiv.Perm.viaEmbeddingHom i).comp act
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  exact Group.isSolvable_of_isSolvable_injective (f := a)
    ((Equiv.Perm.viaEmbeddingHom_injective i).comp MulAction.toPerm_injective)

/-- Nontrivial perfectness excludes the solvable small prime parameters. -/
theorem LocalSetup.linearPrime_gt_three {G : Type*} [Group G]
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (p : ℕ) [Fact p.Prime]
    (e : L ≃* PSL(2,ZMod p)) : 3 < p := by
  let : Nontrivial L := (Subgroup.nontrivial_iff_ne_bot L).mpr
    (fun hz => h.outside (hz ▸ bot_le))
  let : Theory.GroupTheory.IsQuasisimple (L.subgroupOf H) := h.component.2
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := (Subgroup.subgroupOfEquivOfLe h.component_le).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe h.component_le).surjective
  by_contra hp
  let : Group.IsSolvable (PSL(2,ZMod p)) := small_psl2_solvable (ZMod p) (by
    simpa using (show p ≤ 3 by omega))
  have hs : Group.IsSolvable L :=
    Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact Group.IsPerfect.not_isSolvable L hs

/-- All small overlaps are actual characteristic-two model isomorphisms. -/
theorem LocalSetup.linearPrime_small_alternatives {G : Type*} [Group G]
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (p : ℕ) [Fact p.Prime]
    (e : L ≃* PSL(2,ZMod p)) :
    (p = 5 ∧ Nonempty (L ≃* PSL(2,GaloisField 2 2))) ∨
    (p = 7 ∧ Nonempty (L ≃* PSL(3,ZMod 2))) ∨ 7 < p := by
  by_cases hbig : 7 < p
  · exact Or.inr (Or.inr hbig)
  have hsmall : p = 5 ∨ p = 7 := by
    have hgt := h.linearPrime_gt_three p e
    have hprime : p.Prime := Fact.out
    interval_cases p <;> norm_num at *
  rcases hsmall with rfl | rfl
  · obtain ⟨e5⟩ := Matrix.ProjectiveSpecialLinearGroup.five_equiv_four
    exact Or.inl ⟨rfl, ⟨e.trans e5⟩⟩
  · exact Or.inr (Or.inl ⟨rfl, ⟨e.trans
      Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two⟩⟩)

end CFSG.Quasithin.Chapter2.ComponentRefinement

end
