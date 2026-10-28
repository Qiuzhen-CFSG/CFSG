module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Source
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# Numerical consequences of the exchanged factors

Conjugation identifies the two moved summands. Their direct sum therefore has
dimension four or eight, with p=3 in dimension four. The actual commuting
product of dihedral actors and its index-two overgroup also determine the
order of H/O₂(H). These are numerical inputs to orthogonal recognition, not
proofs of the critical-pair alternatives.

Source: Aschbacher--Smith 14.6.12--13, printed pp.1031--1032.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair
open OddNormalizer Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]
variable {H U Z : Subgroup G} [IsElementaryAbelian 2 U]

omit [Finite G] in
/-- The two dihedral factors and the index-two exchange determine the order
of the literal actor H/O₂(H), including the order 72 in the cubic branch. -/
theorem exchanged_actor_card
    (a : LocalQuotientAction H U Z) (T : Subgroup G)
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a T p H0 H1 H2) :
    Nat.card (H ⧸ pCore 2 H) = 8 * p ^ 2 := by
  let q := QuotientGroup.mk' (pCore 2 H)
  have hQ : q.ker ≤ H0.subgroupOf H := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    exact d.first_le (d.core_le_first (mem_map_of_mem H.subtype hx))
  have hi : (actorImage H H0).index = 2 :=
    ((H0.subgroupOf H).index_map_eq (QuotientGroup.mk'_surjective _) hQ).trans d.index
  have he : actorImage H H0 = actorImage H H1 ⊔ actorImage H H2 := by
    unfold actorImage
    rw [← Subgroup.map_sup, ← subgroupOf_sup (d.first_le.trans d.zero_le)
      (d.second_le.trans d.zero_le),d.join_eq]
  have hc : actorImage H H1 ≤ centralizer (actorImage H H2 : Set _) := by
    intro x hx y hy
    exact (d.actors_commute x hx y hy).symm
  obtain ⟨f,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    (actorImage H H1) (actorImage H H2) d.actors_disjoint hc
  have hsize : Nat.card (actorImage H H0) = (2*p)*(2*p) := by
    rw [he,← Nat.card_congr f.toEquiv,Nat.card_prod,
      Nat.card_congr d.first_model.some.toEquiv,Nat.card_congr d.second_model.some.toEquiv,
      DihedralGroup.nat_card]
  have hh := (actorImage H H0).card_mul_index
  rw [hi,hsize] at hh
  calc
    Nat.card (H ⧸ pCore 2 H) = (2*p)*(2*p)*2 := hh.symm
    _ = 8*p^2 := by ring

omit [Finite G] in
theorem exchanged_dimensions_eq
    (a : LocalQuotientAction H U Z) (T : Subgroup G) (hTH : T ≤ H)
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a T p H0 H1 H2) :
    Module.finrank (ZMod 2) (subspaceCommutator a.representation ⊤ (actorImage H H1)) =
      Module.finrank (ZMod 2) (subspaceCommutator a.representation ⊤ (actorImage H H2)) := by
  obtain ⟨x,hx,_hxN,hex⟩ := d.exchanged
  let y : H := ⟨x⁻¹,H.inv_mem (hTH hx)⟩
  have he := actorImage_conjugate H1 (d.first_le.trans d.zero_le) y
  change actorImage H (H1.map (MulAut.conj x⁻¹).toMonoidHom) = _ at he
  rw [hex] at he
  rw [he, ← moved_map_conjugate]
  exact (LinearEquiv.finrank_map_eq
    (LinearEquiv.ofBijective (a.representation (QuotientGroup.mk' (pCore 2 H) y))
      (a.representation.apply_bijective _)) _).symm

/-- The actual moved section has dimension four or eight, and four forces p=3. -/
theorem exchanged_moved_dimension
    (a : LocalQuotientAction H U Z) (T : Subgroup G) (hTH : T ≤ H)
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a T p H0 H1 H2) :
    (p = 3 ∧ Module.finrank (ZMod 2)
      (subspaceCommutator a.representation ⊤ ⊤) = 4) ∨
      Module.finrank (ZMod 2) (subspaceCommutator a.representation ⊤ ⊤) = 8 := by
  have he := exchanged_dimensions_eq a T hTH p H0 H1 H2 d
  have hh := Submodule.finrank_sup_add_finrank_inf_eq
    (subspaceCommutator a.representation ⊤ (actorImage H H1))
    (subspaceCommutator a.representation ⊤ (actorImage H H2))
  rw [d.split,d.disjoint.eq_bot,finrank_bot,add_zero,← he] at hh
  have hd := d.first_dimension
  omega

end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair
