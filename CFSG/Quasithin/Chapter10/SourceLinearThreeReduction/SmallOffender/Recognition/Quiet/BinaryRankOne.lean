module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Quiet.Families
public import Theory.Representation.SL2.MinimalBinaryDegree

/-!
# Every quiet even-field rank-one quotient is excluded

The general TI bound handles fields of order at least sixteen. Over eight,
it bounds the moved quotient by degree six. The quotient is semisimple and
fully moved, hence has no fixed vectors. The minimum nontrivial SL₂(8)
degree is six, forcing irreducibility. Schur's lemma supplies crossed
centralization and the full-normalizer bound, so the checked large-module
contradiction applies. Over four the actual A₅ isomorphism contradicts the
original non-A₅ input.

Quiet.FamilySelection uses this with the literal quotient catalogue.
Source: Aschbacher--Smith 10.1.1 and 10.2.12, pp.741,754--755.
-/

public noncomputable section
open scoped IsMulCommutative MonoidAlgebra MatrixGroups
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Subgroup Theory.GroupTheory Representation
open Chapter3.Section02 ChapterE PointControl.Selection
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem no_quiet_binary_rank_one_eight
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (hF : Nat.card F = 8) : False := by
  have hr : primeRank 2 (MulAut SL(2,F)) ≤ 3 :=
    Theory.PSL2.BinaryAutomorphismRank.sl2_automorphism_two_rank_le (by decide) hF
  have hr' : primeRank 2 (MulAut (L ⧸ pCore 2 L)) ≤ 3 := by
    rw [primeRank_equiv 2 (MulAut.congr e)]
    exact hr
  have hu := quiet_moved_card_le_of_automorphism_rank D c hJ hNL
    (binary_rank_one_three_dvd e (n := 3) hF) hr'
  let := source_full_moved_elementary D
  let Q := Additive ((⁅D.fullModule,L⁆ : Subgroup G) ⧸
    (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G)).subgroupOf ⁅D.fullModule,L⁆)
  obtain ⟨ρ,s,hf,_⟩ := exists_moved_quotient_action D c.nonnormal e
  have hc : Nat.card Q ≤ 2 ^ 6 :=
    (Nat.card_le_card_of_surjective s.coordinates s.onto).trans hu
  have hd : Module.finrank (ZMod 2) Q ≤ 6 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hc
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc
  let : IsSemisimpleModule (ZMod 2)[SL(2,F)] ρ.asModule :=
    quiet_moved_section_semisimple D c.many c.minimal c.nonnormal hJ ρ e s
  have hgen : Coinvariants.ker ρ = ⊤ :=
    s.coinvariants_eq_top_of_group_generation L le_rfl ρ
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) (fun _ _ => rfl) (by
      rw [commutator_comm,source_full_moved_eq_commutator D,sup_eq_left.mpr inf_le_left])
  have hfix := invariants_eq_bot_of_semisimple_of_coinvariants_eq_top ρ hgen
  let : IsSimpleGroup (L ⧸ pCore 2 L) := ModuleChoice.component_quotient_simple D c.nonnormal
  let : Nontrivial SL(2,F) := e.symm.surjective.nontrivial
  have hnρ : ∃ a, ρ a ≠ 1 := by
    obtain ⟨a,ha⟩ := exists_ne (1 : SL(2,F))
    exact ⟨a,fun he => ha (hf (he.trans ρ.map_one.symm))⟩
  let : Nontrivial Q := by
    by_contra hn
    let : Subsingleton Q := not_nontrivial_iff_subsingleton.mp hn
    obtain ⟨a,ha⟩ := hnρ
    exact ha (Subsingleton.elim _ _)
  let hi : ρ.IsIrreducible := SL2.irreducible_of_fixed_free_minimal_binary_degree
    ρ hfix (n := 3) (by decide) hF hd
  have hlow := SL2.Unsigned.irreducible_finrank_bound 2 ρ hnρ 3 (by decide) hF
  change 6 ≤ Module.finrank (ZMod 2) Q at hlow
  have hcard : Nat.card Q = 2 ^ Module.finrank (ZMod 2) Q := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  obtain ⟨b⟩ := large_bounds_of_irreducible_marking D ρ hf hi e s c.nonnormal
    (by omega : 3 < Module.finrank (ZMod 2) Q) hcard hr (by omega)
  exact FixedSpaces.large_module_false_of_normalizer D c b hNL

/-- The complete even-field rank-one exclusion under the original source prefix. -/
theorem no_quiet_binary_rank_one
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) : False := by
  by_cases hlarge : 4 ≤ n
  · exact no_quiet_large_binary_rank_one D c hJ hNL e hlarge hF
  have hcases : n = 2 ∨ n = 3 := by omega
  rcases hcases with rfl | rfl
  · exact not_slTwo_of_not_alternatingFive c.notA5 hF ⟨e⟩
  · exact no_quiet_binary_rank_one_eight D c hJ hNL e hF

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
