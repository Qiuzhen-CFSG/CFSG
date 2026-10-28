module
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.AlternatingSixMovedModel
public import Theory.Representation.HexacodeAction.Cover

/-!
# The B.5.1 action on the actual covered-six component

The component has order 1080. Its two-part has order eight, excluding every
linear and exceptional row except the triple-cover row. The resulting action
retains the literal moved quotient and the source projective-line convention.
The same order comparison excludes every nonsplit and supplement row, so the
full moved module is six-dimensional with a complement fixed by the actor.

Source: Aschbacher--Smith B.4.2, B.5.1 and 13.6.22, pp.86, 99--103, 932.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.CoveredSixModels
open ChapterB.QuasisimpleSource ChapterB.SourceInduction.ProjectiveLine

private theorem binary_card (n : ℕ) :
    Nat.card SL(n,ZMod 2) = ∏ i : Fin n, (2^n - 2^i.val) := by
  rw [Nat.card_congr (BinaryLinear.OuterCyclic.slEquivLinear n).toEquiv,
    ← Nat.card_congr (BinaryLinear.OuterCyclic.matrixEquivLinear n).toEquiv,
    Matrix.card_GL_field]
  simp

private theorem two_power_bound {k : ℕ} (h : 2 ^ k ∣ 1080) : k ≤ 3 := by
  by_contra hk
  have hd : 16 ∣ 1080 := (pow_dvd_pow 2 (by omega : 4 ≤ k)).trans h
  norm_num at hd

private theorem no_linearTwo {E : Type*} [Group E] (hE : Nat.card E = 1080)
    (F : BinaryField) (e : E ≃* SL(2,F.Carrier)) : False := by
  have hc : Nat.card SL(2,F.Carrier) = 1080 := (Nat.card_congr e.toEquiv).symm.trans hE
  rw [GorensteinWalter.sl2_card_formula,F.card_eq] at hc
  have hd : F.degree ≤ 3 := two_power_bound (hc ▸ dvd_mul_right (2 ^ F.degree) _)
  have hp := F.degree_pos
  interval_cases he : F.degree <;> norm_num [he] at hc

private noncomputable def fieldTwoEquiv (F : BinaryField) (h : F.degree = 1) :
    F.Carrier ≃+* ZMod 2 := by
  let : Fintype F.Carrier := Fintype.ofFinite _
  exact FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, F.card_eq,h]
    simp)

private theorem no_linearThree {E : Type*} [Group E] (hE : Nat.card E = 1080)
    (F : BinaryField) (e : E ≃* SL(3,F.Carrier)) : False := by
  have hc : Nat.card SL(3,F.Carrier) = 1080 := (Nat.card_congr e.toEquiv).symm.trans hE
  have hd := (Matrix.PSL3.LinearThree.unipotentSL F.Carrier).card_subgroup_dvd_card
  rw [Matrix.PSL3.LinearThree.card_unipotentSL,F.card_eq,← pow_mul,hc] at hd
  have hb := two_power_bound hd
  have he : F.degree = 1 := by have := F.degree_pos; omega
  have hh := Nat.card_congr (Atlas.fieldEquivSL 3 (fieldTwoEquiv F he)).toEquiv
  rw [hc,binary_card] at hh
  norm_num [Fin.prod_univ_succ] at hh

private theorem no_symplectic {E : Type*} [Group E] (hE : Nat.card E = 1080)
    (F : BinaryField) (e : E ≃* Matrix.symplecticGroup (Fin 2) F.Carrier) : False := by
  have hc := (Nat.card_congr e.toEquiv).symm.trans hE
  have hd := (Theory.SpecificGroups.SymplecticFour.unipotent (F := F.Carrier)).card_subgroup_dvd_card
  rw [Theory.SpecificGroups.SymplecticFour.card_unipotent,F.card_eq,← pow_mul,hc] at hd
  have hb := two_power_bound hd
  have := F.degree_pos
  omega

private theorem no_g2 {E : Type*} [Group E] (hE : Nat.card E = 1080)
    (F : BinaryField) (e : E ≃* Atlas.G2.Model F.Carrier) : False := by
  have hc := (Nat.card_congr e.toEquiv).symm.trans hE
  have hd := (Atlas.G2.unipotent (K := F.Carrier)).card_subgroup_dvd_card
  rw [Atlas.G2.card_unipotent,F.card_eq,← pow_mul,hc] at hd
  have hb := two_power_bound hd
  have := F.degree_pos
  omega

private theorem no_binaryLinear {E : Type*} [Group E] (hE : Nat.card E = 1080)
    {d : ℕ} (hd : d = 4 ∨ d = 5) (e : E ≃* SL(d,ZMod 2)) : False := by
  have hc := (Nat.card_congr e.toEquiv).symm.trans hE
  rcases hd with rfl | rfl <;> rw [binary_card] at hc <;>
    norm_num [Fin.prod_univ_succ] at hc

private theorem no_alternating {E : Type*} [Group E] (hE : Nat.card E = 1080)
    {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) (e : E ≃* alternatingGroup (Fin n)) : False := by
  have hc := (Nat.card_congr e.toEquiv).symm.trans hE
  rcases hn with rfl | rfl | rfl | rfl <;>
    rw [nat_card_alternatingGroup] at hc <;> norm_num [Nat.factorial] at hc

universe u v
variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) {C J : Subgroup D}

/-- The original irreducible source list reduces to its covered-six row,
including the literal projective-plane offender coordinates. -/
theorem irreducible_tripleSix
    (h : ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ C J)
    (e : C ≃* Atlas.Codes.HexEvenAutomorphisms) :
    J = C ∧ Nonempty (ChapterB.SourceInduction.ProjectiveLine.TripleSixAction ρ C) ∧
      quadraticRatio ρ = 1 := by
  have hc : Nat.card C = 1080 := (Nat.card_congr e.toEquiv).trans Atlas.Codes.hexEven_card
  cases h with
  | linearTwo F _ a _ _ => exact (no_linearTwo hc F a.groupEquiv).elim
  | linearThree F _ a _ => exact (no_linearThree hc F a.groupEquiv).elim
  | symplectic F _ _ a _ => exact (no_symplectic hc F a.groupEquiv).elim
  | symplecticTwo a _ =>
    exact (no_alternating hc (Or.inr (Or.inl rfl))
      (ChapterB.QuasisimpleSource.ExtensionConsequences.SymplecticTwo.markedAlternatingActionEquiv a).groupEquiv).elim
  | g2 F _ _ a _ _ => exact (no_g2 hc F a.groupEquiv).elim
  | g2Two a _ _ =>
    have hh := (Nat.card_congr a.subgroupEquiv.toEquiv).symm.trans hc
    rw [Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hh
    norm_num at hh
  | symmetric n hn a _ _ =>
    exact (no_alternating hc (by rcases hn with rfl | rfl <;> simp) a.subgroupEquiv).elim
  | alternatingSix _ a _ _ => exact (no_alternating hc (Or.inr (Or.inl rfl)) a.groupEquiv).elim
  | alternatingSeven _ _ a _ _ _ => exact (no_alternating hc (Or.inr (Or.inr (Or.inl rfl))) a).elim
  | tripleSix hg a hr => exact ⟨hg, ⟨a⟩, hr⟩
  | binaryLinear d hd _ a _ => exact (no_binaryLinear hc hd a.groupEquiv).elim
  | orthogonalSix _ _ a _ _ => exact (no_alternating hc (Or.inr (Or.inr (Or.inr rfl))) a.groupEquiv).elim
  | symmetricEight _ a _ => exact (no_alternating hc (Or.inr (Or.inr (Or.inr rfl))) a.subgroupEquiv).elim
  | exteriorFive _ _ a _ _ _ => exact (no_binaryLinear hc (Or.inr rfl) a).elim

/-- The complete B.5.1 conclusion selects the covered-six action on its
actual moved quotient, including faithfulness and component irreducibility. -/
theorem source_tripleSix
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ C)
    (e : C ≃* Atlas.Codes.HexEvenAutomorphisms) :
    IsIrrPlus ρ C c.sectionData.space.toSubmodule ∧
      Function.Injective c.sectionData.action ∧
      IsIrreducible (c.sectionData.action.comp C.subtype) ∧
      offenderSubgroup c.sectionData.action = C ∧
      Nonempty (ChapterB.SourceInduction.ProjectiveLine.TripleSixAction c.sectionData.action C) ∧
      quadraticRatio c.sectionData.action = 1 := by
  have hc : Nat.card C = 1080 := (Nat.card_congr e.toEquiv).trans Atlas.Codes.hexEven_card
  cases c.clause_one with
  | irreducible hi hf hir hs _ => exact ⟨hi, hf, hir, irreducible_tripleSix _ hs e⟩
  | doubleThree F _ a _ _ => exact (no_linearThree hc F a.groupEquiv).elim
  | naturalDual d hd _ hn => exact (no_binaryLinear hc hd hn.some.groupEquiv).elim
  | repeatedNatural d r hd _ _ _ hn => exact (no_binaryLinear hc hd hn.some.groupEquiv).elim

/-- No nonsplit B.5.1 row has the actual covered-six component. -/
theorem nonsplit_impossible (e : C ≃* Atlas.Codes.HexEvenAutomorphisms) :
    ¬ NonsplitNatural (ρ.comp C.subtype) := by
  have hc : Nat.card C = 1080 := (Nat.card_congr e.toEquiv).trans Atlas.Codes.hexEven_card
  intro h
  cases h with
  | linearTwo F h => exact no_linearTwo hc F h.some.groupEquiv
  | symplectic F h => exact no_symplectic hc F h.some.groupEquiv
  | g2 F h => exact no_g2 hc F h.some.groupEquiv
  | alternatingSix h => exact no_alternating hc (Or.inr (Or.inl rfl)) h.some.groupEquiv
  | alternatingEight h => exact no_alternating hc (Or.inr (Or.inr (Or.inr rfl))) h.some.groupEquiv
  | derivedG2 h =>
    have hh := (Nat.card_congr h.some.groupEquiv.toEquiv).symm.trans hc
    rw [Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hh
    norm_num at hh
  | linearThree h => exact no_linearThree hc BinaryField.two h.some.groupEquiv

/-- The original moved space splits from its full component-fixed space. -/
theorem source_split
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ C)
    (e : C ≃* Atlas.Codes.HexEvenAutomorphisms) :
    IsCompl c.sectionData.space.toSubmodule (fixedSpace ρ C) := by
  by_contra h
  exact nonsplit_impossible c.sectionData.action e (c.clause_two h).2

/-- The central denominator is zero on the literal source moved space. -/
theorem source_central_eq_bot
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ C)
    (e : C ≃* Atlas.Codes.HexEvenAutomorphisms) :
    c.sectionData.central.toSubmodule = ⊥ := by
  have hzero := (source_split ρ c e).inf_eq_bot
  apply le_antisymm ?_ bot_le
  intro w hw
  have hfixed : (w : V) ∈ fixedSpace ρ C := by
    intro g
    exact congrArg Subtype.val ((c.sectionData.central_eq ▸ hw) g)
  have hz : (w : V) ∈ c.sectionData.space.toSubmodule ⊓ fixedSpace ρ C := ⟨w.property, hfixed⟩
  rw [hzero] at hz
  exact Subtype.ext hz

/-- The complement is fixed by the original whole actor. -/
theorem source_invariant_split
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ C)
    (e : C ≃* Atlas.Codes.HexEvenAutomorphisms) :
    IsCompl c.sectionData.space.toSubmodule ρ.invariants := by
  have hsup : c.sectionData.space.toSubmodule ⊔ ρ.invariants = ⊤ := by
    rcases c.clause_five with h | h
    · exact h
    · apply False.elim
      apply nonsplit_impossible c.sectionData.action e
      cases h.2.1 with
      | symplectic F h => exact .symplectic F h
      | alternatingSix h => exact .alternatingSix h
      | alternatingEight h => exact .alternatingEight h
      | linearThree h => exact .linearThree h
  refine ⟨?_, codisjoint_iff.mpr hsup⟩
  apply (source_split ρ c e).disjoint.mono_right
  intro w hw c
  exact hw c.val

/-- The six-dimensional claim concerns the full source moved module. -/
theorem source_moved_finrank
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ C)
    (e : C ≃* Atlas.Codes.HexEvenAutomorphisms) :
    Module.finrank (ZMod 2) c.sectionData.space.toSubmodule = 6 := by
  obtain ⟨_, _, _, _, ⟨a⟩, _⟩ := source_tripleSix ρ c e
  exact ((c.sectionData.central.toSubmodule.quotEquivOfEqBot
    (source_central_eq_bot ρ c e)).finrank_eq).symm.trans a.dimension

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.CoveredSixModels
