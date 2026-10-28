module
public import CFSG.Quasithin.ChapterB.QuasisimpleOffenderModels
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.AlternatingSevenActor
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.FullMovedEquivalence
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.DefiningSylow
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.Homogeneity
/-!
# The exceptional local rows of the genuine FF classification

The actual component has the order of A7, J2 or M23. Comparing the native
B.5.1 actors excludes every reducible row and every irreducible actor except
A7. Neither A7 action is a nonsplit natural extension, so the original moved
space splits from its fixed space. The actual central quotient has dimension
four or six. Source: Aschbacher--Smith 5.1.13 p.637, B.4.2 and B.5.1.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.ExceptionalActions
open ChapterB.QuasisimpleSource ChapterB.SourceInduction.ProjectiveLine

@[expose] def ExceptionalOrder (E : Type*) : Prop :=
  Nat.card E = 2520 ∨ Nat.card E = 604800 ∨ Nat.card E = 10200960

private theorem two_power_bound {E : Type*} (hE : ExceptionalOrder E)
    {k : ℕ} (h : 2 ^ k ∣ Nat.card E) : k ≤ 7 := by
  by_contra hk
  have hd : 256 ∣ Nat.card E := (pow_dvd_pow 2 (by omega : 8 ≤ k)).trans h
  rcases hE with he | he | he <;> rw [he] at hd <;> norm_num at hd

private theorem no_linearTwo {E : Type*} [Group E] (hE : ExceptionalOrder E)
    (F : BinaryField) (e : E ≃* SL(2,F.Carrier)) : False := by
  have hc : Nat.card SL(2,F.Carrier) = Nat.card E := (Nat.card_congr e.toEquiv).symm
  rw [Atlas.card_sl_two,F.card_eq] at hc
  have hd := two_power_bound hE (hc ▸ dvd_mul_right (2 ^ F.degree) _)
  have hp := F.degree_pos
  rcases hE with he | he | he <;> rw [he] at hc <;>
    interval_cases hn : F.degree <;> norm_num [hn] at hc

private theorem no_linearThree {E : Type*} [Group E] (hE : ExceptionalOrder E)
    (F : BinaryField) (e : E ≃* SL(3,F.Carrier)) : False := by
  have hc : Nat.card SL(3,F.Carrier) = Nat.card E := (Nat.card_congr e.toEquiv).symm
  have hd := (Matrix.PSL3.LinearThree.unipotentSL F.Carrier).card_subgroup_dvd_card
  rw [Matrix.PSL3.LinearThree.card_unipotentSL,F.card_eq,← pow_mul,hc] at hd
  have hb := two_power_bound hE hd
  have hp := F.degree_pos
  have hn : F.degree ≤ 2 := by omega
  rw [Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear,F.card_eq] at hc
  rcases hE with he | he | he <;> rw [he] at hc <;>
    interval_cases hd : F.degree <;> norm_num [hd] at hc

private theorem no_symplectic {E : Type*} [Group E] (hE : ExceptionalOrder E)
    (F : BinaryField) (hF : 1 < F.degree)
    (e : E ≃* Matrix.symplecticGroup (Fin 2) F.Carrier) : False := by
  have hc := (Nat.card_congr e.toEquiv).symm
  have hd := (Theory.SpecificGroups.SymplecticFour.unipotent (F := F.Carrier)).card_subgroup_dvd_card
  rw [Theory.SpecificGroups.SymplecticFour.card_unipotent,F.card_eq,← pow_mul,hc] at hd
  have hb := two_power_bound hE hd
  omega

private theorem no_g2 {E : Type*} [Group E] (hE : ExceptionalOrder E)
    (F : BinaryField) (hF : 1 < F.degree) (e : E ≃* Atlas.G2.Model F.Carrier) : False := by
  have hc := (Nat.card_congr e.toEquiv).symm
  have hd := (Atlas.G2.unipotent (K := F.Carrier)).card_subgroup_dvd_card
  rw [Atlas.G2.card_unipotent,F.card_eq,← pow_mul,hc] at hd
  have hb := two_power_bound hE hd
  omega

private theorem binary_card (n : ℕ) :
    Nat.card SL(n,ZMod 2) = ∏ i : Fin n, (2^n - 2^i.val) := by
  rw [Nat.card_congr (BinaryLinear.OuterCyclic.slEquivLinear n).toEquiv,
    ← Nat.card_congr (BinaryLinear.OuterCyclic.matrixEquivLinear n).toEquiv,
    Matrix.card_GL_field]
  simp

private theorem no_binaryLinear {E : Type*} [Group E] (hE : ExceptionalOrder E)
    {d : ℕ} (hd : d = 4 ∨ d = 5) (e : E ≃* SL(d,ZMod 2)) : False := by
  have hc := (Nat.card_congr e.toEquiv).symm
  rcases hd with rfl | rfl <;> rw [binary_card] at hc <;>
    norm_num [Fin.prod_univ_succ] at hc <;>
    rcases hE with he | he | he <;> omega

private theorem no_other_alternating {E : Type*} [Group E] (hE : ExceptionalOrder E)
    {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 8) (e : E ≃* alternatingGroup (Fin n)) : False := by
  have hc := (Nat.card_congr e.toEquiv).symm
  rcases hn with rfl | rfl | rfl <;> rw [nat_card_alternatingGroup] at hc <;>
    norm_num [Nat.factorial] at hc <;> rcases hE with he | he | he <;> omega

private theorem no_symplecticTwo {E : Type*} [Group E] (hE : ExceptionalOrder E)
    (e : E ≃* commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))) : False := by
  have hb := Nat.card_le_card_of_injective
    (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))).subtype
    (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))).subtype_injective
  rw [Theory.SpecificGroups.SymplecticFour.Binary.card_sp_two,
    ← Nat.card_congr e.toEquiv] at hb
  rcases hE with he | he | he <;> omega

private theorem no_g2Two {E : Type*} [Group E] (hE : ExceptionalOrder E)
    (e : E ≃* commutator (Atlas.G2.Model (ZMod 2))) : False := by
  have hh := (Nat.card_congr e.toEquiv).symm
  rw [Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hh
  rcases hE with he | he | he <;> omega

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) {C J : Subgroup D}

/-- The exact B.4.2 actor table leaves A7 on the original component. -/
theorem alternatingSeven_of_irreducible_case
    (h : ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ C J)
    (hc : ExceptionalOrder C) (hz : center C = ⊥) :
    Nonempty (C ≃* alternatingGroup (Fin 7)) := by
  cases h with
  | linearTwo F _ a _ _ => exact (no_linearTwo hc F a.groupEquiv).elim
  | linearThree F _ a _ => exact (no_linearThree hc F a.groupEquiv).elim
  | symplectic F hd _ a _ => exact (no_symplectic hc F hd a.groupEquiv).elim
  | symplecticTwo a _ => exact (no_symplecticTwo hc a.subgroupEquiv).elim
  | g2 F hd _ a _ _ => exact (no_g2 hc F hd a.groupEquiv).elim
  | g2Two a _ _ => exact (no_g2Two hc a.subgroupEquiv).elim
  | symmetric n hn a _ _ =>
    rcases hn with rfl | rfl
    · exact (no_other_alternating hc (Or.inl rfl) a.subgroupEquiv).elim
    · exact ⟨a.subgroupEquiv⟩
  | alternatingSix _ a _ _ => exact (no_other_alternating hc (Or.inr (Or.inl rfl)) a.groupEquiv).elim
  | alternatingSeven _ _ e _ _ _ => exact ⟨e⟩
  | tripleSix _ a _ =>
    have hh := Nat.card_congr a.centerEquiv.toEquiv
    rw [hz,Subgroup.card_bot] at hh
    norm_num at hh
  | binaryLinear d hd _ a _ => exact (no_binaryLinear hc hd a.groupEquiv).elim
  | orthogonalSix _ _ a _ _ => exact (no_other_alternating hc (Or.inr (Or.inr rfl)) a.groupEquiv).elim
  | symmetricEight _ a _ => exact (no_other_alternating hc (Or.inr (Or.inr rfl)) a.subgroupEquiv).elim
  | exteriorFive _ _ a _ _ _ => exact (no_binaryLinear hc (Or.inr rfl) a).elim

/-- The literal moved section is irreducible modulo its fixed space, and its
actor is A7. The original field and action are never replaced by a label. -/
theorem alternatingSeven_of_source_conclusion
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ C)
    (hc : ExceptionalOrder C) (hz : center C = ⊥) :
    Nonempty (C ≃* alternatingGroup (Fin 7)) ∧
      IsIrrPlus ρ C c.sectionData.space.toSubmodule ∧
      IsIrreducible (c.sectionData.action.comp C.subtype) ∧
      (Module.finrank (ZMod 2) (c.sectionData.space.toSubmodule ⧸ c.sectionData.central.toSubmodule) = 4 ∨
       Module.finrank (ZMod 2) (c.sectionData.space.toSubmodule ⧸ c.sectionData.central.toSubmodule) = 6) := by
  cases c.clause_one with
  | irreducible hi hf hirr hs he =>
    obtain ⟨e⟩ := alternatingSeven_of_irreducible_case _ hs hc hz
    refine ⟨⟨e⟩,hi,hirr,?_⟩
    rcases ChapterB.QuasisimpleSource.SourceCompletion.AlternatingSevenActor.natural_or_four _ hs e with hn | hd
    · obtain ⟨a⟩ := hn
      right
      rw [a.linearEquiv.finrank_eq, BinaryPermutation.finrank_natural_odd (Fin 7) (by decide)]
      simp
    · exact Or.inl hd
  | doubleThree F _ a _ _ => exact (no_linearThree hc F a.groupEquiv).elim
  | naturalDual d hd _ hn =>
    obtain ⟨a⟩ := hn
    exact (no_binaryLinear hc hd a.groupEquiv).elim
  | repeatedNatural d r hd _ _ _ hn =>
    obtain ⟨a⟩ := hn
    exact (no_binaryLinear hc hd a.groupEquiv).elim

variable [Finite D] [FiniteDimensional (ZMod 2) V]

/-- Both surviving A7 constituents split from the literal component fixed space. -/
theorem source_split
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ C)
    (hc : ExceptionalOrder C) (hz : center C = ⊥) :
    IsCompl c.sectionData.space.toSubmodule (fixedSpace ρ C) := by
  cases c.clause_one with
  | irreducible hi hf hirr hs he =>
    cases hs with
    | linearTwo F _ a _ _ => exact (no_linearTwo hc F a.groupEquiv).elim
    | linearThree F _ a _ => exact (no_linearThree hc F a.groupEquiv).elim
    | symplectic F hd _ a _ => exact (no_symplectic hc F hd a.groupEquiv).elim
    | symplecticTwo a _ => exact (no_symplecticTwo hc a.subgroupEquiv).elim
    | g2 F hd _ a _ _ => exact (no_g2 hc F hd a.groupEquiv).elim
    | g2Two a _ _ => exact (no_g2Two hc a.subgroupEquiv).elim
    | symmetric n hn a _ _ =>
      exact ChapterB.QuasisimpleSource.ExtensionConsequences.symmetricOdd_isCompl
        c.sectionData hi hn a
    | alternatingSix _ a _ _ => exact (no_other_alternating hc (Or.inr (Or.inl rfl)) a.groupEquiv).elim
    | alternatingSeven hg hw e hd ho hq =>
      exact ChapterB.QuasisimpleSource.ExtensionConsequences.alternatingSeven_isCompl
        c.sectionData ⟨hi,hf,hirr,.alternatingSeven hg hw e hd ho hq,he⟩ e hd
    | tripleSix _ a _ =>
      have hh := Nat.card_congr a.centerEquiv.toEquiv
      rw [hz,Subgroup.card_bot] at hh
      norm_num at hh
    | binaryLinear d hd _ a _ => exact (no_binaryLinear hc hd a.groupEquiv).elim
    | orthogonalSix _ _ a _ _ => exact (no_other_alternating hc (Or.inr (Or.inr rfl)) a.groupEquiv).elim
    | symmetricEight _ a _ => exact (no_other_alternating hc (Or.inr (Or.inr rfl)) a.subgroupEquiv).elim
    | exteriorFive _ _ a _ _ _ => exact (no_binaryLinear hc (Or.inr rfl) a).elim
  | doubleThree F _ a _ _ => exact (no_linearThree hc F a.groupEquiv).elim
  | naturalDual d hd _ hn =>
    obtain ⟨a⟩ := hn
    exact (no_binaryLinear hc hd a.groupEquiv).elim
  | repeatedNatural d r hd _ _ _ hn =>
    obtain ⟨a⟩ := hn
    exact (no_binaryLinear hc hd a.groupEquiv).elim

/-- For the original fully moved module, the quotient coordinates are actual
coordinates on the whole space, giving irreducibility and order 16 or 64. -/
theorem fully_moved_source
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ C)
    (hc : ExceptionalOrder C) (hz : center C = ⊥) (hm : moved ρ C = ⊤) :
    Nonempty (C ≃* alternatingGroup (Fin 7)) ∧
      IsIrreducible (ρ.comp C.subtype) ∧ fixedSpace ρ C = ⊥ ∧
      (Nat.card V = 2^4 ∨ Nat.card V = 2^6) := by
  obtain ⟨he,_,hi,hd⟩ := alternatingSeven_of_source_conclusion ρ c hc hz
  have hwhole : c.sectionData.space.toSubmodule = ⊤ := c.sectionData.space_eq.trans hm
  have hfixed : fixedSpace ρ C = ⊥ := by
    have hh := (source_split ρ c hc hz).disjoint.eq_bot
    simpa only [hwhole,top_inf_eq] using hh
  let a := c.sectionData.fullComponentActionEquiv hm hfixed
  have hi' : IsIrreducible (ρ.comp C.subtype) :=
    ChapterB.QuasisimpleSource.ExtensionConsequences.irreducible_of_equiv a hi
  have hd' : Module.finrank (ZMod 2) V = 4 ∨ Module.finrank (ZMod 2) V = 6 := by
    rw [a.linearEquiv.finrank_eq]
    exact hd
  refine ⟨he,hi',hfixed,?_⟩
  rcases hd' with hd' | hd'
  · left
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hd']
  · right
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hd']

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.ExceptionalActions
