module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions.ModelRigidity.LinearModels
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.ModuleIdentifications
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.BorelReduction.LinearCases

/-!
# Comparing the exchanged E.2.2 and F.9.18 component models

Actual group isomorphisms exclude A₅ and L₃(2). For PSL₂, the order and
elementary two-rank distinguish L₃(2), and the two-part of the order recovers
the defining field. Suzuki's three-free order separates the two infinite
families; divisibility of Suzuki field degrees recovers its parameter.
Only after the field comparison do we exclude the even-exponent SL₂ row.

The local statements retain E.2.2's actual image in H/J and its Borel pair.
They do not identify that image with an arbitrary faithful section image:
the source assembly must supply the stated comparison map, preserving any
central kernels. No module classification or FF exclusion is assumed here.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), E.2.2,
pp.215--216; F.9.18(5), pp.325--326; and 15.3.65, printed p.1152.
-/

@[expose] public section
open Subgroup Matrix BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged

open FFExclusions.ModelRigidity
open BorelReduction BorelReduction.SourceCases

section Models
variable {F E : Type} [Field F] [Finite F] [Field E] [Finite E] {f n : ℕ}

/-- An actual PSL₂ isomorphism identifies its defining-field exponent. -/
theorem pslTwo_exponent_eq (hf : 0 < f) (hn : 0 < n)
    (hF : Nat.card F = 2 ^ f) (hE : Nat.card E = 2 ^ n)
    (e : PSL(2,F) ≃* PSL(2,E)) : f = n := by
  have hc := congrArg (fun c : ℕ => c.factorization 2) (Nat.card_congr e.toEquiv)
  rw [(pslTwo_invariants hf hF).2, (pslTwo_invariants hn hE).2] at hc
  exact hc

/-- L₃(2) cannot be PSL₂ over a binary field: its two-rank and two-part disagree. -/
theorem pslTwo_not_binaryThree (hf : 0 < f) (hF : Nat.card F = 2 ^ f) :
    ¬ Nonempty (PSL(2,F) ≃* PSL(3,ZMod 2)) := by
  rintro ⟨e⟩
  have hr := Theory.GroupTheory.primeRank_equiv 2 e
  have hc := congrArg (fun c : ℕ => c.factorization 2) (Nat.card_congr e.toEquiv)
  have h₂ := pslTwo_invariants hf hF
  have h₃ := pslThree_invariants (F := ZMod 2) (n := 1) (by decide) (by simp)
  rw [h₂.1, h₃.1] at hr
  rw [h₂.2, h₃.2] at hc
  omega

/-- The A₅ overlap has field exponent two, excluded by the actual odd exponent. -/
theorem pslTwo_not_alternatingFive (hf : 1 < f) (ho : Odd f)
    (hF : Nat.card F = 2 ^ f) :
    ¬ Nonempty (PSL(2,F) ≃* alternatingGroup (Fin 5)) := by
  rintro ⟨e⟩
  have h := pslTwo_componentModel hf ho hF (ComponentModel.alternatingFive e)
  cases h.1

omit [Finite F] in
/-- The order-three element separates PSL₂ from every positive Suzuki model. -/
theorem pslTwo_not_suzuki (m : ℕ) (hm : 0 < m) :
    ¬ Nonempty (PSL(2,F) ≃* SuzukiMatrixGroup m) := by
  rintro ⟨e⟩
  apply suzukiMatrixGroup_three_free m hm
  rw [← Nat.card_congr e.toEquiv]
  exact ProjectiveSpecialLinearGroup.three_dvd_card F 2 (by decide)

/-- The positive Suzuki parameter is intrinsic to the actual group. -/
theorem suzuki_parameter_eq {k m : ℕ} (hk : 0 < k) (hm : 0 < m)
    (e : SuzukiMatrixGroup k ≃* SuzukiMatrixGroup m) : k = m := by
  have hc := Nat.card_congr e.toEquiv
  have hkm := suzukiMatrixGroup_degree_dvd_of_card_dvd hk hm (dvd_of_eq hc)
  have hmk := suzukiMatrixGroup_degree_dvd_of_card_dvd hm hk (dvd_of_eq hc.symm)
  have he := Nat.dvd_antisymm hkm hmk
  omega

end Models

section SourceModels
variable {G : Type*} [Group G] {H M K : Subgroup G} {f : ℕ}

/-- All three L₃(2) rows of F.9.18(5) are excluded against the genuine E.2.2 model. -/
theorem source_not_binaryThree (h : ExchangedModel H M K f) :
    ¬ Nonempty (sourceImage H M K ≃* PSL(3,ZMod 2)) := by
  rintro ⟨e⟩
  rcases h with ⟨F, hfield, hfin, hchar, hf, hF, a, hB⟩ |
    ⟨m, hm, he, a, hB⟩
  · exact pslTwo_not_binaryThree (by omega) hF ⟨a.symm.trans e⟩
  · exact not_componentModel_of_suzuki_equiv m hm a .linearThree 2
      (.linearThree (ZMod 2) (n := 1) (by decide) (by simp) e)

/-- The separate A₅ row is excluded without replacing the source component by a tag. -/
theorem source_not_alternatingFive (h : ExchangedModel H M K f)
    (hf : 1 < f) (ho : Odd f) :
    ¬ Nonempty (sourceImage H M K ≃* alternatingGroup (Fin 5)) := by
  rintro ⟨e⟩
  rcases h with ⟨F, hfield, hfin, hchar, hf', hF, a, hB⟩ |
    ⟨m, hm, he, a, hB⟩
  · exact pslTwo_not_alternatingFive hf ho hF ⟨a.symm.trans e⟩
  · exact not_componentModel_of_suzuki_equiv m hm a .alternatingFive 0
      (.alternatingFive e)

/-- A PSL₂ realization from F.9.18 has exactly the E.2.2 field cardinality.
The Suzuki source possibility is eliminated by the actual group order. -/
theorem source_linear_field_card (h : ExchangedModel H M K f)
    {E : Type} [Field E] [Finite E] {n : ℕ} (hn : 0 < n)
    (hE : Nat.card E = 2 ^ n) (e : sourceImage H M K ≃* PSL(2,E)) :
    Nat.card E = 2 ^ f := by
  rcases h with ⟨F, hfield, hfin, hchar, hf, hF, a, hB⟩ |
    ⟨m, hm, he, a, hB⟩
  · have he := pslTwo_exponent_eq (by omega) hn hF hE (a.symm.trans e)
    exact hE.trans (congrArg (fun k : ℕ => 2 ^ k) he.symm)
  · exact (pslTwo_not_suzuki (F := E) m hm ⟨e.symm.trans a⟩).elim

/-- In the Suzuki row, the source parameter agrees with the natural module's parameter. -/
theorem source_suzuki_exponent (h : ExchangedModel H M K f)
    {m : ℕ} (hm : 0 < m) (e : sourceImage H M K ≃* SuzukiMatrixGroup m) :
    f = 2 * m + 1 := by
  rcases h with ⟨F, hfield, hfin, hchar, hf, hF, a, hB⟩ |
    ⟨k, hk, he, a, hB⟩
  · exact (pslTwo_not_suzuki (F := F) m hm ⟨a.symm.trans e⟩).elim
  · exact he.trans (congrArg (fun k : ℕ => 2 * k + 1)
      (suzuki_parameter_eq hk hm (a.symm.trans e)))

/-- Exclude the even-exponent orthogonal SL₂ constituent only after identifying
its defining field with the field of the actual E.2.2 model. -/
theorem source_not_even_orthogonal (h : ExchangedModel H M K f) (ho : Odd f)
    {E : Type} [Field E] [Finite E] {n : ℕ} (hn : 0 < n)
    (hE : Nat.card E = 2 ^ (2 * n)) :
    ¬ Nonempty (sourceImage H M K ≃* PSL(2,E)) := by
  rintro ⟨e⟩
  have hfield := source_linear_field_card h (by omega : 0 < 2 * n) hE e
  exact field_card_ne_even_exponent hfield ho n hE

end SourceModels
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged
