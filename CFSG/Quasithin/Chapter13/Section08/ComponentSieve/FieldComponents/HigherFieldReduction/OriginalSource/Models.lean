module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SourceList
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.Assembly
public import Theory.SpecificGroups.PSL3.OuterSolvable.Coverage
public import Theory.SpecificGroups.SU3.EvenSemilinear.SpecialCoverage
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.FullGroup
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.AutomorphismDescription
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.SemilinearCoverage

/-!
# Concrete models for the original higher-field Borel argument

Every higher-field row of the 13.8.17 catalogue supplies the automorphism
coverage consumed by the Borel calculation. The field order gives the
characteristic; the proved inner-field and graph-field descriptions then
supply the seven torus model witnesses. Special and projective unitary groups
retain their actual Hermitian form and fixed-field parameter. The symplectic
and G₂ derived carriers are identified with the full group only for n > 1.

These are intrinsic model inputs to the original field-sieve application,
not a higher-field exclusion. Source: Aschbacher–Smith, 13.8.20, printed
p.954, and the automorphism descriptions of GLS3, Theorem 2.5.12 and §2.7.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
open TorusModels.Assembly Chapter1.Section02.LocalModels Components.Models
open HermitianForm.OddPrimeSylow.NormalizedOuter
universe u

private theorem linear_two_coverage {F : Type} [Field F] [Finite F] [CharP F 2]
    (a : MulAut PSL(2,F)) :
    ∃ (g : PSL(2,F)) (σ : F ≃+* F), a = MulAut.conj g * Atlas.fieldEquivPSL 2 σ := by
  obtain ⟨g,σ,hg⟩ := BenderSuzuki.ZD.Linear.semilinear_coverage a
  have he : BenderSuzuki.ZD.Linear.fieldAut σ = Atlas.fieldEquivPSL 2 σ := by
    ext x
    obtain ⟨y,rfl⟩ := BenderSuzuki.Converse.pi_surjective x
    rw [BenderSuzuki.ZD.Linear.fieldAut_apply_pi]
    change _ = Atlas.fieldEquivPSL 2 σ (QuotientGroup.mk' _ y)
    rw [Atlas.fieldEquivPSL_mk]
    rfl
  exact ⟨g,σ,he ▸ hg⟩

private theorem field_card_gt_two {F : Type} [Field F] [Finite F]
    {n : ℕ} (hn : 1 < n) (hc : Nat.card F = 2^n) : 2 < Nat.card F := by
  rw [hc]
  exact (by simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) hn)

/-- All seven catalogue rows supply the actual automorphism-marked torus model. -/
theorem torus_model_of_higher_field {A : Type u} [Group A]
    (h : HigherFieldAlternative A) :
    ∃ n : ℕ, 1 < n ∧ ∃ unitary four : Bool, Model.{u,0} A n unitary four := by
  obtain ⟨n,hn,h⟩ := h
  refine ⟨n,hn,?_⟩
  rcases h with h | ⟨unitary,h | h⟩ | h | h
  · obtain ⟨F,hF,hfin,hc,⟨e⟩⟩ := h
    let := hF
    let := hfin
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hc)
    exact ⟨false,true,.linearTwo F hc e linear_two_coverage⟩
  · cases unitary with
    | false =>
      obtain ⟨F,hF,hfin,hc,⟨e⟩⟩ := h
      let := hF
      let := hfin
      let : Fintype F := Fintype.ofFinite F
      let : CharP F 2 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hc)
      exact ⟨false,true,.projectiveLinearThree F hc e
        (Matrix.PSL3.OuterSolvable.standard_eq_top_of_two_power_card F (by omega) hc)⟩
    | true =>
      obtain ⟨F,hF,hfin,J,hc,hconj,⟨e⟩⟩ := h
      let := hF
      let := hfin
      let J' := FormTransport.standardForm J
      have hf : Nat.card {x : F // J'.conj x = x} = 2^n :=
        FiniteField.card_fixed_of_quadratic_frobenius J'.conj 2 n (by omega) hc hconj
      let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J') :=
        BenderSuzuki.External.huppert_II_10_13 J' (2^n)
          (by simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) hn) hc hf
      exact ⟨true,false,.projectiveUnitaryThree F J hc hconj e
        (HermitianForm.EvenSemilinear.semilinear_coverage J' rfl (by omega) hc hconj)⟩
  · cases unitary with
    | false =>
      obtain ⟨F,hF,hfin,hc,⟨e⟩⟩ := h
      let := hF
      let := hfin
      let : Fintype F := Fintype.ofFinite F
      let : CharP F 2 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hc)
      exact ⟨false,true,.specialLinearThree F hc e
        (Matrix.PSL3.OuterSolvable.standard_eq_top_of_two_power_card F (by omega) hc)⟩
    | true =>
      obtain ⟨F,hF,hfin,J,hc,hconj,⟨e⟩⟩ := h
      let := hF
      let := hfin
      exact ⟨true,false,.specialUnitaryThree F J hc hconj e
        (HermitianForm.EvenSemilinear.special_semilinear_coverage
          (FormTransport.standardForm J) rfl (by omega) hc hconj)⟩
  · obtain ⟨F,hF,hfin,hc,⟨e⟩⟩ := h
    let := hF
    let := hfin
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hc)
    exact ⟨false,false,.symplecticFour F hc
      (e.trans (Theory.SpecificGroups.SymplecticFour.derivedEquivFull_of_card_gt_two
        (field_card_gt_two hn hc)))
      Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.inner_field_of_preservesDiagram⟩
  · obtain ⟨F,hF,hfin,hc,⟨e⟩⟩ := h
    let := hF
    let := hfin
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hc)
    exact ⟨false,false,.g2 F hc (e.trans (Atlas.G2.DerivedEvenOrder.derivedEquivModel hn hc))
      (Atlas.G2.LieAutomorphismExtensions.semilinearAction_bijective (field_card_gt_two hn hc)).2⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
