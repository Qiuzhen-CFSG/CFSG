module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.UpperCore
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.ModelBounds
public import CFSG.Quasithin.Chapter13.Section03.SourceComponentRigidity
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.QuasisimpleContaining
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.QuotientShape

/-!
# The actual upper quotient is A₆ or A₇

The full proved A.3.6 model theorem applies to the literal component image
in IT/O₂(IT). The intrinsic quotient I/O₂(I) is identified with that image
by the existing radical-local equivalence. Transporting the proved order,
linear-action and Sylow bounds through this exact equivalence leaves A₆
or A₇ by the complete model catalogue.

For the original normal A₆ branch, maximal-upper selection and the existing
A₆ local rigidity theorem therefore give either maximality of the original
L or a proper upper component with A₇ quotient. No model predicate or
classification callback is an extra hypothesis. The remaining A₇ exclusion
is separate. Source: Aschbacher–Smith A.3.6 and 13.3.2, pp.43–44,884–885.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.UpperModels
open Section08.SourceCompletion Chapter1 Chapter1.Section02 Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
  (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH)
include d h e hseed hn hU

/-- The literal upper quotient, classified using its actual A.3.6 source image. -/
theorem upper_quotient_six_or_seven {I : Subgroup G}
    (hI : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T I)
    (hLI : D.L ≤ I) :
    IsAlternating (I ⧸ pCore 2 I) 6 ∨ IsAlternating (I ⧸ pCore 2 I) 7 := by
  let J := I ⊔ (D.T : Subgroup G)
  let P := radicalLocalImage (D.T : Subgroup G) I
  let eqv : (I ⧸ pCore 2 I) ≃* P := radicalLocalQuotientEquiv hI.maximal_faithful.1.1
  let : IsQuasisimple (I ⧸ pCore 2 I) := hI.quasisimple
  let : IsQuasisimple P := IsQuasisimple.of_mulEquiv eqv
  let := pCore_isNilpotent (p := 2) (G := J)
  have hp : P.IsCComponent := hI.maximal_faithful.1.1.1.map_quotient (pCore 2 J)
  have hs := uniqueness_local_quotient_sqtk hI.simpleQTKE hI.maximal_faithful.1.1.2.2
  have hm := ChapterA.Section03.SourceEmbeddings.quasisimple_containing_component_models_knownSimple
    hs (pCore_quotient_pCore_eq_bot 2) hp
  have hcard : Nat.card (I ⧸ pCore 2 I) = Nat.card P := Nat.card_congr eqv.toEquiv
  have h360 : 360 ∣ Nat.card P := hcard ▸ UpperCore.six_dvd_upper_quotient e hLI
  have hGL : Nat.card P ∣ 9999360 := hcard ▸
    UpperCore.upper_quotient_card_dvd d h e hseed hn hU hI hLI
  have hSyl (S : Sylow 2 P) : Nat.card S ≤ 32 := by
    let R := S.mapSurjective (f := eqv.symm.toMonoidHom) eqv.symm.surjective
    have hb := UpperCore.upper_quotient_sylow_card_le d h e hseed hn hU hI hLI R
    have hc : Nat.card R = Nat.card S := card_map_of_injective eqv.symm.injective
    exact hc ▸ hb
  have hmodels : TheoremCModel P ∨ ThreeCoverModel P := hm.imp And.right And.right
  rcases ModelBounds.theoremC_or_threeCover h360 hGL hSyl hmodels with ha | ha
  · exact .inl (Nonempty.map (fun a => eqv.trans a) ha)
  · exact .inr (Nonempty.map (fun a => eqv.trans a) ha)

/-- The original source setup has only the proper A₇ upper-component branch left. -/
theorem original_maximal_or_seven_overgroup :
    D.L ∈ Chapter1.LStar G (D.T : Subgroup G) ∨
      ∃ I : Subgroup G, D.L < I ∧
        Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T I ∧
        (D.T : Subgroup G) ≤ normalizer (I : Set G) ∧
        IsAlternating (I ⧸ pCore 2 I) 7 := by
  obtain ⟨I,hLI,hI,hTI⟩ :=
    SixMaximality.NaturalSetup.exists_maximal_quasisimple_overgroup d e
  by_cases he : D.L = I
  · exact .inl (he.symm ▸ hI.maximal_faithful.1)
  have hL := ((Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff D.T D.L).mp
    d.counterexample.local_component).1
  rcases upper_quotient_six_or_seven d h e hseed hn hU hI hLI with h6 | h7
  · exact (he (Noncentrality.SupercriticalSource.local_eq_of_midSize
      hI.maximal_faithful.1.1 hL hLI (.inr (.inr (.inl h6))))).elim
  · exact .inr ⟨I,lt_of_le_of_ne hLI he,hI,hTI,h7⟩

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.UpperModels
