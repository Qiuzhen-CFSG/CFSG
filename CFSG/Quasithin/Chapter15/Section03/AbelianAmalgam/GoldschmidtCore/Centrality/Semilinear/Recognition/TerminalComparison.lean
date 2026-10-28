module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.SourceQuotient
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.ComponentComparison

/-!
# The complete B.5 comparison at the terminal quotient

The actual terminal configuration supplies the SQTK cover and the nonzero
image of X_E. Apply the full universal B.5.6 input once to its genuine
restricted offender action, retain that full group-and-module conclusion,
and deduce the possible actors. Under the two F-side facts (quasisimplicity of F*(H/O₂(H)) and the small
Sylow bound), identify the actual component in each remaining actor.

This intermediate comparison preserves its independent conditional API.
`FComparison` now supplies both F-side facts from the full thirteen-row
source input, and `FinalComparison` applies the exhaustive comparison at the
actual terminal quotient before the Fano marking in `Recognition`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.1,
B.5.3/B.5.6, pp.99–105, and 15.3.68, pp.1154–1155.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
universe u v
variable {G : Type u} [Group G] [Finite G]

/-- The terminal B.5 application retains the full source conclusion on the
actual representation. Only its derived actor list is displayed alongside it. -/
theorem terminal_offender_alternatives {K : GroupClass.{u}}
    (source : GeneralClassificationInput.{u,v} K)
    (T : Sylow 2 G) (M Y V E F : Subgroup G)
    (d : OrthogonalFourBinary.NaturalAction V M)
    (c : TerminalConfiguration T M Y V E F d)
    (hH : IsSQTK K (amalgamGroup Y T E F)) (hTM : (T : Subgroup G) ≤ M)
    (hX : ¬ lineX E ≤ M)
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) W]
    (ρ : Representation (ZMod 2)
      (amalgamGroup Y T E F ⧸ pCore 2 (amalgamGroup Y T E F)) W)
    (hfaith : Function.Injective ρ)
    (hXI : ((lineX E).subgroupOf (amalgamGroup Y T E F)).map
      (QuotientGroup.mk' (pCore 2 (amalgamGroup Y T E F))) ≤ offenderSubgroup ρ)
    (hr : primeRank 3 (amalgamGroup Y T E F ⧸ pCore 2 (amalgamGroup Y T E F)) ≤ 1) :
    SourceAlternative (ρ.comp (offenderSubgroup ρ).subtype) ∧
    (Nonempty (offenderSubgroup ρ ≃* Equiv.Perm (Fin 3)) ∨
      (∃ B : BinaryField, 2 ≤ B.degree ∧ Nonempty (offenderSubgroup ρ ≃* SL(2,B.Carrier))) ∨
      (∃ B : BinaryField, Odd B.degree ∧ Nonempty (offenderSubgroup ρ ≃* SL(3,B.Carrier))) ∨
      Nonempty (offenderSubgroup ρ ≃* Equiv.Perm (Fin 5))) := by
  obtain ⟨_, _, ha, hi⟩ := terminal_classification_applicability
    T M Y V E F d c hH hTM hX ρ hfaith hXI
  have hs := source _ _ _ ha
  let : Nontrivial (offenderSubgroup ρ) := (Subgroup.nontrivial_iff_ne_bot _).mpr hi
  exact ⟨hs, source_actor_rank_one _
    ((primeRank_le_of_injective 3 (offenderSubgroup ρ).subtype Subtype.val_injective).trans hr) hs⟩

/-- The actual terminal component has this derived B-side list, once the
F-side quasisimplicity and Sylow-size facts have been discharged. The complete
source action conclusion is kept, so its module information is not discarded. -/
theorem terminal_component_alternatives {K : GroupClass.{u}}
    (source : GeneralClassificationInput.{u,v} K)
    (T : Sylow 2 G) (M Y V E F : Subgroup G)
    (d : OrthogonalFourBinary.NaturalAction V M)
    (c : TerminalConfiguration T M Y V E F d)
    (hH : IsSQTK K (amalgamGroup Y T E F)) (hTM : (T : Subgroup G) ≤ M)
    (hX : ¬ lineX E ≤ M)
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) W]
    (ρ : Representation (ZMod 2)
      (amalgamGroup Y T E F ⧸ pCore 2 (amalgamGroup Y T E F)) W)
    (hfaith : Function.Injective ρ)
    (hXI : ((lineX E).subgroupOf (amalgamGroup Y T E F)).map
      (QuotientGroup.mk' (pCore 2 (amalgamGroup Y T E F))) ≤ offenderSubgroup ρ)
    (hr : primeRank 3 (amalgamGroup Y T E F ⧸ pCore 2 (amalgamGroup Y T E F)) ≤ 1)
    (hL : IsQuasisimple (generalizedFitting
      (amalgamGroup Y T E F ⧸ pCore 2 (amalgamGroup Y T E F))))
    (S : Sylow 2 (amalgamGroup Y T E F ⧸ pCore 2 (amalgamGroup Y T E F)))
    (hS : Nat.card S ≤ 128) :
    let L := generalizedFitting (amalgamGroup Y T E F ⧸ pCore 2 (amalgamGroup Y T E F))
    SourceAlternative (ρ.comp (offenderSubgroup ρ).subtype) ∧
    ((L = offenderSubgroup ρ ∧
      ∃ B : BinaryField, 2 ≤ B.degree ∧ Nonempty (L ≃* SL(2,B.Carrier))) ∨
    (L = offenderSubgroup ρ ∧ Nonempty (L ≃* SL(3,ZMod 2))) ∨
    (Nonempty (offenderSubgroup ρ ≃* Equiv.Perm (Fin 5)) ∧
      Nonempty (L ≃* alternatingGroup (Fin 5)))) := by
  obtain ⟨_, _, ha, hi⟩ := terminal_classification_applicability
    T M Y V E F d c hH hTM hX ρ hfaith hXI
  have hs := source _ _ _ ha
  have hcore := CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.coreQuotient_twoCore
    (H := amalgamGroup Y T E F)
  exact ⟨hs, fitting_source_rank_one ρ hr hi hcore hL S hS hs⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
