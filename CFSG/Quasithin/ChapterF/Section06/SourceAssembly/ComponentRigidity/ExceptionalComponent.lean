module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentRigidity.OppositeExceptional
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentExclusions.Janko
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentExclusions.PSL28

/-!
# The exceptional-vertex component branch after its two model exclusions

For the component selected from the original source quotient, failure of
characteristic two at either vertex forces the contained residual to be
cubic. Its opposite core, and hence an actual Sylow subgroup of the simple
central quotient, is elementary of order at most eight. The original
residual and Sylow intersection exclude the J1 and PSL2(8) alternatives.

The remaining elementary-Sylow simple-group sieve is the independent
Theorem B/C source input. No model recognition is assumed here.
Source: Aschbacher--Smith F.6.17, printed p.309.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
variable {G₁ G₂ : Subgroup G}

/-- All constructed component data before the odd-PSL2 sieve, with the
same original component and literal quotient retained. -/
theorem SingleResidualComponent.exceptional_component_data
    (d : SingleResidualComponent G₁ G₂)
    (e : G ≃* (H ⧸ pPrimeCore 3 H))
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hbad : generalizedFitting G₁ ≠ pCore 2 G₁ ∨ generalizedFitting G₂ ≠ pCore 2 G₂) :
    Nat.card ((pResidual 2 G₁).map G₁.subtype) = 3 ∧
      IsElementaryAbelian 2 ((pCore 2 G₂).map G₂.subtype) ∧
      primeRank 2 ((pCore 2 G₂).map G₂.subtype) ≤ 3 ∧
      IsSimpleGroup (d.component ⧸ center d.component) ∧
      (∃ S : Sylow 2 (d.component ⧸ center d.component),
        IsElementaryAbelian 2 S ∧ Nat.card S ≤ 8) ∧
      ¬ Nonempty ((d.component ⧸ center d.component) ≃* Janko1.Model) ∧
      ¬ ClassicalGroup.IsPSL (d.component ⧸ center d.component) 2 8 := by
  let : d.component.Normal := d.normal
  have hc := left_residual_cubic_of_either_not_characteristic_two h hcore d.component
    d.left_contains d.right_escapes hbad
  obtain ⟨_, he, hr, hs, hS⟩ := d.small_sylow_of_either_exceptional h hcore hbad
  exact ⟨hc, he, hr, hs, hS,
    central_quotient_not_janko_one_of_left_residual_cubic e h d.isComponent d.left_contains hc,
    central_quotient_not_psl_eight_model_of_left_residual_cubic h d.isComponent d.left_contains hc⟩

end CFSG.Quasithin.ChapterF.SourceAssembly
