module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Action
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.Selection
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.Lifting
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.Sections
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.SixExtension
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.RecognitionStep
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension

/-!
# The nonsolvable closure branch of transvection recognition

The literal nonsolvable normal closure of the given transvection in H/O₂(H)
supplies a relative C-component K with K*=[K*,t]≠1. The actual order-two
line makes G₁ a two-local subgroup, giving the SQTK cover for the faithful,
two-core-free displacement action used in G.6.4. Its natural component
section is transported through K/O₂(K)≃K* to Ũ_K/C_{Ũ_K}(K).

The earlier 13.7.6 then gives the linear or alternating alternatives.
The full-module extension constructs the natural or augmentation module,
with equivariance for the same H* identification. The result retains H=KT,
the actual S₆/S₇/L₄(2) actor, the A₆ or concrete hexacode triple-cover
quotient of L, and the two noncentral L₁-chief factors on U_H/V₁.
The Sylow subgroup absorbs O₂(H) in the quotient-product lift.

`nonsolvable_closure_recognition` retains the moved-component witnesses;
`complete_conclusions_of_nonsolvable_closure` returns the three source
clauses with an intrinsic C-component of H. The genuine standing setup
constructs the quotient's normality and elementary abelianness. Only the
universal earlier G.6.4, 13.7.6 and centralizer statements remain explicit
inputs. The separate exclusion of solvable closure and final 13.8.5 assembly
belong to the parent recognition theorem.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
combined manuscript of 1 March 2004, 13.8.5, printed pp.947–948.
-/

@[expose] public section

open Subgroup Representation
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component
open RecognitionStep ModelExtension

universe u
variable {G : Type u} [Group G] [Finite G]

/-- The nonsolvable branch of 13.8.5, including the constructed moved
component and every group/module alternative. The line's order two supplies
the SQTK application witness; G.6.4 is applied to the faithful displacement
action, and its actual section discharges the hypothesis of 13.7.6.
Normality of V₁ in U_H and elementary abelianness of U_H/V₁ are derived
from the standing setup rather than imposed on this theorem. -/
theorem nonsolvable_closure_recognition
    (T : Sylow 2 G) {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (earlier : EarlierInputs T L V V₁ V₂ V₃ M G₁)
    (hG64 : G64SourceTheorem.{u} KnownSimple.IsKnownSimple)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M) :
    let := d.uh_elementary hH
    let := (V₁.subgroupOf (Source.UH H V₃)).normal_of_isMulCommutative
    ∀ (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁))),
      IsConjugation H V₃ V₁ ρ →
      ∀ (t : Source.Hstar H), IsTransvection ρ t →
      ¬ Group.IsSolvable (normalClosure ({t} : Set (Source.Hstar H))) →
      ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
        Source.starImage H K ≤ normalClosure ({t} : Set (Source.Hstar H)) ∧
        zpowers t ≤ normalizer (Source.starImage H K : Set (Source.Hstar H)) ∧
        ⁅Source.starImage H K, zpowers t⁆ = Source.starImage H K ∧
        Source.starImage H K ≠ ⊥ ∧
        (H : Set G) = (K : Set G) * (T : Set G) ∧
        FullAlternatives H L (sourceOne L T V₁) V₃ V₁
          (le_sup_left.trans hH.1.2) ρ := by
  let := d.uh_elementary hH
  let := (V₁.subgroupOf (Source.UH H V₃)).normal_of_isMulCommutative
  dsimp only
  intro ρ hρ t ht hns
  have hV₁ : V₁ ≠ ⊥ := by
    intro hb
    have hc := d.line_card
    rw [hb, Subgroup.card_bot] at hc
    omega
  have hpV₁ : IsPGroup 2 V₁ :=
    IsPGroup.of_card (n := 1) (by simpa only [pow_one] using d.line_card)
  obtain ⟨K, hKH, hK, hclosure, hnormalizes, hcomm, hne, hsection⟩ :=
    exists_component_natural_section d.counterexample.qtke hG64
      H (sourceOne L T V₁) T G₁ M V₁ V₃ V₁ hH hV₁ hpV₁ d.first_normalizer
      ρ hρ (earlier.centralizer d H hH).le t ht hns
  have hs : RecognizedSection H K V₃ V₁ hKH ρ := by
    rcases hsection with ⟨n, hn, _hn5, eK, hs⟩ | ⟨n, hn, _hn8, eK, hs⟩
    · exact Or.inl ⟨n, hn, (Components.componentStarEquiv H K hKH hK).trans eK, hs⟩
    · exact Or.inr ⟨n, hn, (Components.componentStarEquiv H K hKH hK).trans eK, hs⟩
  obtain ⟨hprod, hmodels⟩ :=
    full_alternatives_of_recognized_section T d earlier hH hKH hK ρ hρ t ht hs
  exact ⟨K, hKH, hK, hclosure, hnormalizes, hcomm, hne, hprod, hmodels⟩

/-- All three conclusions of 13.8.5 under the literal nonsolvable-closure
hypothesis. The component is intrinsic to H, and `FullAlternatives` retains
the concrete actor, local quotient, equivariant module and chief-series
conclusions. The parent proves nonsolvability and supplies the universal
earlier theorems; no component or recognized section is an input here. -/
theorem complete_conclusions_of_nonsolvable_closure
    (T : Sylow 2 G) {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (earlier : EarlierInputs T L V V₁ V₂ V₃ M G₁)
    (hG64 : G64SourceTheorem.{u} KnownSimple.IsKnownSimple)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M) :
    let := d.uh_elementary hH
    let := (V₁.subgroupOf (Source.UH H V₃)).normal_of_isMulCommutative
    ∀ (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁))),
      IsConjugation H V₃ V₁ ρ →
      ∀ (t : Source.Hstar H), IsTransvection ρ t →
      ¬ Group.IsSolvable (normalClosure ({t} : Set (Source.Hstar H))) →
      (∃ C : Subgroup H, C.IsCComponent ∧
        (H : Set G) = (C.map H.subtype : Set G) * (T : Set G)) ∧
      FullAlternatives H L (sourceOne L T V₁) V₃ V₁
        (le_sup_left.trans hH.1.2) ρ := by
  let := d.uh_elementary hH
  let := (V₁.subgroupOf (Source.UH H V₃)).normal_of_isMulCommutative
  dsimp only
  intro ρ hρ t ht hns
  obtain ⟨K, hKH, hK, _hclosure, _hnormalizes, _hcomm, _hne, hprod, hmodels⟩ :=
    nonsolvable_closure_recognition T d earlier hG64 hH ρ hρ t ht hns
  refine ⟨⟨K.subgroupOf H, hK, ?_⟩, hmodels⟩
  rwa [map_subgroupOf_eq_of_le hKH]

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component

end
