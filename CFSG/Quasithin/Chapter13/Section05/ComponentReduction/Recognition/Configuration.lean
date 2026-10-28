module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration.Prefix
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration.SourceDefs
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Action

/-!
# The marked quotient configuration in 13.5.21

This is the source-faithful boundary immediately before B.4.2 and B.4.5.
`Prefix` proves the literal quotient carriers, the selected-component
normalization, both Sylow assertions, the simple marked component, the
Fitting equality, and condition (i) together with the nontrivial and local
parts of (ii). `SourceDefs` records the exact remaining F.9.5 statements:
O₂,₃ containment, the rank-two moved seed, and the S₃ two-conjugate clause.
The final structure keeps those earlier source implications explicit for the
assembly owner.

The module action is the actual `Action.starRepresentation` on
`Additive(U_H/V₁)` and its actual `Action.seedSpace`; no abstract replacement
of the F.9 quotient is introduced.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Lemma
13.5.21, printed pp.923–924 (PDF pp.940–941).
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration
open Section08.Source
open ComponentReduction
open ComponentReduction.Recognition

variable {G : Type*} [Group G] [Finite G]
variable {D : ChapterF.Section09.Setup G} {K : Subgroup G}

section

variable (s : Selected D K) (h : D.Hypothesis)
variable [(componentCentralizer s h).Normal]

/-- The complete pre-B.4 configuration, parameterized only by the remaining
source applications (ii), (iii), and (iv). -/
structure SourceConfiguration (s : Selected D K) (h : D.Hypothesis)
    (Y : Subgroup G) (hY : Y ≤ D.L₁)
    [(componentCentralizer s h).Normal] : Prop where
  proved_prefix : Prefix s h Y
  condition_ii_O23 : LocalCoreCondition s h
  condition_iii : ModuleConditions D h
  condition_iv : PairCondition s h
  action :
    letI := Action.point_normal D h
    letI := Action.quotient_elementary D h
    ∃ ρ : Representation (ZMod 2) (Hstar D.H) (Action.Space D),
      Function.Injective ρ ∧
      (∀ (x : D.H) (u : D.UH),
        ρ (QuotientGroup.mk' (pCore 2 D.H) x)
          (Additive.ofMul (QuotientGroup.mk' (D.V₁.subgroupOf D.UH) u)) =
        Additive.ofMul (QuotientGroup.mk' (D.V₁.subgroupOf D.UH)
          ⟨x.val * u.val * x.val⁻¹,
            le_normalizer_iff.mp (le_normalizer_conjugateSpanBy D.Vplus D.H)
              x.val x.property u.val u.property⟩)) ∧
      ∀ W : Subrepresentation ρ,
        Action.seedSpace D ≤ W.toSubmodule → W = ⊤

/-- Assemble the proved prefix with the literal remaining F.9.5 conditions. -/
theorem SourceConfiguration.of_prefix
    (Y : Subgroup G) (hY : Y ≤ D.L₁)
    (p : Prefix s h Y)
    (hO23 : LocalCoreCondition s h)
    (hiii : ModuleConditions D h)
    (hiv : PairCondition s h) :
    SourceConfiguration s h Y hY := by
  exact ⟨p, hO23, hiii, hiv, Action.exists_source_action D h⟩

/-- The source condition (i), in the exact form used by the recognition
argument: V̂ has order two, lies in the marked Sylow image, and centralizes it.
The nonidentity element of a finite subgroup of order two is an involution. -/
theorem SourceConfiguration.condition_i
    (Y : Subgroup G) (hY : Y ≤ D.L₁)
    (c : SourceConfiguration s h Y hY) :
    Nat.card (Vhat s h) = 2 ∧
      Vhat s h ≤ That s h ∧
      Vhat s h ≤ centralizer (That s h : Set (Xhat s h)) :=
  ⟨c.proved_prefix.actor_card, c.proved_prefix.actor_le_sylow,
    c.proved_prefix.actor_central⟩

end
end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration
end
