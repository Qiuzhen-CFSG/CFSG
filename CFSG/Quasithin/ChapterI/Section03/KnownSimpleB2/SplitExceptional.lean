module

public import CFSG.KnownSimple.CarrierCatalogue
public import Theory.SpecificGroups.G2.InvolutoryTwoComponents

/-!
# Split exceptional catalogue cases: structural assembly

These reductions use the literal octonion G₂ carrier and the root-generated
central quotients F₄/E₆/E₇/E₈ in the full known-simple catalogue. Simplicity
is transported from the given simple group. Every involution, its actual
fixed subgroup and its intrinsic two-components are transported along the
catalogue's multiplicative equivalence.

The fixed-group alternatives remain explicit model premises. Consequently
these are conditional assembly results, not completed exceptional-family
B₂ theorems. The source calculations must establish the alternatives for
inner and outer automorphisms, including every allowed small field.

Sources: GLS II Definition 2.4 and Lemma 5.28; GLS III §§3.1, 4.2, 4.5,
4.9. The model conventions are in CFSG.KnownSimple.CarrierCatalogue and
CFSG.KnownSimple.ExceptionalModels.
-/

public section

open Theory.GroupTheory

namespace CFSG.Quasithin.ChapterI.Section03.KnownSimpleB2
variable {S : Type*} [Group S] [IsSimpleGroup S]

/-- Structural assembly on the actual G₂ carrier, retaining q > 2. -/
theorem of_g2_of_fixedGroupLayerAlternative
    (hS : KnownSimple.IsG2Carrier S)
    (hfixed : ∀ (F : Type) [Field F] [Finite F] [IsSimpleGroup (Atlas.G2.Model F)],
      2 < Nat.card F → ∀ a : MulAut (Atlas.G2.Model F), orderOf a = 2 →
        FixedGroupLayerAlternative a.fixedSubgroup) : HasInvolutoryB2 S := by
  obtain ⟨F, hF, hfin, hq, ⟨e⟩⟩ := hS
  let : IsSimpleGroup (Atlas.G2.Model F) := e.symm.isSimpleGroup
  exact (HasInvolutoryB2.of_fixedGroupLayerAlternative (hfixed F hq)).of_mulEquiv e

/-- Structural assembly for F4, with no exclusion at q = 2 or q = 3. -/
theorem of_f4_of_fixedGroupLayerAlternative {q : ℕ}
    (hS : ExceptionalGroup.IsF4 S q)
    (hfixed : ∀ (F : Type) [Field F] [Finite F] [IsSimpleGroup (ExceptionalSplit.F4 F)],
      Nat.card F = q → ∀ a : MulAut (ExceptionalSplit.F4 F), orderOf a = 2 →
        FixedGroupLayerAlternative a.fixedSubgroup) : HasInvolutoryB2 S := by
  obtain ⟨F, hF, hfin, hq, ⟨e⟩⟩ := hS
  let : IsSimpleGroup (ExceptionalSplit.F4 F) := e.symm.isSimpleGroup
  exact (HasInvolutoryB2.of_fixedGroupLayerAlternative (hfixed F hq)).of_mulEquiv e

/-- Structural assembly for E6, with no exclusion at q = 2 or q = 3. -/
theorem of_e6_of_fixedGroupLayerAlternative {q : ℕ}
    (hS : ExceptionalGroup.IsE6 S q)
    (hfixed : ∀ (F : Type) [Field F] [Finite F] [IsSimpleGroup (ExceptionalSplit.E6 F)],
      Nat.card F = q → ∀ a : MulAut (ExceptionalSplit.E6 F), orderOf a = 2 →
        FixedGroupLayerAlternative a.fixedSubgroup) : HasInvolutoryB2 S := by
  obtain ⟨F, hF, hfin, hq, ⟨e⟩⟩ := hS
  let : IsSimpleGroup (ExceptionalSplit.E6 F) := e.symm.isSimpleGroup
  exact (HasInvolutoryB2.of_fixedGroupLayerAlternative (hfixed F hq)).of_mulEquiv e

/-- Structural assembly for E7, with no exclusion at q = 2 or q = 3. -/
theorem of_e7_of_fixedGroupLayerAlternative {q : ℕ}
    (hS : ExceptionalGroup.IsE7 S q)
    (hfixed : ∀ (F : Type) [Field F] [Finite F] [IsSimpleGroup (ExceptionalSplit.E7 F)],
      Nat.card F = q → ∀ a : MulAut (ExceptionalSplit.E7 F), orderOf a = 2 →
        FixedGroupLayerAlternative a.fixedSubgroup) : HasInvolutoryB2 S := by
  obtain ⟨F, hF, hfin, hq, ⟨e⟩⟩ := hS
  let : IsSimpleGroup (ExceptionalSplit.E7 F) := e.symm.isSimpleGroup
  exact (HasInvolutoryB2.of_fixedGroupLayerAlternative (hfixed F hq)).of_mulEquiv e

/-- Structural assembly for E8, with no exclusion at q = 2 or q = 3. -/
theorem of_e8_of_fixedGroupLayerAlternative {q : ℕ}
    (hS : ExceptionalGroup.IsE8 S q)
    (hfixed : ∀ (F : Type) [Field F] [Finite F] [IsSimpleGroup (ExceptionalSplit.E8 F)],
      Nat.card F = q → ∀ a : MulAut (ExceptionalSplit.E8 F), orderOf a = 2 →
        FixedGroupLayerAlternative a.fixedSubgroup) : HasInvolutoryB2 S := by
  obtain ⟨F, hF, hfin, hq, ⟨e⟩⟩ := hS
  let : IsSimpleGroup (ExceptionalSplit.E8 F) := e.symm.isSimpleGroup
  exact (HasInvolutoryB2.of_fixedGroupLayerAlternative (hfixed F hq)).of_mulEquiv e

end CFSG.Quasithin.ChapterI.Section03.KnownSimpleB2
