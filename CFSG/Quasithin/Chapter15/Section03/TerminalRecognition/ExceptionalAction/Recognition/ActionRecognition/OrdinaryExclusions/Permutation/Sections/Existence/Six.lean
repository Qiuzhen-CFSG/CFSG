module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.Permutation.Sections.Existence.SixDimension
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.Permutation.Sections.Existence.AlternatingActor
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.Permutation.Groups
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.G2.Seed
import Theory.GroupTheory.SylowKernelCore

/-!
# Natural sections for the terminal S₆ quotient

In the alternating-offender case B.5.1 gives a faithful central section of
dimension four. The source seed injects into this section and is fixed by
the marked local two-core. Since that core has order four, faithfulness
contradicts the equality of the seed and section dimensions. This excludes
the alternating image without extending its action across an odd coset or
identifying symplectic coordinates with deleted-permutation coordinates.

The remaining full symmetric offender image uses B.5.1's actual natural
coordinates. The construction retains the entire moved space and central
kernel; no splitting of the original module is required.

Source: Aschbacher–Smith, B.5.1 and B.5.6, printed pp.99 and 105, and
the final proof of 15.3.1, p.1155 (combined manuscript, 1 March 2004).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.Permutation

variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
  [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

/-- The actual local core remains a nontrivial four-group in the offender actor. -/
theorem firstCore_card_six (e : coreQuotient H ≃* Equiv.Perm (Fin 6)) :
    Nat.card d.firstCoreInOffender = 4 := by
  have hc := (six_residual_pair d e).2.2.1
  have hm : ((d.YF.map coreProjection).pCoreIn 2).map e.toMonoidHom =
      (d.YF.map (e.toMonoidHom.comp coreProjection)).pCoreIn 2 := by
    rw [map_pCoreIn_of_injective 2 _ _ e.injective, Subgroup.map_map]
  rw [← hm, ← d.firstCoreInOffender_map] at hc
  exact (Nat.card_congr ((equivMapOfInjective d.firstCoreInOffender
    d.offenderGroup.subtype d.offenderGroup.subtype_injective).trans
      (e.subgroupMap _)).toEquiv).trans hc


private theorem fixed_section_lower_bound
    (c : QuasisimpleSourceConclusion d.offenderAction (generalizedFitting d.offenderGroup))
    (ht : generalizedFitting d.offenderGroup = ⊤) :
    4 ≤ Module.finrank (ZMod 2) (fixedSpace c.sectionData.action d.firstCoreInOffender) := by
  apply G2.section_firstCore_fixed_finrank_ge_four d c.sectionData.space c.sectionData.central
  · rw [c.sectionData.space_eq, ht, d.offenderAction_moved_eq_top]
    exact le_top
  · rw [c.sectionData.central_eq]
    intro v hv g
    exact hv ⟨g, ht ▸ mem_top _⟩

/-- A four-dimensional faithful section cannot be fixed by the marked four-group.
The seed survives the complete central kernel, including nonsplit extensions. -/
theorem not_alternating_offender_six
    (e : coreQuotient H ≃* Equiv.Perm (Fin 6))
    (hN : d.offenderGroup.map e.toMonoidHom = alternatingGroup (Fin 6))
    (h : SourceAlternative d.offenderAction) : False := by
  let eN := (e.subgroupMap d.offenderGroup).trans (MulEquiv.subgroupCongr hN)
  obtain ⟨c, ht⟩ := source_of_alternating_offender d (Or.inl rfl) eN h
  have hc : Nat.card (generalizedFitting d.offenderGroup) = 360 := by
    rw [ht, Nat.card_congr topEquiv.toEquiv, Nat.card_congr eN.toEquiv,
      nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  obtain ⟨hf, hd⟩ := SixDimension.section_faithful_dimension d.offenderAction hc c.clause_one
  have hfix : fixedSpace c.sectionData.action d.firstCoreInOffender = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    exact le_antisymm (Submodule.finrank_le _) (hd ▸ fixed_section_lower_bound d c ht)
  have hbot : d.firstCoreInOffender = ⊥ := by
    apply le_bot_iff.mp
    intro a ha
    apply hf
    apply LinearMap.ext
    intro v
    have hv := (show v ∈ fixedSpace c.sectionData.action d.firstCoreInOffender by
      rw [hfix]; exact Submodule.mem_top) ⟨a, ha⟩
    simpa using hv
  have hc4 := firstCore_card_six d e
  rw [hbot, Subgroup.card_bot] at hc4
  omega

/-- The complete source alternative constructs the natural moved central
section for the actual terminal S₆ quotient. -/
theorem naturalSection_six (e : coreQuotient H ≃* Equiv.Perm (Fin 6))
    (h : SourceAlternative d.offenderAction) : Nonempty (NaturalSection d 6) := by
  rcases offender_image_cases d (by decide) e with hN | hN
  · exact (not_alternating_offender_six d e hN h).elim
  · have ht : d.offenderGroup = ⊤ := (Subgroup.map_injective e.injective)
      (hN.trans (Subgroup.map_top_of_surjective _ e.surjective).symm)
    exact naturalSection_of_full_offender d (Or.inl rfl) e ht h
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.Permutation
