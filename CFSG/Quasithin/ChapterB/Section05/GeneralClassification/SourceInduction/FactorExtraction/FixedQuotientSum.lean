module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ModuleDecomposition
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentDescent

/-!
# Opposite-factor decomposition modulo the global fixed space

Factor extraction gives E+C_V(G₂)=V₂, so the first moved space and E need
only span V modulo C_V(G). Temporarily adjoining the globally fixed space to
both invariant subspaces permits the proved opposite-factor decomposition
lemma to apply. Their images in V/C_V(G) do not change. The final construction
therefore retains the original spaces required by the natural/doubled cases.

The actual B.5.12 consumer uses B.5.10's literal centralizer product and fixed
space. Once both source factor actions and the transported complementary
supplement are constructed, the nonexceptional configuration contradicts the
counterexample condition. Those action and transport premises remain explicit;
this module supplies the quotient decomposition and contradiction only.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.11–12,
printed p.109, and the fixed-quotient convention in B.5.6(3), p.105.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction
open QuasisimpleSource
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V)

/-- Adjoining globally fixed vectors changes no image in the fixed quotient. -/
theorem quotientImage_sup_fixed (U : Subrepresentation ρ) :
    ((fixed ρ).quotientImage (U ⊔ fixed ρ)).toSubmodule =
      ((fixed ρ).quotientImage U).toSubmodule := by
  change (U.toSubmodule ⊔ ρ.invariants).map ρ.invariants.mkQ =
    U.toSubmodule.map ρ.invariants.mkQ
  rw [Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq]

/-- Opposite-factor fixedness gives a direct decomposition when the original
subspaces span modulo the global fixed space. This is the precise spanning
condition supplied by factor extraction in B.5.12. -/
theorem quotient_images_isCompl_mod_fixed {A B : Subgroup D} (h : InternalProduct A B)
    (U W : Subrepresentation ρ)
    (hs : (U.toSubmodule ⊔ W.toSubmodule) ⊔ ρ.invariants = ⊤)
    (hU : U.toSubmodule ≤ fixedSpace ρ B)
    (hW : W.toSubmodule ≤ fixedSpace ρ A) :
    IsCompl ((fixed ρ).quotientImage U).toSubmodule
      ((fixed ρ).quotientImage W).toSubmodule := by
  have hC (H : Subgroup D) : ρ.invariants ≤ fixedSpace ρ H := fun _ hv g => hv g
  have hsum : (U ⊔ fixed ρ).toSubmodule ⊔ (W ⊔ fixed ρ).toSubmodule = ⊤ := by
    change (U.toSubmodule ⊔ ρ.invariants) ⊔ (W.toSubmodule ⊔ ρ.invariants) = ⊤
    simpa only [sup_assoc, sup_left_comm, sup_comm, sup_idem] using hs
  have hc := quotient_images_isCompl ρ h (U ⊔ fixed ρ) (W ⊔ fixed ρ)
    hsum (sup_le hU (hC B)) (sup_le hW (hC A))
  simpa only [quotientImage_sup_fixed] using hc

/-- The fixed-quotient version of `SourceTwoFactorCase.of_cross_fixed`.
The original natural and doubled spaces remain their actual moved spaces;
only the decomposition proof adjoins fixed vectors temporarily. -/
noncomputable def SourceTwoFactorCase.of_cross_fixed_mod_fixed {A B : Subgroup D}
    (h : InternalProduct A B) (U W : Subrepresentation ρ)
    (hs : (U.toSubmodule ⊔ W.toSubmodule) ⊔ ρ.invariants = ⊤)
    (hU : U.toSubmodule ≤ fixedSpace ρ B)
    (hW : W.toSubmodule ≤ fixedSpace ρ A)
    (ha : SourceFactorCase ρ A U) (hb : SourceFactorCase ρ B W) : SourceTwoFactorCase ρ where
  first := A
  second := B
  product := h
  firstSpace := U
  secondSpace := W
  decomposition := quotient_images_isCompl_mod_fixed ρ h U W hs hU hW
  firstCase := ha
  secondCase := hb

namespace ComponentReduction
/-- B.5.12's final contradiction after the two literal factor cases have
been constructed. The complementary extraction supplies its supplement
inside V₂, and this proof constructs the quotient direct sum. -/
theorem Conclusion.exceptional_of_factor_cases (c : Conclusion ρ)
    (hnot : ¬ AdequateAlternative ρ)
    (U : Subrepresentation ρ)
    (hU : U.toSubmodule ⊔ ρ.invariants = c.productConfiguration.fixed.toSubmodule)
    (ha : SourceFactorCase ρ c.first c.sectionData.space)
    (hb : SourceFactorCase ρ (centralizer (c.first : Set D)) U) :
    IsExceptional ρ c.first c.sectionData.space := by
  rcases c.productConfiguration.configuration with hs | he
  · exfalso
    apply hnot
    apply Or.inr
    apply NontrivialAdequateAlternative.twoFactors
    apply SourceTwoFactorCase.of_cross_fixed_mod_fixed ρ c.productConfiguration.product
      c.sectionData.space U
    · rw [sup_assoc, hU]
      exact hs
    · rw [c.productConfiguration.centralizer_eq]
      exact le_fixedSpace_subspaceKernel ρ c.sectionData.space.toSubmodule ⊤
    · exact le_trans (le_sup_left.trans hU.le) c.productConfiguration.fixed_eq.le
    · exact ha
    · exact hb
  · exact he
end ComponentReduction
end CFSG.Quasithin.ChapterB.SourceInduction
