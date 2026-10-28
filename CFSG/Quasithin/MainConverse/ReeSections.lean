module

public import CFSG.Quasithin.MainConverse.ReeSections.Reduction
public import Theory.SpecificGroups.Tits.FiniteSimple

/-!
# Proper-K assembly for the Ree family: remaining structural inputs

These theorems connect the subfield induction to condition K in
Aschbacher--Smith, Theorem 0.1.2(1), printed pp.4 and 482. The input group
is identified with the genuine exceptional fixed-point carrier by an
actual multiplicative equivalence. The full catalogue inclusion is tested
only on finite simple sections.

The Tits adapter uses the independently certified simplicity of Parrott's
carrier; no such certification is requested for every smaller Ree group.
The final theorem is explicitly conditional on the Ree subgroup geometry,
the full ²F₄(2) derived comparison, and the remaining family section results.
This module does not claim to have discharged these inputs or to have
completed the Ree converse.
-/

public section

namespace CFSG.Quasithin.MainConverse.ReeSections

open CFSG.KnownSimple

/-- The Tits task's maximal-section output suffices also for sections of the
whole Tits group, since the latter is already a certified simple carrier. -/
theorem tits_isKGroup_of_maximal_sections
    (h : ExceptionalSections.NonabelianMaximalSections.{0, 0} Tits.ParrottGroup) :
    IsKGroup ExceptionalSections.IsSectionCarrier Tits.ParrottGroup := by
  have hp : HasProperKSubgroups ExceptionalSections.IsSectionCarrier Tits.ParrottGroup :=
    ExceptionalSections.properK_of_maximal_sections (fun _ _ _ _ h => h)
      (MulEquiv.refl _) h
  intro S _ hs U f hf
  let := hs
  by_cases hU : U = ⊤
  · subst U
    let a : (⊤ : Subgroup Tits.ParrottGroup) ≃* Tits.ParrottGroup := Subgroup.topEquiv
    exact ExceptionalSections.IsSectionCarrier.of_surjective
      (.constructed (.smallDerived (.tits ⟨MulEquiv.refl _⟩)))
      (f.comp a.symm.toMonoidHom) (hf.comp a.symm.surjective)
  · let a : (⊤ : Subgroup U) ≃* U := Subgroup.topEquiv
    exact hp U hU S hs ⊤ (f.comp a.toMonoidHom) (hf.comp a.surjective)

/-- Conditional proper-K assembly. The catalogue inclusion is the only premise
intended to remain after the intrinsic and independent-family inputs are proved. -/
theorem ree_properK_of_inputs
    {G : Type*} [Group G] {K : GroupClass}
    (hK : ∀ (S : Type _) [Group S] [Finite S] [IsSimpleGroup S],
      IsSectionCarrier S → K S)
    (hcover : MaximalSubgroupCover)
    (hcore : ∀ m, 1 ≤ m → ∃ P : Subgroup (ReeF4.Model m),
      IsCoatom P ∧ P.normalCore = ⊥)
    (hzero : Nonempty (commutator (ReeF4.Model 0) ≃* Tits.ParrottGroup))
    (hU : ∀ m, 1 ≤ m → ∀ (L : Type) [Group L],
      ClassicalGroup.IsPSU L 3 (2 ^ (2 * m + 1)) → IsKGroup IsConstructedCarrier L)
    (hSp : ∀ m, 1 ≤ m → ∀ (L : Type) [Group L],
      ClassicalGroup.IsPSp L 2 (2 ^ (2 * m + 1)) → IsKGroup IsConstructedCarrier L)
    (hT : ExceptionalSections.NonabelianMaximalSections.{0, 0} Tits.ParrottGroup)
    {m : ℕ} (_hm : 1 ≤ m) (e : G ≃* ReeF4.Model m) : HasProperKSubgroups K G := by
  let : Finite G := Finite.of_injective e e.injective
  have hmodel := model_isKGroup_of_inputs hcover hcore hzero hU hSp
    (tits_isKGroup_of_maximal_sections hT) m
  have hG := section_isKGroup_of_injective hmodel e.toMonoidHom e.injective
  apply IsKGroup.properK
  intro S _ hs U f hf
  let := hs
  let : Finite S := Finite.of_surjective f hf
  exact hK S (hG S hs U f hf)

end CFSG.Quasithin.MainConverse.ReeSections
