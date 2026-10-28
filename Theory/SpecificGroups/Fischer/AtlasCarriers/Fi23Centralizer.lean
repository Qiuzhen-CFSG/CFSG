module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.FixedPointSetup
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22

/-!
# The fixed-point route to the Fi23 involution centralizer

In the exact ATLAS generators put `w = (a*b^2)*(a*b^2)*(a*b)^3` and
`t = w^7`. The proposed quotient is the action of the centralizer of `t`
on the fixed points of `t`, followed by an identification of its image
with the exact degree-3510 Fi22 carrier. The pointwise stabilizer must
be proved to consist of `1` and `t`; thus the construction retains the
central double cover rather than assuming an embedded Fi22.

The definitions and conditional assembly below do not yet establish the
concrete order, image identification, or pointwise stabilizer bound.
These are the three explicit mathematical premises of the assembly.

Source: GLS, volume 3, Table 5.3u and the explanatory Fischer paragraph
in `refs/KGroup/GLS3/Chapter5(sec3-).tex`, line 1042. That paragraph states
`2Fi22` and corrects the table's transcription `2Fi12`. The application
is Aschbacher--Smith A.2.19, printed pp. 40–41.
-/

@[expose] public section

namespace Sporadic.Fischer.Fi23.CentralizerSection

open Theory.GroupAction

/-- A concrete fixed-point rigidity theorem will identify the double-cover kernel. -/
theorem fixedPointAction_ker_eq_zpowers
    (hr : ∀ g : numerator,
      (∀ x : Fin 31671, inclusion candidate x = x → inclusion g.val x = x) →
      g.val = 1 ∨ g.val = candidate) :
    fixedPointAction.ker =
      Subgroup.zpowers (CentralizerFixedPointSection.marked candidate) :=
  CentralizerFixedPointSection.ker_eq_zpowers inclusion candidate hr

/-- Conditional assembly from an actual restriction-image isomorphism and a
pointwise-stabilizer bound. The concrete premises remain to be constructed. -/
theorem exists_section_of_fixedPointAction
    (ht : orderOf candidate = 2)
    (e : fixedPointAction.range ≃* Fi22.Carrier)
    (hr : ∀ g : numerator,
      (∀ x : Fin 31671, inclusion candidate x = x → inclusion g.val x = x) →
      g.val = 1 ∨ g.val = candidate) :
    ∃ (t : Carrier) (L : Subgroup Carrier) (f : L →* Fi22.Carrier),
      orderOf t = 2 ∧ L ≤ Subgroup.centralizer ({t} : Set Carrier) ∧
      Function.Surjective f ∧ IsPGroup 2 f.ker := by
  exact ⟨candidate, numerator,
    CentralizerFixedPointSection.quotientMap inclusion candidate e, ht, le_rfl,
    CentralizerFixedPointSection.quotientMap_surjective inclusion candidate e,
    CentralizerFixedPointSection.quotientMap_ker_isPGroup inclusion candidate ht hr e⟩

end Sporadic.Fischer.Fi23.CentralizerSection
