module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.Reduction
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.MarkedElimination.AlternatingSevenDimension.Orders
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.GroupCore
public import Theory.Representation.HexacodeAction.OvergroupFitting
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoQuotientProducts

/-!
# The component in the terminal triple-cover branch

The supplied containment of the even cover in the actual offender image
identifies F*(N), through the literal embedding N → H/O₂(H) → Ŝ₆, with the
perfect even cover Â₆. The source supplies O₂(N)=1.

This excludes B.5.6(3) by the direct-product obstruction for a quasisimple
two-group extension. In B.5.6(4), the perfect F*(N) lies in the normal
A₆ × C₃ product because its quotient is cyclic. Projection to C₃ is trivial,
so the component would embed in A₆, contradicting their orders 1080 and 360.
Thus the split product is never identified with the nonsplit perfect cover.

The preliminary source reduction then selects the entire six-clause B.5.1
conclusion on the original offender action. The classification witness and
even-cover containment remain explicit inputs, as in this task's contract;
`ActionRecognition.even_le_offender_image` supplies the containment at assembly.
This module does not import that consumer or assume its action selection.

Source: Aschbacher–Smith, B.5.1 and B.5.6, printed pp.99 and 105, and the
final proof of 15.3.1, p.1155 (combined manuscript, 1 March 2004).
-/

public section
open Subgroup Atlas.Codes Theory.GroupTheory

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.TripleCover.GroupComparison
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open scoped IsMulCommutative
open Representation.Hexacode
variable {H : Type*} [Group H] [Finite H]
    {V : Subgroup H} [IsElementaryAbelian 2 (moduleClosure V)]

/-- The exact offender inclusion followed by the specified quotient equivalence. -/
noncomputable abbrev offenderEmbedding (d : SourceInput V) (e : coreQuotient H ≃* HexAutomorphisms) :
    d.offenderGroup →* HexAutomorphisms := e.toMonoidHom.comp d.offenderGroup.subtype

omit [Finite H] in
private theorem embedding_injective (d : SourceInput V)
    (e : coreQuotient H ≃* HexAutomorphisms) : Function.Injective (offenderEmbedding d e) :=
  e.injective.comp d.offenderGroup.subtype_injective

omit [Finite H] in
private theorem even_le_range (d : SourceInput V)
    (e : coreQuotient H ≃* HexAutomorphisms)
    (hE : hexSign.ker ≤ d.offenderGroup.map e.toMonoidHom) :
    hexSign.ker ≤ (offenderEmbedding d e).range := by
  simpa only [offenderEmbedding, MonoidHom.range_comp, range_subtype] using hE

/-- The generalized Fitting subgroup maps onto the actual even cover. -/
theorem fitting_image (d : SourceInput V) (e : coreQuotient H ≃* HexAutomorphisms)
    (hE : hexSign.ker ≤ d.offenderGroup.map e.toMonoidHom) :
    (generalizedFitting d.offenderGroup).map
      (e.toMonoidHom.comp d.offenderGroup.subtype) = hexSign.ker :=
  generalizedFitting_map_eq_even _ (embedding_injective d e) (even_le_range d e hE)
    d.offenderGroup_twoCore

/-- The group equivalence induced by the literal offender embedding. -/
noncomputable def fittingEquiv (d : SourceInput V) (e : coreQuotient H ≃* HexAutomorphisms)
    (hE : hexSign.ker ≤ d.offenderGroup.map e.toMonoidHom) :
    generalizedFitting d.offenderGroup ≃* HexEvenAutomorphisms :=
  generalizedFittingEquivEven _ (embedding_injective d e) (even_le_range d e hE)
    d.offenderGroup_twoCore

/-- The equivalence retains both literal subgroup inclusions. -/
theorem fittingEquiv_apply (d : SourceInput V) (e : coreQuotient H ≃* HexAutomorphisms)
    (hE : hexSign.ker ≤ d.offenderGroup.map e.toMonoidHom)
    (x : generalizedFitting d.offenderGroup) :
    (fittingEquiv d e hE x : HexAutomorphisms) =
      e ((x : d.offenderGroup) : coreQuotient H) := by rfl

/-- Quasisimplicity follows from the concrete perfect cover, without classification. -/
theorem fitting_isQuasisimple (d : SourceInput V) (e : coreQuotient H ≃* HexAutomorphisms)
    (hE : hexSign.ker ≤ d.offenderGroup.map e.toMonoidHom) :
    IsQuasisimple (generalizedFitting d.offenderGroup) := by
  let : IsQuasisimple HexEvenAutomorphisms := even_isQuasisimple
  exact IsQuasisimple.of_mulEquiv (fittingEquiv d e hE).symm

/-- The source product factors are nontrivial, contradicting the intrinsic product obstruction. -/
theorem not_twoFactors (d : SourceInput V) (e : coreQuotient H ≃* HexAutomorphisms)
    (hE : hexSign.ker ≤ d.offenderGroup.map e.toMonoidHom) :
    ¬ Nonempty (SourceTwoFactorCase d.offenderAction) := by
  rintro ⟨c⟩
  let : Nontrivial c.first := MarkedElimination.AlternatingSevenDimension.factor_nontrivial
    (c.firstCase.factorModel d.offenderAction)
  let : Nontrivial c.second := MarkedElimination.AlternatingSevenDimension.factor_nontrivial
    (c.secondCase.factorModel d.offenderAction)
  let K := evenPreimage (offenderEmbedding d e)
  let : IsQuasisimple HexEvenAutomorphisms := even_isQuasisimple
  let : IsQuasisimple K := IsQuasisimple.of_mulEquiv
    (evenPreimageEquiv _ (embedding_injective d e) (even_le_range d e hE)).symm
  exact not_product_of_quasisimple_two_quotient K
    (quotient_evenPreimage_isTwoGroup _) d.offenderGroup_twoCore c.product.equiv

/-- Perfectness distinguishes the even cover from the source’s A₆ × C₃ product. -/
theorem not_outerSixThree (d : SourceInput V) (e : coreQuotient H ≃* HexAutomorphisms)
    (hE : hexSign.ker ≤ d.offenderGroup.map e.toMonoidHom) :
    ¬ Nonempty (OuterSixThreeCase d.offenderAction) := by
  rintro ⟨c⟩
  let K := generalizedFitting d.offenderGroup
  let : IsQuasisimple K := fitting_isQuasisimple d e hE
  let P := c.first ⊔ c.second
  let : P.Normal := c.product_normal _
  let : IsCyclic (d.offenderGroup ⧸ P) := c.quotient_isCyclic _
  have hKP : K ≤ P := le_of_isPerfect_of_solvable_quotient K P
  let g : K →* (c.first × c.second) :=
    c.product.symm.toMonoidHom.comp (Subgroup.inclusion hKP)
  have hg : Function.Injective g := c.product.symm.injective.comp
    (Subgroup.inclusion_injective hKP)
  let b : K →* Multiplicative (ZMod 3) := c.secondEquiv.toMonoidHom.comp
    ((MonoidHom.snd c.first c.second).comp g)
  let : Group.IsPerfect b.range := Group.IsPerfect.range b
  have hb (x : K) : (g x).2 = 1 := by
    apply c.secondEquiv.map_eq_one_iff.mp
    exact congrArg Subtype.val (Subsingleton.elim (⟨b x, ⟨x, rfl⟩⟩ : b.range) 1)
  have hfst : Function.Injective (fun x : K => (g x).1) := by
    intro x y he
    exact hg (Prod.ext he ((hb x).trans (hb y).symm))
  have hle := Nat.card_le_card_of_injective _ hfst
  have hKcard : Nat.card K = 1080 :=
    (Nat.card_congr (fittingEquiv d e hE).toEquiv).trans hexEven_card
  have hAcard : Nat.card c.first = 360 := by
    rw [Nat.card_congr c.firstEquiv.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  omega

/-- Excluding both remaining nonquasisimple branches retains every B.5.1 source clause. -/
theorem quasisimple_source_conclusion (d : SourceInput V)
    (e : coreQuotient H ≃* HexAutomorphisms)
    (h : SourceAlternative d.offenderAction)
    (hE : hexSign.ker ≤ d.offenderGroup.map e.toMonoidHom) :
    Nonempty (QuasisimpleSourceConclusion d.offenderAction
      (generalizedFitting d.offenderGroup)) := by
  rcases OrdinaryExclusions.remaining_source_cases d h with hq | ht | ho
  · exact hq.2
  · exact (not_twoFactors d e hE ht).elim
  · exact (not_outerSixThree d e hE ho).elim
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.TripleCover.GroupComparison
