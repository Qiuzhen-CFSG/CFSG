module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction.FlagTypes.ComponentAction.ProductRows.Groups
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.ClassifierCases.TwoFactor.Sections

/-!
# Natural component quotients in the product alternatives

The component normal-subgroup dichotomy locates C in an original factor of
the multiplication-compatible internal product. The group comparisons leave
only the natural and doubled-natural SL₃ rows, and identify that factor with C.
The global quotient map on [V,C] is then surjective onto the source summand.
Vanishing of fixed vectors in that summand identifies its kernel with
C_[V,C](C), giving the intrinsic moved quotient with multiplicity one or two.
No equality of ambient fixed spaces or whole-module splitting is used.

The binary four-dimensional extension and both hyperplane rows are excluded
by their actual actor isomorphisms. The hyperplane argument does not replace
its moved-space decomposition by a splitting of V.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.6(3),(5),
printed p.105, applied before 13.6.14 and in 13.6.19, pp.929–931.
The kernel comparison specializes the construction in the accepted
RankOneBorel/Replacement/NaturalRecognition/ClassifierCases/TwoFactor/Sections
module to a summand that is itself the image of [V,C].
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction.ComponentAction.ProductRows
open ChapterB.QuasisimpleSource ChapterB.SourceInduction ChapterB.QuasisimpleSource.ExtensionConsequences

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {C A : Subgroup D}

/-- The source image of [V,C] and its intrinsic central quotient have the same
kernel whenever the image has no C-fixed vectors. -/
def sectionImageOfMoved (s : MovedSection ρ C) (U : Subrepresentation ρ)
    (hu : U.toSubmodule = moved ρ C)
    (hfix : Representation.invariants
      (((fixed ρ).quotientImage U).toRepresentation.comp C.subtype) = ⊥) :
    ActionEquiv (s.action.comp C.subtype)
      (((fixed ρ).quotientImage U).toRepresentation.comp C.subtype) := by
  have hsu : s.space.toSubmodule = U.toSubmodule := s.space_eq.trans hu.symm
  let f : s.space.toSubmodule →ₗ[ZMod 2] ((fixed ρ).quotientImage U).toSubmodule := {
    toFun v := ⟨ρ.invariants.mkQ v, ⟨v, hsu ▸ v.property, rfl⟩⟩
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  have hk : s.central.toSubmodule = f.ker := by
    ext v
    rw [s.central_eq]
    change (∀ g : C, s.space.toRepresentation g v = v) ↔ f v = 0
    constructor
    · intro hv
      apply (Submodule.mem_bot (ZMod 2)).mp
      rw [← hfix]
      intro g
      exact congrArg f (hv g)
    · intro hv g
      apply Subtype.ext
      have hx : (v : V) ∈ ρ.invariants :=
        (Submodule.Quotient.mk_eq_zero _).mp (congrArg Subtype.val hv)
      exact hx g
  let q := s.central.toSubmodule.liftQ f hk.le
  have hq : Function.Bijective q := by
    constructor
    · apply (injective_iff_map_eq_zero _).mpr
      intro v hv
      induction v using Submodule.Quotient.induction_on with
      | _ v => exact (Submodule.Quotient.mk_eq_zero _).mpr (hk.symm ▸ hv)
    · rintro ⟨v,w,hw,rfl⟩
      exact ⟨s.central.toSubmodule.mkQ ⟨w, hsu.symm ▸ hw⟩,rfl⟩
  refine ⟨MulEquiv.refl _, LinearEquiv.ofBijective q hq, ?_⟩
  intro g v
  induction v using Submodule.Quotient.induction_on with | _ v => rfl

private def naturalRepeatedOne (E : BinaryField) :
    ActionEquiv (linearNatural E 3) (repeated (linearNatural E 3) 1) :=
  ⟨MulEquiv.refl _, (LinearEquiv.funUnique (Fin 1) (ZMod 2) (Fin 3 → E.Carrier)).symm,
    fun _ _ => rfl⟩

variable {F : Type*} [Field F] [Finite F] [CharP F 2] {m : ℕ}

omit [CharP F 2] in
private theorem exclude_small_factor (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    (e : C ≃* SL(3,F)) (hCA : C ≤ A) {H : Type*} [Finite H]
    (a : A ≃ H) (hH : Nat.card H ≤ 1080) : False :=
  not_injective_small hF hm hH (fun x => a (inclusion hCA (e.symm x)))
    (a.injective.comp ((inclusion_injective hCA).comp e.symm.injective))

/-- Every source row on a factor containing C gives either one or two copies
of a genuine natural SL₃ action on the literal component quotient. -/
theorem factor_repeated (hC : IsComponent D C) (hCA : C ≤ A)
    (hF : Nat.card F = 2 ^ m) (hm : 1 < m) (e : C ≃* SL(3,F))
    (s : MovedSection ρ C) (U : Subrepresentation ρ) (h : SourceFactorCase ρ A U) :
    ∃ (E : BinaryField) (r : ℕ), 0 < r ∧
      IsRepeatedLinearNatural (s.action.comp C.subtype) E 3 r := by
  cases h with
  | natural hu hn =>
    cases hn with
    | linearTwo E a =>
      obtain ⟨a⟩ := a
      exact (not_injective_linearTwo
        (a.groupEquiv.toMonoidHom.comp ((inclusion hCA).comp e.symm.toMonoidHom))
        (a.groupEquiv.injective.comp ((inclusion_injective hCA).comp e.symm.injective))).elim
    | symmetricFive a =>
      obtain ⟨a⟩ := a
      exact (exclude_small_factor hF hm e hCA a.groupEquiv.toEquiv
        (by norm_num [Nat.card_eq_fintype_card, Fintype.card_perm])).elim
    | linearThree E _ a =>
      obtain ⟨a⟩ := a
      have heq := component_eq_linearThree hC hCA E a.groupEquiv
      subst A
      let t := sectionImageOfMoved s U hu (invariants_of_equiv a
        (linearNatural_invariants E (by decide : 2 ≤ 3)))
      exact ⟨E,1,by decide,⟨FactorExtraction.transAction t
        (FactorExtraction.transAction a (naturalRepeatedOne E))⟩⟩
  | doubleNatural E _ hu a =>
    obtain ⟨a⟩ := a
    have heq := component_eq_linearThree hC hCA E a.groupEquiv
    subst A
    let t := sectionImageOfMoved s U hu (invariants_of_equiv a
      (repeated_invariants 2 (linearNatural_invariants E (by decide : 2 ≤ 3))))
    exact ⟨E,2,by decide,⟨FactorExtraction.transAction t a⟩⟩
  | exceptional _ a =>
    exact (exclude_small_factor hF hm e hCA a.natural.groupEquiv.toEquiv
      (by rw [card_sl_three]; norm_num [BinaryField.two])).elim

/-- Both literal factors of B.5.6(3) are treated; the four-dimensional
extension is excluded by its actual binary SL₃ actor. -/
theorem twoFactor_repeated (hC : IsComponent D C)
    (hF : Nat.card F = 2 ^ m) (hm : 1 < m) (e : C ≃* SL(3,F))
    (s : MovedSection ρ C) (c : SourceTwoFactorCase ρ) :
    ∃ (E : BinaryField) (r : ℕ), 0 < r ∧
      IsRepeatedLinearNatural (s.action.comp C.subtype) E 3 r := by
  rcases CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.ClassifierCases.TwoFactor.component_le_factor hC c.product with h | h
  · exact factor_repeated hC h hF hm e s c.firstSpace c.firstCase
  · exact factor_repeated hC h hF hm e s c.secondSpace c.secondCase

/-- The hyperplane alternative is impossible for the actual larger-field
SL₃ component. Only its product and literal actor identifications are needed. -/
theorem not_hyperplane (hC : IsComponent D C)
    (hF : Nat.card F = 2 ^ m) (hm : 1 < m) (e : C ≃* SL(3,F))
    (c : HyperplaneCase ρ) : False := by
  rcases CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.ClassifierCases.TwoFactor.component_le_factor hC c.product with h | h
  · exact exclude_small_factor hF hm e h c.firstEquiv.toEquiv
      (by rw [card_sl_three]; norm_num)
  · cases c.secondCase with
    | linearThree r _ a =>
      obtain ⟨a⟩ := a
      exact exclude_small_factor hF hm e h a.groupEquiv.toEquiv
        (by rw [card_sl_three]; norm_num [BinaryField.two])
    | linearTwo E a =>
      obtain ⟨a⟩ := a
      exact not_injective_linearTwo
        (a.groupEquiv.toMonoidHom.comp ((inclusion h).comp e.symm.toMonoidHom))
        (a.groupEquiv.injective.comp ((inclusion_injective h).comp e.symm.injective))

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction.ComponentAction.ProductRows
