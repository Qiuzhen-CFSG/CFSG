module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.Statement
public import Theory.Representation.GeneralLinearNatural
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison

/-!
# Faithful centerless component actions in B.5.10

The four branches with first factor L identify L with an actual special
linear group. Natural matrix actions are faithful; this passes through
repetition, compatible action equivalences, and the literal central quotient.
The center calculation uses characteristic two in degree two and odd field
degree in degree three. No faithfulness or centerlessness certificate is
assumed for the component.

These facts feed the product-constructor applications in ProductGeometry.
The marked symmetric-five case has its own normalizer argument.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.9–10,
printed pp.107–109.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.ProductGeometry
variable {G E V U : Type*} [Group G] [Group E]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup U] [Module (ZMod 2) U]
  {ρ : Representation (ZMod 2) G V} {σ : Representation (ZMod 2) E U}

private theorem faithful_of_actionEquiv (e : ActionEquiv ρ σ)
    (hf : Function.Injective σ) : Function.Injective ρ := by
  intro g h he
  apply e.groupEquiv.injective
  apply hf
  apply LinearMap.ext
  intro w
  obtain ⟨v, rfl⟩ := e.linearEquiv.surjective w
  rw [← e.intertwines, ← e.intertwines]
  exact congrArg e.linearEquiv (LinearMap.congr_fun he v)

private theorem linearNatural_faithful (F : BinaryField) (d : ℕ) :
    Function.Injective (linearNatural F d) := by
  intro g h he
  apply specialLinearNatural_injective d
  apply LinearMap.ext
  intro v
  exact LinearMap.congr_fun he v

private theorem repeated_faithful (r : ℕ) (hr : 0 < r)
    (hf : Function.Injective ρ) : Function.Injective (repeated ρ r) := by
  intro g h he
  apply hf
  apply LinearMap.ext
  intro v
  exact congrArg (fun f : Fin r → V => f ⟨0, hr⟩)
    (LinearMap.congr_fun he (fun _ => v))

private theorem faithful_of_quotient (W : Subrepresentation ρ)
    (hf : Function.Injective W.quotientRepresentation) : Function.Injective ρ := by
  intro g h he
  apply hf
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ v => exact congrArg W.toSubmodule.mkQ (LinearMap.congr_fun he v)

private theorem center_eq_bot_of_equiv (e : G ≃* E) (hz : center E = ⊥) :
    center G = ⊥ := by
  apply bot_unique
  intro x hx
  have hy := (Subgroup.centerCongr e ⟨x, hx⟩).property
  change e x ∈ center E at hy
  rw [hz, mem_bot] at hy
  exact e.injective (hy.trans e.map_one.symm)

private theorem linearThree_center (F : BinaryField) (ho : Odd F.degree) :
    center (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) = ⊥ := by
  apply (Matrix.SL3.center_eq_bot_iff_card_mod_three F.Carrier).mpr
  rw [F.card_eq]
  obtain ⟨n, hn⟩ := ho
  rw [hn, pow_add, pow_mul]
  norm_num [Nat.mul_mod, Nat.pow_mod]

theorem linearTwo_faithful_center {L : Subgroup G} (s : MovedSection ρ L)
    (F : BinaryField) (hn : IsLinearNatural (s.action.comp L.subtype) F 2) :
    Function.Injective (s.space.toRepresentation.comp L.subtype) ∧ center L = ⊥ := by
  obtain ⟨e⟩ := hn
  constructor
  · have hf := faithful_of_actionEquiv e (linearNatural_faithful F 2)
    intro g h he
    apply hf
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ v => exact congrArg s.central.toSubmodule.mkQ (LinearMap.congr_fun he v)
  · exact center_eq_bot_of_equiv e.groupEquiv (Theory.PSL2.sl2_center_eq_bot F.Carrier)

theorem doubleThree_faithful_center {L : Subgroup G} (s : MovedSection ρ L)
    (F : BinaryField) (ho : Odd F.degree)
    (hn : IsRepeatedLinearNatural (s.space.toRepresentation.comp L.subtype) F 3 2) :
    Function.Injective (s.space.toRepresentation.comp L.subtype) ∧ center L = ⊥ := by
  obtain ⟨e⟩ := hn
  exact ⟨faithful_of_actionEquiv e (repeated_faithful 2 (by decide)
    (linearNatural_faithful F 3)), center_eq_bot_of_equiv e.groupEquiv (linearThree_center F ho)⟩

theorem naturalThree_faithful_center {L : Subgroup G} (s : MovedSection ρ L)
    (F : BinaryField) (ho : Odd F.degree)
    (hn : IsLinearNatural (s.space.toRepresentation.comp L.subtype) F 3) :
    Function.Injective (s.space.toRepresentation.comp L.subtype) ∧ center L = ⊥ := by
  obtain ⟨e⟩ := hn
  exact ⟨faithful_of_actionEquiv e (linearNatural_faithful F 3),
    center_eq_bot_of_equiv e.groupEquiv (linearThree_center F ho)⟩

theorem fourCover_faithful_center {L : Subgroup G} (s : MovedSection ρ L)
    (cover : FourDimensionalCoverSource (s.space.toRepresentation.comp L.subtype)) :
    Function.Injective (s.space.toRepresentation.comp L.subtype) ∧ center L = ⊥ := by
  exact ⟨faithful_of_quotient _ (faithful_of_actionEquiv cover.natural
    (linearNatural_faithful BinaryField.two 3)),
    center_eq_bot_of_equiv cover.natural.groupEquiv (linearThree_center BinaryField.two (by decide))⟩

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.ProductGeometry
