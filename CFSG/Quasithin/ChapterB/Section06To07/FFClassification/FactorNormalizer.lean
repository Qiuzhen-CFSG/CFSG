module
public import Theory.Representation.BinaryOffender.IrreducibleTransport
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Statement
public import Theory.Representation.BinaryOffender.MarkedCentralQuotient
public import Theory.Representation.BinaryOffender.MovedSpaceTransport

/-!
# Normalizer actions on the original B.5.6 quotient summands

A source factor summand is the image of [V,A] in V/C_V(Y). Since Y is
normal, the full ambient group acts on this quotient; the actual normalizer
of A preserves its moved image. Restriction to A agrees with the original
B.5.6 action, including its actor mark and quotient coordinates. Thus every
natural or doubled-natural row has the required normalizer chart without
assuming the action descends through the component centralizer.

The final theorem consumes the literal SourceFactorCase; its exceptional
extension branch is retained unchanged.
Source: Aschbacher–Smith B.5.6(3) and B.6.9, printed pp.105 and 116.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB
open QuasisimpleSource SourceInduction
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (Y : Subgroup G) [Y.Normal]
  (A : Subgroup Y) (U : Subrepresentation (ρ.comp Y.subtype))

set_option backward.isDefEq.respectTransparency false in
/-- The original factor image is the moved space of the global fixed quotient. -/
theorem source_factor_image_eq_moved
    (hU : U.toSubmodule = moved (ρ.comp Y.subtype) A) :
    ((fixed (ρ.comp Y.subtype)).quotientImage U).toSubmodule =
      moved (fixedQuotient ρ Y) (A.map Y.subtype) := by
  have he := subspaceCommutator_map_embedding (fixedQuotient ρ Y) ρ (MonoidHom.id G)
    (fixedSpace ρ Y).mkQ (fun _ _ => rfl) (A.map Y.subtype) ⊤
  rw [Submodule.map_top, LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _),
    Subgroup.map_id] at he
  have hm := subspaceCommutator_map_embedding (ρ.comp Y.subtype) ρ Y.subtype
    (LinearMap.id : V →ₗ[ZMod 2] V) (fun _ _ => rfl) A ⊤
  simp only [Submodule.map_id] at hm
  change U.toSubmodule.map (fixedSpace ρ Y).mkQ = _
  rw [hU]
  exact (congrArg (fun W : Submodule (ZMod 2) V => W.map (fixedSpace ρ Y).mkQ) hm).trans he.symm

/-- The actual normalizer acts on the same B.5.6 quotient summand. -/
def sourceFactorNormalizerSpace
    (hU : U.toSubmodule = moved (ρ.comp Y.subtype) A) :
    Subrepresentation ((fixedQuotient ρ Y).comp
      (normalizer (A.map Y.subtype : Set G)).subtype) where
  toSubmodule := ((fixed (ρ.comp Y.subtype)).quotientImage U).toSubmodule
  apply_mem_toSubmodule g v hv := by
    rw [source_factor_image_eq_moved ρ Y A U hU] at hv ⊢
    exact (subspaceCommutator_invariant_normalizer (fixedQuotient ρ Y)
      (le_subspaceStabilizer _ ⊤ (by intros; trivial)) le_rfl g.property v).2 hv

/-- The original component mark, including both subtype inclusions. -/
def sourceFactorNormalizerEquiv :
    (A.map Y.subtype).subgroupOf (normalizer (A.map Y.subtype : Set G)) ≃* A :=
  (subgroupOfEquivOfLe (A.map Y.subtype).le_normalizer).trans
    (A.equivMapOfInjective Y.subtype Y.subtype_injective).symm

/-- Quotient coordinates keep their original actor under the normalizer action. -/
def sourceFactorNormalizerActionEquiv
    (hU : U.toSubmodule = moved (ρ.comp Y.subtype) A) :
    ActionEquiv ((sourceFactorNormalizerSpace ρ Y A U hU).toRepresentation.comp
      ((A.map Y.subtype).subgroupOf (normalizer (A.map Y.subtype : Set G))).subtype)
      (((fixed (ρ.comp Y.subtype)).quotientImage U).toRepresentation.comp A.subtype) where
  groupEquiv := sourceFactorNormalizerEquiv Y A
  linearEquiv := LinearEquiv.refl _ _
  intertwines a v := by
    have ha : (((sourceFactorNormalizerEquiv Y A a : A) : Y) : G) =
        (((a : (A.map Y.subtype).subgroupOf (normalizer (A.map Y.subtype : Set G))) :
          normalizer (A.map Y.subtype : Set G)) : G) := by
      exact congrArg Subtype.val ((A.equivMapOfInjective Y.subtype Y.subtype_injective).apply_symm_apply
        ((subgroupOfEquivOfLe (A.map Y.subtype).le_normalizer) a))
    apply Subtype.ext
    have he : fixedQuotient ρ Y (a : G) =
        (fixed (ρ.comp Y.subtype)).quotientRepresentation
          (sourceFactorNormalizerEquiv Y A a : Y) := by
      apply LinearMap.ext
      intro w
      induction w using Submodule.Quotient.induction_on with
      | _ w =>
        change (fixedSpace ρ Y).mkQ (ρ (a : G) w) =
          (fixedSpace ρ Y).mkQ (ρ (((sourceFactorNormalizerEquiv Y A a : A) : Y) : G) w)
        rw [ha]
    exact LinearMap.congr_fun he v.val

/-- A natural source row supplies its actual full-normalizer chart. -/
theorem source_factor_normalizer_natural
    (hU : U.toSubmodule = moved (ρ.comp Y.subtype) A)
    (F : BinaryField) (n : ℕ)
    (h : IsLinearNatural
      (((fixed (ρ.comp Y.subtype)).quotientImage U).toRepresentation.comp A.subtype) F n) :
    IsLinearNatural ((sourceFactorNormalizerSpace ρ Y A U hU).toRepresentation.comp
      ((A.map Y.subtype).subgroupOf (normalizer (A.map Y.subtype : Set G))).subtype) F n := by
  obtain ⟨c⟩ := h
  let e := sourceFactorNormalizerActionEquiv ρ Y A U hU
  exact ⟨⟨e.groupEquiv.trans c.groupEquiv, e.linearEquiv.trans c.linearEquiv,
    fun g v => (congrArg c.linearEquiv (e.intertwines g v)).trans (c.intertwines _ _)⟩⟩

/-- A doubled-natural source row supplies its actual full-normalizer chart. -/
theorem source_factor_normalizer_repeated_natural
    (hU : U.toSubmodule = moved (ρ.comp Y.subtype) A)
    (F : BinaryField) (n r : ℕ)
    (h : IsRepeatedLinearNatural
      (((fixed (ρ.comp Y.subtype)).quotientImage U).toRepresentation.comp A.subtype) F n r) :
    IsRepeatedLinearNatural ((sourceFactorNormalizerSpace ρ Y A U hU).toRepresentation.comp
      ((A.map Y.subtype).subgroupOf (normalizer (A.map Y.subtype : Set G))).subtype) F n r := by
  obtain ⟨c⟩ := h
  let e := sourceFactorNormalizerActionEquiv ρ Y A U hU
  exact ⟨⟨e.groupEquiv.trans c.groupEquiv, e.linearEquiv.trans c.linearEquiv,
    fun g v => (congrArg c.linearEquiv (e.intertwines g v)).trans (c.intertwines _ _)⟩⟩
/-- Apply the original B.5.6 factor row to the actual normalizer action.
The exceptional extension remains the exact original branch. -/
theorem source_factor_normalizer_cases
    (h : SourceFactorCase (ρ.comp Y.subtype) A U) :
    (∃ hU : U.toSubmodule = moved (ρ.comp Y.subtype) A,
      FactorNatural ((sourceFactorNormalizerSpace ρ Y A U hU).toRepresentation.comp
        ((A.map Y.subtype).subgroupOf (normalizer (A.map Y.subtype : Set G))).subtype)) ∨
    (∃ hU : U.toSubmodule = moved (ρ.comp Y.subtype) A, ∃ F : BinaryField,
      Odd F.degree ∧ IsRepeatedLinearNatural
        ((sourceFactorNormalizerSpace ρ Y A U hU).toRepresentation.comp
          ((A.map Y.subtype).subgroupOf (normalizer (A.map Y.subtype : Set G))).subtype) F 3 2) ∨
    (moved (ρ.comp Y.subtype) A ≤ U.toSubmodule ∧
      Nonempty (FourDimensionalSource
        (((fixed (ρ.comp Y.subtype)).quotientImage U).toRepresentation.comp A.subtype))) := by
  cases h with
  | natural hU hn =>
    left
    refine ⟨hU,?_⟩
    cases hn with
    | linearTwo F hc => exact .linearTwo F (source_factor_normalizer_natural ρ Y A U hU F 2 hc)
    | linearThree F ho hc =>
      exact .linearThree F ho (source_factor_normalizer_natural ρ Y A U hU F 3 hc)
    | symmetricFive hc =>
      obtain ⟨c⟩ := hc
      let e := sourceFactorNormalizerActionEquiv ρ Y A U hU
      exact .symmetricFive ⟨⟨e.groupEquiv.trans c.groupEquiv, e.linearEquiv.trans c.linearEquiv,
        fun g v => (congrArg c.linearEquiv (e.intertwines g v)).trans (c.intertwines _ _)⟩⟩
  | doubleNatural F ho hU hc =>
    exact Or.inr (Or.inl ⟨hU,F,ho,source_factor_normalizer_repeated_natural ρ Y A U hU F 3 2 hc⟩)
  | exceptional hU hc => exact Or.inr (Or.inr ⟨hU,⟨hc⟩⟩)

end CFSG.Quasithin.ChapterB
