module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.FixedSpace.Inputs
public import Theory.Representation.PSL3Three.AbsoluteDegrees.Saturation
public import Theory.Representation.InjectiveDescent

/-!
# HS five-center fixed spaces from modular saturation

Actual pairwise inequivalent simple models, together with a bound on the
number of odd-order conjugacy classes, exhaust the simple representations by
modular trace independence. In degree at most fifty only the trivial model
and the degree-twenty model survive. Extension to an algebraic closure
preserves dimension, and the proved extraspecial restriction excludes degree
one for a faithful action. The same restriction then makes the literal
five-center fixed-point-free on the original coefficient field.

The three construction inputs in `FixedSpace.Inputs` remain explicit. This
module supplies their checked application, not the unconditional theorem
`fiveCenterFixedFreeInWindow`. It assumes neither the degree of the arbitrary
input action nor a character table's completeness.

Source: Guralnick--Malle, *Classification of 2F-modules I*, Proposition 5.1,
HS paragraph, author-preprint p.16; Hiss--Malle, corrected Table 2;
Aschbacher--Smith K.4, printed p.457.
-/

public section
open scoped TensorProduct
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow

universe v

namespace FixedSpace

/-- The independently constructed binary model supplies the closed-field input
by actual scalar extension and its coordinate equivalence. -/
theorem twentyModelExists_of_binary_model
    (σ : Representation (ZMod 2) KnownSimple.SporadicName.hs.Carrier
      (Fin 20 → ZMod 2)) (hi : σ.IsAbsolutelyIrreducible) :
    TwentyModelExists.{v} := by
  intro _ F _ _ _
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let := hi
  refine ⟨Representation.mapCoefficients (algebraMap (ZMod 2) F) σ, ?_⟩
  exact (Representation.extendScalarsMapCoefficientsEquiv (E := F) σ).irreducible_euqiv.mp
    (Representation.IsAbsolutelyIrreducible.irreducible_of_extension σ F)

private theorem largeDegree_gt_fifty (i : Fin 7) : 50 < largeDegree i := by
  revert i
  decide

/-- The nine genuine simple actions exhaust the small window once their
number reaches the proved odd-order conjugacy-class bound. -/
theorem finrank_eq_one_or_twenty_of_models
    (hclasses : OddClassBound) (hsmall : TwentyModelExists.{v})
    (hlarge : LargeModelsExist.{v})
    (hs : IsSimpleGroup KnownSimple.SporadicName.hs.Carrier)
    {F U : Type v} [Field F] [IsAlgClosed F] [CharP F 2]
    [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    (τ : Representation F KnownSimple.SporadicName.hs.Carrier U)
    [τ.IsIrreducible] (hd : Module.finrank F U ≤ 50) :
    Module.finrank F U = 1 ∨ Module.finrank F U = 20 := by
  classical
  let : Finite KnownSimple.SporadicName.hs.Carrier :=
    inferInstanceAs (Finite _root_.Sporadic.LeechRelated.HS.Carrier)
  obtain ⟨ρs, hsirr⟩ := hsmall hs F
  obtain ⟨ρl, hlirr, hlne⟩ := hlarge hs F
  let V : Option (Option (Fin 7)) → Type v := fun i => match i with
    | none => F
    | some none => Fin 20 → F
    | some (some j) => Fin (largeDegree j) → F
  let addV : ∀ i, AddCommGroup (V i) := fun i => by
    rcases i with _ | (_ | i) <;> dsimp [V] <;> infer_instance
  let modV : ∀ i, Module F (V i) := fun i => by
    rcases i with _ | (_ | i) <;> dsimp [V] <;> infer_instance
  let rep : ∀ i, Representation F KnownSimple.SporadicName.hs.Carrier (V i) :=
    fun i => match i with
    | none => Representation.trivial F KnownSimple.SporadicName.hs.Carrier F
    | some none => ρs
    | some (some j) => ρl j
  have finV : ∀ i, FiniteDimensional F (V i) := by
    intro i
    rcases i with _ | (_ | i) <;> dsimp [V] <;> infer_instance
  have irr : ∀ i, (rep i).IsIrreducible := by
    intro i
    rcases i with _ | (_ | i)
    · change (Representation.trivial F KnownSimple.SporadicName.hs.Carrier F).IsIrreducible
      constructor
      intro S
      rcases IsSimpleOrder.eq_bot_or_eq_top S.toSubmodule with h | h
      · exact Or.inl (Subrepresentation.toSubmodule_injective h)
      · exact Or.inr (Subrepresentation.toSubmodule_injective h)
    · exact hsirr
    · exact hlirr i
  have hdistinct : Pairwise fun i j => IsEmpty ((rep i).Equiv (rep j)) := by
    intro i j hij
    constructor
    intro e
    have he := e.toLinearEquiv.finrank_eq
    rcases i with _ | (_ | i) <;> rcases j with _ | (_ | j)
    all_goals simp only [V, Module.finrank_self, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin] at he
    · exact hij rfl
    · omega
    · have := largeDegree_gt_fifty j; omega
    · omega
    · exact hij rfl
    · have := largeDegree_gt_fifty j; omega
    · have := largeDegree_gt_fifty i; omega
    · have := largeDegree_gt_fifty i; omega
    · exact (hlne (fun h => hij (by rw [h]))).false e
  have hc : Nat.card (Option (Option (Fin 7))) = 9 := by
    simp [Nat.card_eq_fintype_card]
  obtain ⟨i, ⟨e⟩⟩ := Representation.exists_equiv_of_pRegular_class_bound V rep 2 hdistinct
    (hc ▸ hclasses hs) τ
  have he := e.toLinearEquiv.finrank_eq
  rcases i with _ | (_ | i)
  all_goals simp only [V, Module.finrank_self, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin] at he
  · exact Or.inl he
  · exact Or.inr he
  · have := largeDegree_gt_fifty i
    omega

end FixedSpace

/-- Concrete application to the original representation and literal five-center.
The model and conjugacy constructions are independent remaining premises; the
fixed-free degree-forty exclusion is not used. -/
theorem fiveCenterFixedFreeInWindow_of_saturating_models
    (hclasses : FixedSpace.OddClassBound)
    (hsmall : FixedSpace.TwentyModelExists.{v})
    (hlarge : FixedSpace.LargeModelsExist.{v}) : FiveCenterFixedFreeInWindow.{v} := by
  intro hs K _ _ _ W _ _ _ τ hf hi hd
  let F := AlgebraicClosure K
  let := hi.irreducible_of_closure
  have hd' : Module.finrank F (F ⊗[K] W) ≤ 50 := by
    simpa only [Module.finrank_baseChange] using hd
  have h := FixedSpace.finrank_eq_one_or_twenty_of_models hclasses hsmall hlarge hs
    (Representation.extendScalars F τ) hd'
  simp only [Module.finrank_baseChange] at h
  obtain ⟨a, ha, he⟩ := finrank_eq_fixed_add_twenty_mul τ hf
  have htwenty : Module.finrank K W = 20 := by omega
  exact fiveCenter_fixed_eq_bot_of_finrank_twenty τ hf htwenty

/-- Application with the literal binary model supplied by the existing
model-construction task. Its action is extended to every coefficient field;
no identification of the arbitrary input action with that model is assumed. -/
theorem fiveCenterFixedFreeInWindow_of_binary_model_and_saturation
    (hclasses : FixedSpace.OddClassBound)
    (σ : Representation (ZMod 2) KnownSimple.SporadicName.hs.Carrier
      (Fin 20 → ZMod 2)) (hi : σ.IsAbsolutelyIrreducible)
    (hlarge : FixedSpace.LargeModelsExist.{v}) : FiveCenterFixedFreeInWindow.{v} :=
  fiveCenterFixedFreeInWindow_of_saturating_models hclasses
    (FixedSpace.twentyModelExists_of_binary_model σ hi) hlarge

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow
