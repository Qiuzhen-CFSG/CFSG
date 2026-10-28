module

public import Theory.Representation.ModularDegreeRecognition
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.FixedSpace.Inputs
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.TraceField.ElevenFixedFree.Model.Assembly

/-!
# Universal HS degree-twenty comparison by modular saturation

Over an algebraically closed characteristic-two field, the constructed
binary model extends to a simple representation of degree twenty. Together
with the trivial representation and seven larger simple models it exhausts
the simple representations if HS has at most nine odd-order conjugacy
classes. The other eight degrees differ from twenty, so saturation gives
an actual equivalence from every simple degree-twenty representation to the
scalar extension of the constructed model.

Apply this over the algebraic closure of the arbitrary finite coefficient
field. Absolute irreducibility supplies the original action's simplicity
after extension. The equivalence supplies the nonzero intertwiner required
by `DegreeTwentyModelComparison`; the checked model's order-eleven calculation
and the existing fixed-space descent then give `DegreeTwentyElevenFixedFree`.
Thus the arbitrary representation needs no binary field of definition,
cubic-ratio bound or extension to an outer automorphism group.

The odd-class bound and seven larger simple models remain explicit inputs.
Their independent constructions also serve the absolute degree-window
argument. The theorems here establish universal transport conditional on
those constructions; the unconditional source assertion remains to be assembled.

Source: Guralnick--Malle, *Classification of 2F-modules I*, Proposition 5.1,
HS paragraph, published p.366 (author-preprint p.16), and the concrete
HSG1-f2r20B0 action. The source's order-eleven inversion calculation is
https://www.math.uni-bielefeld.de/~baumeist/sommerschule/Guralmalle2F.pdf .
-/

public section
open scoped TensorProduct
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.TraceField.Universal
universe v

open AbsoluteWindow.FixedSpace
open _root_.Sporadic.LeechRelated.HS.Twenty

private theorem largeDegree_gt_twenty (i : Fin 7) : 20 < largeDegree i := by
  revert i
  decide

/-- Modular saturation identifies every simple degree-twenty action over a
closed field with the actual constructed binary model after scalar extension. -/
theorem equiv_constructedModel_of_saturation
    (hclasses : OddClassBound) (hlarge : LargeModelsExist.{v})
    (hs : IsSimpleGroup KnownSimple.SporadicName.hs.Carrier)
    {F U : Type v} [Field F] [IsAlgClosed F] [CharP F 2]
    [Algebra (ZMod 2) F]
    [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    (τ : Representation F KnownSimple.SporadicName.hs.Carrier U)
    [hτ : τ.IsIrreducible] (hd : Module.finrank F U = 20) :
    Nonempty (τ.Equiv (carrierRepresentation.extendScalars F)) := by
  classical
  let : Finite KnownSimple.SporadicName.hs.Carrier :=
    inferInstanceAs (Finite _root_.Sporadic.LeechRelated.HS.Carrier)
  let := carrierRepresentation_absolutelyIrreducible
  let hσ := Representation.IsAbsolutelyIrreducible.irreducible_of_extension
    carrierRepresentation F
  obtain ⟨ρ, hirr, hne⟩ := hlarge hs F
  let V : Option (Fin 7) → Type v := fun i => match i with
    | none => F
    | some j => Fin (largeDegree j) → F
  let addV : ∀ i, AddCommGroup (V i) := fun i => by
    cases i <;> dsimp [V] <;> infer_instance
  let modV : ∀ i, Module F (V i) := fun i => by
    cases i <;> dsimp [V] <;> infer_instance
  let rep : ∀ i, Representation F KnownSimple.SporadicName.hs.Carrier (V i) :=
    fun i => match i with
    | none => Representation.trivial F KnownSimple.SporadicName.hs.Carrier F
    | some j => ρ j
  have finV : ∀ i, FiniteDimensional F (V i) := by
    intro i
    cases i <;> dsimp [V] <;> infer_instance
  let irr : ∀ i, (rep i).IsIrreducible := by
    intro i
    cases i with
    | none =>
      change (Representation.trivial F KnownSimple.SporadicName.hs.Carrier F).IsIrreducible
      constructor
      intro S
      rcases IsSimpleOrder.eq_bot_or_eq_top S.toSubmodule with h | h
      · exact Or.inl (Subrepresentation.toSubmodule_injective h)
      · exact Or.inr (Subrepresentation.toSubmodule_injective h)
    | some i => exact hirr i
  have hdistinct : Pairwise fun i j => IsEmpty ((rep i).Equiv (rep j)) := by
    intro i j hij
    refine ⟨fun e => ?_⟩
    have he := e.toLinearEquiv.finrank_eq
    cases i with
    | none =>
      cases j with
      | none => exact hij rfl
      | some j =>
        simp only [V, Module.finrank_self, Module.finrank_fintype_fun_eq_card,
          Fintype.card_fin] at he
        have := largeDegree_gt_twenty j
        omega
    | some i =>
      cases j with
      | none =>
        simp only [V, Module.finrank_self, Module.finrank_fintype_fun_eq_card,
          Fintype.card_fin] at he
        have := largeDegree_gt_twenty i
        omega
      | some j => exact (hne (fun h => hij (congrArg some h))).false e
  have hmodel : Module.finrank F (F ⊗[ZMod 2] Vector) = 20 := by
    rw [Module.finrank_baseChange, representation_finrank]
  have hdifferent : ∀ i, Module.finrank F (V i) ≠
      Module.finrank F (F ⊗[ZMod 2] Vector) := by
    intro i
    rw [hmodel]
    cases i with
    | none => simp [V]
    | some i =>
      simpa only [V, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
        (ne_of_gt (largeDegree_gt_twenty i))
  have hc : Nat.card (Option (Fin 7)) + 1 = 9 := by
    simp [Nat.card_eq_fintype_card]
  exact Representation.nonempty_equiv_of_complementary_models
    (hirr := irr) (hσ := hσ) (hτ := hτ)
    (carrierRepresentation.extendScalars F) V rep 2 hdistinct hdifferent
    (hc.symm ▸ hclasses hs) τ (hd.trans hmodel.symm)

/-- Recognition over the common algebraic closure supplies the exact nonzero
intertwiner contract, for every finite characteristic-two coefficient field. -/
theorem constructedModelComparison_of_saturation
    (hclasses : OddClassBound) (hlarge : LargeModelsExist.{v}) :
    DegreeTwentyModelComparison.{0,v} carrierRepresentation := by
  intro hs K _ _ _ W _ _ _ τ _ hi hd
  let : Algebra (ZMod 2) (AlgebraicClosure K) :=
    (ZMod.castHom (dvd_refl 2) (AlgebraicClosure K)).toAlgebra
  let := hi.irreducible_of_closure
  let : Nontrivial (AlgebraicClosure K ⊗[K] W) :=
    Subrepresentation.irreducible_module_nontrivial (τ.extendScalars (AlgebraicClosure K))
  obtain ⟨e⟩ := equiv_constructedModel_of_saturation hclasses hlarge hs
    (τ.extendScalars (AlgebraicClosure K))
    (by simpa only [Module.finrank_baseChange] using hd)
  refine ⟨e.toIntertwiningMap, ?_⟩
  intro hz
  have hzero : e.toLinearEquiv.toLinearMap = 0 :=
    congrArg Representation.IntertwiningMap.toLinearMap hz
  exact (LinearMap.ne_zero_of_injective e.toLinearEquiv.injective) hzero

/-- The actual model calculation transfers to every faithful absolute
characteristic-two degree-twenty module once the two saturation inputs are proved. -/
theorem degreeTwentyElevenFixedFree_of_saturation
    (hclasses : OddClassBound) (hlarge : LargeModelsExist.{v}) :
    DegreeTwentyElevenFixedFree.{v} :=
  Model.degreeTwentyElevenFixedFree_of_constructedModelComparison
    (constructedModelComparison_of_saturation hclasses hlarge)

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.TraceField.Universal
