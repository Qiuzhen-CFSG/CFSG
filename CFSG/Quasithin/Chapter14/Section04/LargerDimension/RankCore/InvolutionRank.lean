module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.KnownModels
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.OrthogonalInspection
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.TensorInspection

/-!
# The involution-rank dichotomy of 14.4.6

The input alternatives mark the literal H/O₂(H) action on U/Z(U), rather
than merely its group isomorphism type. In the S₇ and triple-M₂₂ branches,
the existing representation bounds exclude rank at most two. The full
normalizer inspection in the orthogonal branch and the constituent inspection
in the tensor branch give rank exactly two in the two stated exceptions.
Sylow normalization makes the actual distinguished quotient line singular;
the displacement line is nonsingular, giving the required exclusion.

`ActionAlternative` is the action portion of the explicit earlier 14.4.2
input, not a substitute for Hypothesis 14.3.10. The source application in
`Source` uses the actual ambient subgroups, extraspecial U, earlier geometry,
and source model generation to discharge the rank premise of 14.4.7.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
14.4.2(3)--(6) and 14.4.6, printed pp.1006--1008.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore
open TensorProduct Subgroup Representation BinaryPermutation ClassicalOrthogonal
open ClassicalOrthogonal.FourPlusMatrix
open CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor

universe w
variable {H V : Type*} [Group H] {U : Subgroup H} [U.Normal]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- The literal group and module alternatives of 14.4.2(3)--(6).
No displacement or marked-vector condition is included. -/
inductive ActionAlternative (d : SourceAction H U V) : Prop
  | orthogonal
      (κ : ((pResidual 2 H).map (QuotientGroup.mk' (pCore 2 H))) ≃* OmegaPlus 2 Binary.F)
      (e : V ≃ₗ[ZMod 2] VectorD 2 Binary.F)
      (he : ∀ (k : (pResidual 2 H).map (QuotientGroup.mk' (pCore 2 H))) v,
        e (d.representation k v) = subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v)) :
      ActionAlternative d
  | symmetricSeven
      (e : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 7))
      (p : AlternatingSevenConjugatePair.Pair V)
      (he : ∀ a v, d.representation a v = p.representation (e a) v) :
      ActionAlternative d
  | tensor {W : Type w} [AddCommGroup W] [Module (ZMod 2) W]
      (D : Subgroup Five) (hAD : AltFive ≤ D)
      (σ : Representation (ZMod 2) D W)
      (hD : D = ⊤ ∨ D = AltFive) (hσ : IsSourceConstituent hAD σ)
      (e : (H ⧸ pCore 2 H) ≃* Three × D)
      (f : V ≃ₗ[ZMod 2] (core (Fin 3) ⊗[ZMod 2] W))
      (hf : ∀ a v, f (d.representation a v) = sourceTensorAction σ (e a) (f v)) :
      ActionAlternative d
  | tripleM22
      (hL : CFSG.Quasithin.ChapterH.Section10To12.IsTripleM22
        (Theory.GroupTheory.generalizedFitting (H ⧸ pCore 2 H)))
      (hirr : d.representation.IsIrreducible)
      (hd : Module.finrank (ZMod 2) V = 12) : ActionAlternative d

/-- The two exceptional alternatives retain their actual module markings. -/
inductive ExceptionalAction (d : SourceAction H U V) : Prop
  | orthogonal
      (κ : ((pResidual 2 H).map (QuotientGroup.mk' (pCore 2 H))) ≃* OmegaPlus 2 Binary.F)
      (e : V ≃ₗ[ZMod 2] VectorD 2 Binary.F)
      (he : ∀ (k : (pResidual 2 H).map (QuotientGroup.mk' (pCore 2 H))) v,
        e (d.representation k v) = subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v)) :
      ExceptionalAction d
  | tensorDeleted {W : Type w} [AddCommGroup W] [Module (ZMod 2) W]
      (D : Subgroup Five) (hAD : AltFive ≤ D)
      (σ : Representation (ZMod 2) D W) (hD : D = ⊤) (hσ : IsDeletedFour hAD σ)
      (e : (H ⧸ pCore 2 H) ≃* Three × D)
      (f : V ≃ₗ[ZMod 2] (core (Fin 3) ⊗[ZMod 2] W))
      (hf : ∀ a v, f (d.representation a v) = sourceTensorAction σ (e a) (f v)) :
      ExceptionalAction d

/-- Conditional source Lemma 14.4.6, including both exceptional module
alternatives and the singular/nonsingular exclusion of the actual line. -/
theorem SourceAction.involution_rank_dichotomy [Finite H] [Module.Finite (ZMod 2) V]
    (d : SourceAction H U V) (models : ActionAlternative.{w} d)
    (T : Sylow 2 H) (V₂ : Subgroup H)
    (hnorm : (T : Subgroup H) ≤ normalizer (V₂ : Set H))
    (hdim : Module.finrank (ZMod 2) (d.image V₂) = 1)
    (a : H ⧸ pCore 2 H) (ha : orderOf a = 2) :
    2 < d.movedRank a ∨
      (ExceptionalAction.{w} d ∧ d.movedRank a = 2 ∧ ¬ d.image V₂ ≤ d.moved a) := by
  by_cases hr : 2 < d.movedRank a
  · exact Or.inl hr
  right
  have hle : d.movedRank a ≤ 2 := Nat.le_of_not_gt hr
  cases models with
  | orthogonal κ e he =>
    obtain ⟨hb, _, hexcl⟩ := d.orthogonal_inspection κ e he T V₂ hnorm hdim a ha hle
    exact ⟨.orthogonal κ e he, hb, hexcl⟩
  | symmetricSeven e p he =>
    have hb := d.symmetricSeven_movedRank U e p (LinearEquiv.refl (ZMod 2) V) he a ha
    omega
  | tensor D hAD σ hD hσ e f hf =>
    obtain ⟨hD', hσ', _, hb, hexcl⟩ :=
      d.tensor_inspection σ hD hσ e f hf T V₂ hnorm hdim a ha hle
    exact ⟨.tensorDeleted D hAD σ hD' hσ' e f hf, hb, hexcl⟩
  | tripleM22 hL hirr hd =>
    let := hirr
    have hb := d.tripleM22_movedRank U _ hL rfl hd a ha
    omega

/-- The rank obstruction consumed by the conjugate-centralizer argument. -/
theorem SourceAction.rank_obstruction [Finite H] [Module.Finite (ZMod 2) V]
    (d : SourceAction H U V) (models : ActionAlternative.{w} d)
    (T : Sylow 2 H) (V₂ : Subgroup H)
    (hnorm : (T : Subgroup H) ≤ normalizer (V₂ : Set H))
    (hdim : Module.finrank (ZMod 2) (d.image V₂) = 1)
    (a : H ⧸ pCore 2 H) (ha : orderOf a = 2) :
    2 < d.movedRank a ∨ (d.movedRank a = 2 ∧ ¬ d.image V₂ ≤ d.moved a) := by
  rcases d.involution_rank_dichotomy models T V₂ hnorm hdim a ha with h | ⟨_, h⟩
  · exact Or.inl h
  · exact Or.inr h
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore
