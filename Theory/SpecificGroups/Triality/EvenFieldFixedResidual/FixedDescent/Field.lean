module

public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.Twist
/-!
# The smaller coefficient field and its split D4 embedding

For n = 2m > 0, the fixed field of prime Frobenius to the power 3m is
GF(2^(3m)). Choose an actual field equivalence and compose its inverse with
the subfield inclusion. The induced entrywise Geck-group homomorphism is
injective, has coefficient-fixed image, and intertwines the smaller defining
graph-field action with the forward half-parameter action in the larger group.

These are the field and functoriality steps of Aschbacher–Smith 16.1.4(4),
printed p.1171 (`refs/quasithin.pdf`), with the standard form of GLS3 §§2.2
and 2.5 (`refs/KGroup/GLS3/chapter2.tex`). Surjectivity onto the relevant
fixed matrices still requires subfield descent in the root-generated group.
-/

@[expose] public section
noncomputable section
open Triality.Standard Triality.Standard.OuterOdd
open Theory.AlgebraicGroup.StandardRootSystem
open scoped Matrix
namespace Triality.Standard.EvenField
local instance matrixIndexDecidableEq :
    DecidableEq ((typeDRootPairing_base 2).support ⊕ TypeDRootIndex (2 + 2)) := instDecidableEqSum

/-- The literal scalar fixed subfield of the coefficient involution. -/
def halfField (n : ℕ) (hn : 0 < n) (m : ℕ) : Subfield (ExtensionField (binaryParameters n hn)) :=
  FixedBy.subfield _ (coefficientFrobenius n hn (3*m))

private theorem halfField_nonempty_equiv (n : ℕ) (hn : 0 < n)
    (m : ℕ) (hm : 0 < m) (hnm : n = 2*m) :
    Nonempty (halfField n hn m ≃+* ExtensionField (binaryParameters m hm)) := by
  let e := coefficientFrobenius n hn (3*m)
  have ho : orderOf e = 2 := coefficientFrobenius_order_two n hn m hm hnm
  have he : e^2 = 1 := ho ▸ pow_orderOf_eq_one e
  have hne : e ≠ 1 := by intro h; simp [h] at ho
  obtain ⟨k, hk, hnk, hF⟩ := coefficient_fixedField_model n hn e he hne
  have hkm : k = m := by omega
  subst k
  exact hF

/-- The scalar fixed subfield is the canonical smaller cubic binary field. -/
def halfFieldEquiv (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : 0 < m) (hnm : n = 2*m) :
    halfField n hn m ≃+* ExtensionField (binaryParameters m hm) :=
  Classical.choice (by exact halfField_nonempty_equiv n hn m hm hnm)

/-- Embed the smaller canonical coefficient field into the larger one. -/
def halfFieldEmbedding (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : 0 < m) (hnm : n = 2*m) :
    ExtensionField (binaryParameters m hm) →+* ExtensionField (binaryParameters n hn) :=
  (halfField n hn m).subtype.comp (halfFieldEquiv n hn m hm hnm).symm.toRingHom

/-- Every embedded scalar is fixed by the coefficient involution. -/
theorem halfFieldEmbedding_fixed (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : 0 < m)
    (hnm : n = 2*m) (t : ExtensionField (binaryParameters m hm)) :
    coefficientFrobenius n hn (3*m) (halfFieldEmbedding n hn m hm hnm t) =
      halfFieldEmbedding n hn m hm hnm t :=
  ((halfFieldEquiv n hn m hm hnm).symm t).property

/-- Every fixed scalar, and only a fixed scalar, comes from the smaller field. -/
theorem halfFieldEmbedding_range (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : 0 < m)
    (hnm : n = 2*m) (t : ExtensionField (binaryParameters n hn)) :
    t ∈ Set.range (halfFieldEmbedding n hn m hm hnm) ↔
      coefficientFrobenius n hn (3*m) t = t := by
  constructor
  · rintro ⟨u,rfl⟩
    exact halfFieldEmbedding_fixed n hn m hm hnm u
  · intro ht
    refine ⟨halfFieldEquiv n hn m hm hnm ⟨t, ht⟩, ?_⟩
    exact congrArg Subtype.val ((halfFieldEquiv n hn m hm hnm).symm_apply_apply ⟨t, ht⟩)

/-- The actual entrywise coefficient embedding on root-generated D4 groups. -/
def halfSplitMap (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : 0 < m) (hnm : n = 2*m) :
    SplitGroup (binaryParameters m hm) →* SplitGroup (binaryParameters n hn) :=
  RootPairing.SimpleGeckGroup.map (halfFieldEmbedding n hn m hm hnm)

/-- Entrywise injectivity gives injectivity of the split-group homomorphism. -/
theorem halfSplitMap_injective (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : 0 < m)
    (hnm : n = 2*m) : Function.Injective (halfSplitMap n hn m hm hnm) := by
  intro x y h
  apply Subtype.ext
  apply Units.ext
  ext i j
  apply (halfFieldEmbedding n hn m hm hnm).injective
  exact congrArg (fun z : SplitGroup (binaryParameters n hn) => z.val.val i j) h

/-- The image split matrices are coefficient-fixed. -/
theorem halfSplitMap_fixed (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : 0 < m)
    (hnm : n = 2*m) (x : SplitGroup (binaryParameters m hm)) :
    splitFrobenius n hn (3*m) (halfSplitMap n hn m hm hnm x) =
      halfSplitMap n hn m hm hnm x := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  exact halfFieldEmbedding_fixed n hn m hm hnm (x.val.val i j)
/-- The embedding preserves the pinned diagram action. -/
theorem halfSplitMap_diagram (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : 0 < m)
    (hnm : n = 2*m) (x : SplitGroup (binaryParameters m hm)) :
    halfSplitMap n hn m hm hnm (diagramAutomorphism (binaryParameters m hm) x) =
      diagramAutomorphism (binaryParameters n hn) (halfSplitMap n hn m hm hnm x) :=
  (RootPairing.SimpleGeckGroup.diagramEquiv_map _ _ _ _ x).symm

/-- The smaller defining Frobenius becomes the m-th prime Frobenius. -/
theorem halfSplitMap_frobenius (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : 0 < m)
    (hnm : n = 2*m) (x : SplitGroup (binaryParameters m hm)) :
    halfSplitMap n hn m hm hnm (fieldAutomorphism (binaryParameters m hm) x) =
      splitFrobenius n hn m (halfSplitMap n hn m hm hnm x) := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  exact map_pow (halfFieldEmbedding n hn m hm hnm) (x.val.val i j) (2^m)

/-- Exact compatibility of the smaller defining twist with the larger half twist. -/
theorem halfSplitMap_graphField (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : 0 < m)
    (hnm : n = 2*m) (x : SplitGroup (binaryParameters m hm)) :
    halfSplitMap n hn m hm hnm (graphFieldAutomorphism (binaryParameters m hm) x) =
      diagramAutomorphism (binaryParameters n hn)
        (splitFrobenius n hn m (halfSplitMap n hn m hm hnm x)) :=
  (halfSplitMap_frobenius n hn m hm hnm (diagramAutomorphism (binaryParameters m hm) x)).trans
    ((congrArg (splitFrobenius n hn m) (halfSplitMap_diagram n hn m hm hnm x)).trans
      (RootPairing.SimpleGeckGroup.diagramEquiv_equiv _ _ _ _ _).symm)

end Triality.Standard.EvenField
