module

public import Theory.Representation.Triality.BinaryDegree.CarrierTransport.RootComparison
public import Theory.AlgebraicGroup.RootSystems.EvenOrthogonalElementaryGeneration.Symmetries

/-!
# Root words over a specified coefficient subfield

The coordinate-root closure retains the coefficient subfield in every generator.
Weyl conjugation uses only the parameters 1 and -1, and therefore reduces all
rational D4 roots to the eight literal simple Spin curves without enlarging the
field. Faithfulness of the natural action transfers membership back to Spin.

Sources: GLS3, §§1.10–1.12 and Remarks 2.2.5, with the coordinate matrices of §2.7.
-/

@[expose] public section
noncomputable section

namespace Theory.AlgebraicGroup.RationalOrthogonal
open StandardRootSystem
variable {k : Type*} [Field k]

/-- All eight coordinates lie in the specified coefficient field. -/
def HasCoordinates (F : Subfield k) (v : HyperbolicSpace k 4) : Prop :=
  (∀ i, v.1 i ∈ F) ∧ (∀ i, v.2 i ∈ F)

/-- The closure of the literal orthogonal root matrices with coefficients in `F`. -/
def rootSubgroup (F : Subfield k) :
    Subgroup (quadraticIsometrySubgroup (hyperbolicForm (k := k) 4)) :=
  Subgroup.closure (Set.range fun p : TypeDRootIndex 4 × F =>
    evenOrthogonalRootQuadraticPoint 4 p.1 (p.2 : k))

theorem root_mem (F : Subfield k) (r : TypeDRootIndex 4) {a : k} (ha : a ∈ F) :
    evenOrthogonalRootQuadraticPoint 4 r a ∈ rootSubgroup F :=
  Subgroup.subset_closure ⟨(r, ⟨a, ha⟩), rfl⟩

end Theory.AlgebraicGroup.RationalOrthogonal

namespace Triality.BinaryDegree.CarrierTransport
open Triality.Standard Triality.SimplyConnected Triality.SimplyConnected.Pinning
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem

variable {k : Type*} [Field k] [IsAlgClosed k] [CharP k 2]
variable {n : ℕ} {hn : 0 < n}
variable (f : ExtensionField (binaryParameters n hn) →+* k)

theorem positiveSimplePoint_mem_rational (i : Fin 4)
    (a : ExtensionField (binaryParameters n hn)) :
    positiveSimplePoint k i (f a) ∈ rationalSimpleSubgroup f :=
  Subgroup.subset_closure (Or.inl ⟨(i, a), rfl⟩)

theorem negativeSimplePoint_mem_rational (i : Fin 4)
    (a : ExtensionField (binaryParameters n hn)) :
    negativeSimplePoint k i (f a) ∈ rationalSimpleSubgroup f :=
  Subgroup.subset_closure (Or.inr ⟨(i, a), rfl⟩)

private theorem simpleNormalizer_mem_rational (i : Fin 4) :
    simpleNormalizer k i ∈ rationalSimpleSubgroup f := by
  have hp : positiveSimplePoint k i 1 ∈ rationalSimpleSubgroup f := by
    simpa only [map_one] using positiveSimplePoint_mem_rational f i 1
  have hm : negativeSimplePoint k i (-1) ∈ rationalSimpleSubgroup f := by
    simpa only [map_neg, map_one] using negativeSimplePoint_mem_rational f i (-1)
  simpa only [simpleNormalizer, normalizerWord, Units.val_one, inv_one] using
    (rationalSimpleSubgroup f).mul_mem ((rationalSimpleSubgroup f).mul_mem hp hm) hp

/-- Weyl conjugation preserves the coefficient field in every root word. -/
theorem rootPoint_mem_rational (r : RootIndex)
    (a : ExtensionField (binaryParameters n hn)) :
    rootPoint k r (f a) ∈ rationalSimpleSubgroup f := by
  have h : (∀ a, rootPoint k r (f a) ∈ rationalSimpleSubgroup f) ∧
      (∀ a, rootPoint k (negativeRoot r) (f a) ∈ rationalSimpleSubgroup f) := by
    apply (typeDRootPairing_base 2).induction_reflect r
    · intro s hs
      simpa only [reflection_self_negativeRoot, negativeRoot_negativeRoot] using hs.symm
    · intro s hs
      obtain ⟨i, hi⟩ := (typeDRootPairing_baseEquiv 2).surjective ⟨s, hs⟩
      have his : simpleRoot i = s := congrArg Subtype.val hi
      rw [← his]
      exact ⟨positiveSimplePoint_mem_rational f i, negativeSimplePoint_mem_rational f i⟩
    · intro s j hs hj
      obtain ⟨i, hi⟩ := (typeDRootPairing_baseEquiv 2).surjective ⟨j, hj⟩
      have hij : simpleRoot i = j := congrArg Subtype.val hi
      rw [← hij]
      have hconj (s : RootIndex) (a : ExtensionField (binaryParameters n hn))
          (ha : rootPoint k s (f a) ∈ rationalSimpleSubgroup f) :
          rootPoint k ((typeDRootPairing 2).reflectionPerm (simpleRoot i) s) (f a) ∈
            rationalSimpleSubgroup f := by
        rw [← simpleNormalizer_rootPoint_conjugation]
        exact (rationalSimpleSubgroup f).mul_mem
          ((rationalSimpleSubgroup f).mul_mem
            ((rationalSimpleSubgroup f).inv_mem (simpleNormalizer_mem_rational f i)) ha)
          (simpleNormalizer_mem_rational f i)
      refine ⟨fun a => hconj s a (hs.1 a), fun a => ?_⟩
      rw [← reflection_negativeRoot]
      exact hconj (negativeRoot s) a (hs.2 a)
  exact h.1 a

/-- The natural image is exactly the orthogonal closure with the same parameters. -/
theorem rationalSimpleSubgroup_map_naturalAction :
    (rationalSimpleSubgroup f).map (naturalAction k) =
      RationalOrthogonal.rootSubgroup f.fieldRange := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    apply (Subgroup.closure_le _).mpr
    rintro g (⟨⟨i, t⟩, rfl⟩ | ⟨⟨i, t⟩, rfl⟩)
    all_goals
      change naturalAction k (rootPoint k _ (f t)) ∈
        RationalOrthogonal.rootSubgroup f.fieldRange
      rw [naturalAction_rootPoint]
      exact RationalOrthogonal.root_mem _ _ (f.mem_fieldRange_self t)
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨⟨r, a⟩, rfl⟩
    obtain ⟨t, ht⟩ := a.property
    refine ⟨rootPoint k r (f t), rootPoint_mem_rational f r t, ?_⟩
    rw [naturalAction_rootPoint, ht]

/-- Rational coordinate-root generation lifts through the faithful Spin action. -/
theorem mem_rationalSimpleSubgroup_iff (g : Points k) :
    g ∈ rationalSimpleSubgroup f ↔
      naturalAction k g ∈ RationalOrthogonal.rootSubgroup f.fieldRange := by
  rw [← rationalSimpleSubgroup_map_naturalAction]
  constructor
  · intro hg
    exact ⟨g, hg, rfl⟩
  · rintro ⟨h, hh, he⟩
    exact naturalAction_injective k he ▸ hh

end Triality.BinaryDegree.CarrierTransport
