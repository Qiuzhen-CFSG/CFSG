module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.ReflectionPinning
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.PositiveCoordinates
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.WeylCoefficient

/-!
# Source positive roots from reflection-aligned rank-one pinnings

Use the actual source reflections as the Weyl images of both whole SL₂
pinnings. Transport their upper root maps along the same source lifts to
obtain the six A--F maps. The source root ranges, positive generation and
highest-root nontriviality hold for every finite field of characteristic two.
The short rank-one word and the two transported root orbits now require no
additional pinning-alignment premise.

The orthogonal-root centralizer and lower module/commutator equations remain
explicit inputs. They are the still-unproved source steps in Fong--Seitz II
(9.2)--(9.15), printed pp.211--216, including the separate binary branch.
The conclusion is conditional positive collection, not full source recognition.
The literal original/geometric consumer is ReflectionApplication.
-/

@[expose] public noncomputable section
open Subgroup Theory.PSL2.SemilinearCoverage
open scoped MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open RootCoordinates HexagonStructure Atlas.G2.RootPresentationRecognition
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- Right-conjugate the simple-root map of the whole aligned pinning. -/
def alignedConjugateParameter (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) (n : RootReflection Q split i) (v : Q.tits.N) :
    Multiplicative F →* X ⧸ Q.D :=
  (MulAut.conj (v : X ⧸ Q.D)⁻¹).toMonoidHom.comp (alignedSimpleParameter Q split i hV μ n)

theorem alignedConjugateParameter_range (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) (n : RootReflection Q split i)
    (w : Weyl Q) (v : Q.tits.N)
    (hv : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) v = w) :
    (alignedConjugateParameter Q split i hV μ n v).range = rootAt Q split i w := by
  rw [alignedConjugateParameter, MonoidHom.range_comp, alignedSimpleParameter_range,
    rootAt_eq Q split i w v hv, rightConjugate, comap_equiv_eq_map_symm',map_inv]
  rfl

theorem alignedConjugateParameter_injective (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) (n : RootReflection Q split i) (v : Q.tits.N) :
    Function.Injective (alignedConjugateParameter Q split i hV μ n v) :=
  (MulAut.conj (v : X ⧸ Q.D)⁻¹).injective.comp
    (alignedSimpleParameter_injective Q split i hV μ n)

variable (hK : ∀ i, simpleRemainder Q split i ≤ localKernel Q i)
  (μ : ∀ i, localGroup Q split i ≃* PSL(2,F))
  (n : ∀ i, RootReflection Q split i) (short : Fin 2)

/-- All six root maps use the two entire reflection-aligned source pinnings. -/
def alignedSourceRoots : PositiveRoots F (X ⧸ Q.D) where
  root :=
    let long := 1-short
    ![alignedConjugateParameter Q split long (hK long) (μ long) (n long)
        ((n short).val * (n long).val),
      alignedConjugateParameter Q split long (hK long) (μ long) (n long) (n short).val,
      alignedConjugateParameter Q split short (hK short) (μ short) (n short)
        ((n long).val * (n short).val),
      alignedConjugateParameter Q split short (hK short) (μ short) (n short) (n long).val,
      alignedSimpleParameter Q split long (hK long) (μ long) (n long),
      alignedSimpleParameter Q split short (hK short) (μ short) (n short)]

theorem alignedSourceRoots_range (k : Fin 6) :
    ((alignedSourceRoots Q split hK μ n short).root k).range = positiveCarrier Q split short k := by
  have hprod (i j : Fin 2) :
      QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N)
        ((n i).val*(n j).val) = Q.simple i*Q.simple j := by
    rw [map_mul, (n i).class_eq, (n j).class_eq]
  fin_cases k
  · exact alignedConjugateParameter_range Q split _ _ _ _ _ _ (hprod _ _)
  · exact alignedConjugateParameter_range Q split _ _ _ _ _ _ (n short).class_eq
  · exact alignedConjugateParameter_range Q split _ _ _ _ _ _ (hprod _ _)
  · exact alignedConjugateParameter_range Q split _ _ _ _ _ _ (n (1-short)).class_eq
  · exact alignedSimpleParameter_range Q split _ _ _ _
  · exact alignedSimpleParameter_range Q split _ _ _ _

theorem alignedSourceRoots_injective (k : Fin 6) :
    Function.Injective ((alignedSourceRoots Q split hK μ n short).root k) := by
  fin_cases k
  · exact alignedConjugateParameter_injective Q split _ _ _ _ _
  · exact alignedConjugateParameter_injective Q split _ _ _ _ _
  · exact alignedConjugateParameter_injective Q split _ _ _ _ _
  · exact alignedConjugateParameter_injective Q split _ _ _ _ _
  · exact alignedSimpleParameter_injective Q split _ _ _ _
  · exact alignedSimpleParameter_injective Q split _ _ _ _

theorem alignedSourceRoots_generated (hm : rotationOrder Q = 6) :
    (alignedSourceRoots Q split hK μ n short).generated = split.U :=
  positive_generated_of_ranges Q split hm short _ (alignedSourceRoots_range Q split hK μ n short)

theorem alignedSourceRoots_highest_nontrivial :
    (alignedSourceRoots Q split hK μ n short).x 0 1 ≠ 1 := by
  intro h
  have he : (alignedSourceRoots Q split hK μ n short).root 0 (Multiplicative.ofAdd 1) =
      (alignedSourceRoots Q split hK μ n short).root 0 (Multiplicative.ofAdd 0) := by
    simpa only [PositiveRoots.x_zero] using h
  exact one_ne_zero (Multiplicative.ofAdd.injective
    (alignedSourceRoots_injective Q split hK μ n short 0 he))

variable (hc : rankOne Q split short ≤ centralizer (positiveCarrier Q split short 0 : Set (X ⧸ Q.D)))

/-- The short rank-one data are constructed with the specified source reflection.
Only its orthogonal-root centralization is still a source premise. -/
def alignedShortRankOne : ShortRankOneData (alignedSourceRoots Q split hK μ n short) where
  hom := alignedPinningHom Q split short (hK short) (μ short) (n short)
  root a := rfl
  fixes_highest a := by
    have ha : (alignedSourceRoots Q split hK μ n short).x 0 a ∈ positiveCarrier Q split short 0 := by
      rw [← alignedSourceRoots_range Q split hK μ n short 0]
      exact ⟨.ofAdd a,rfl⟩
    have hcomm := mem_centralizer_iff.mp (hc (n short).mem_rankOne) _ ha
    change MulAut.conj (alignedPinningHom Q split short (hK short) (μ short) (n short) (weyl F))
      ((alignedSourceRoots Q split hK μ n short).x 0 a) = _
    rw [alignedPinningHom_weyl,MulAut.conj_apply,← hcomm,mul_assoc,mul_inv_cancel,mul_one]
  long_orbit a := by
    have hinv : ((n short).val : X ⧸ Q.D)⁻¹ = (n short).val :=
      inv_eq_of_mul_eq_one_right (sourceReflection_sq Q split short (hK short) (μ short) (n short))
    change MulAut.conj (alignedPinningHom Q split short (hK short) (μ short) (n short) (weyl F))
      (alignedSimpleParameter Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) (.ofAdd a)) =
      MulAut.conj ((n short).val : X ⧸ Q.D)⁻¹
        (alignedSimpleParameter Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) (.ofAdd a))
    rw [alignedPinningHom_weyl,hinv]
  middle_orbit a := by
    have hinv : ((n short).val : X ⧸ Q.D)⁻¹ = (n short).val :=
      inv_eq_of_mul_eq_one_right (sourceReflection_sq Q split short (hK short) (μ short) (n short))
    change MulAut.conj (alignedPinningHom Q split short (hK short) (μ short) (n short) (weyl F))
      (MulAut.conj ((n (1-short)).val : X ⧸ Q.D)⁻¹
        (alignedSimpleParameter Q split short (hK short) (μ short) (n short) (.ofAdd a))) =
      MulAut.conj (((n (1-short)).val : X ⧸ Q.D) * (n short).val)⁻¹
        (alignedSimpleParameter Q split short (hK short) (μ short) (n short) (.ofAdd a))
    rw [alignedPinningHom_weyl]
    simp only [MulAut.conj_apply,mul_inv_rev,inv_inv,hinv]
    group

include hc in
/-- The lower equations imply the full positive table for the constructed roots,
including q=2 and q=4, without a Weyl-alignment assumption. -/
theorem aligned_positive_relations
    (d : PartialPositiveData (alignedSourceRoots Q split hK μ n short)) :
    (alignedSourceRoots Q split hK μ n short).CharTwoRelations :=
  d.relations_of_short_rankOne (alignedShortRankOne Q split hK μ n short hc)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
