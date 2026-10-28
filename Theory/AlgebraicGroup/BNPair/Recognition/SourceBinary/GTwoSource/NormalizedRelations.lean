module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.PinningRecovery
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.CommonFieldPinning
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.ShortRootModule

/-!
# Complete Borel--Weyl equations for the compatible source pinnings

The middle pairing already constructs a field automorphism and a whole long
rank-one pinning with normalized DC. Use PinningRecovery to obtain local PSL₂
markings whose canonical aligned pinnings are exactly those new pinnings.
The short marking stays fixed. Equality of the six parameter maps, rather
than only of their ranges, transports normalized DC into ShortRootModule.
Its existing algebra then proves the entire positive multiplication table
and all torus, Weyl and rank-one relations on the same quotient.

No equation is assumed beyond the earlier nonvanishing subgroup pairing;
ZeroPairing supplies that pairing at the constructed source orientation.
CommonFieldRecognition makes the actual positive, full marked, original and
geometric applications with the pairing discharged. All finite fields of
characteristic two, including q=2 and q=4, are covered.

Source: Fong--Seitz II (9.13)--(9.21), printed pp.215--217. The left
conjugations and ordered exchanges are exactly the published consumer's.
-/

@[expose] public noncomputable section
open Subgroup Theory.PSL2 Theory.PSL2.SemilinearCoverage
open scoped MatrixGroups commutatorElement
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open RootCoordinates HexagonStructure Atlas.G2.RootPresentationRecognition
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (hK : ∀ i, simpleRemainder Q split i ≤ localKernel Q i)
  (μ : ∀ i, localGroup Q split i ≃* PSL(2,F))
  (n : ∀ i, RootReflection Q split i) (short : Fin 2)
  (hm : rotationOrder Q = 6)
  (hne : ⁅positiveCarrier Q split short 3,positiveCarrier Q split short 2⁆ ≠ ⊥)

local notation "σ" => sourceFieldEquiv Q split hK μ n short hm hne

/-- The short local marking is unchanged; the long marking is induced by the
whole field-relabelled rank-one pinning. -/
def normalizedLocalModels (i : Fin 2) : localGroup Q split i ≃* PSL(2,F) :=
  if i=short then μ i else
    localMarkingOfPinning Q split i (hK i) (μ i)
      ((sl2FieldAut σ).trans (alignedPinning Q split i (hK i) (μ i) (n i)))

@[simp] theorem normalizedLocalModels_short :
    normalizedLocalModels Q split hK μ n short hm hne short = μ short := by
  simp only [normalizedLocalModels,ite_true]

/-- The canonical construction now recovers the entire normalized long pinning. -/
theorem normalizedLocalModels_long_pinning :
    alignedPinning Q split (1-short) (hK (1-short))
      (normalizedLocalModels Q split hK μ n short hm hne (1-short)) (n (1-short)) =
        normalizedLongPinning Q split hK μ n short hm hne := by
  have hneIndex : (1:Fin 2)-short ≠ short := by fin_cases short <;> decide
  rw [normalizedLocalModels,if_neg hneIndex]
  apply alignedPinning_recovers
  · have he : (Unip F).map (sl2FieldAut σ).toMonoidHom = Unip F := by
      ext x
      constructor
      · rintro ⟨g,hg,rfl⟩
        obtain ⟨a,rfl⟩ := (mem_Unip_iff _).mp hg
        exact (mem_Unip_iff _).mpr ⟨σ a,sl2FieldAut_uni σ a⟩
      · intro hx
        obtain ⟨a,rfl⟩ := (mem_Unip_iff _).mp hx
        refine ⟨uni ((σ).symm a),(mem_Unip_iff _).mpr ⟨_,rfl⟩,?_⟩
        simp only [MulEquiv.coe_toMonoidHom,sl2FieldAut_uni,RingEquiv.apply_symm_apply]
    change (Unip F).map ((alignedPinningHom Q split (1-short) (hK (1-short))
      (μ (1-short)) (n (1-short))).comp (sl2FieldAut σ).toMonoidHom) = _
    rw [←map_map,he,alignedPinningHom_unip_map]
  · change alignedPinningHom Q split (1-short) (hK (1-short))
      (μ (1-short)) (n (1-short)) (sl2FieldAut σ (weyl F)) = _
    rw [sl2FieldAut_weyl,alignedPinningHom_weyl]

private theorem normalizedLocalModels_long_hom (g : SL2 F) :
    alignedPinningHom Q split (1-short) (hK (1-short))
      (normalizedLocalModels Q split hK μ n short hm hne (1-short)) (n (1-short)) g =
        normalizedLongPinningHom Q split hK μ n short hm hne g :=
  congrArg (fun p : SL2 F ≃* rankOne Q split (1-short) => (p g : X ⧸ Q.D))
    (normalizedLocalModels_long_pinning Q split hK μ n short hm hne)

/-- Equality of all six maps, not merely their ranges, retains the new field labels. -/
theorem normalizedLocalModels_roots :
    alignedSourceRoots Q split hK (normalizedLocalModels Q split hK μ n short hm hne) n short =
      normalizedSourceRoots Q split hK μ n short hm hne := by
  have hl (a : Multiplicative F) :
      alignedSimpleParameter Q split (1-short) (hK (1-short))
        (normalizedLocalModels Q split hK μ n short hm hne (1-short)) (n (1-short)) a =
      alignedSimpleParameter Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short))
        (.ofAdd (σ a.toAdd)) := by
    change alignedPinningHom Q split (1-short) (hK (1-short))
      (normalizedLocalModels Q split hK μ n short hm hne (1-short)) (n (1-short)) (uni a.toAdd) = _
    rw [normalizedLocalModels_long_hom]
    change alignedPinningHom Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short))
      (sl2FieldAut σ (uni a.toAdd)) = _
    rw [sl2FieldAut_uni]
    rfl
  apply congrArg PositiveRoots.mk
  funext k
  apply MonoidHom.ext
  intro a
  fin_cases k <;>
    simp only [alignedSourceRoots,
      alignedConjugateParameter,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      Fin.reduceFinMk,MonoidHom.comp_apply,normalizedLocalModels_short,hl] <;> rfl

/-- The normalized roots satisfy the entire positive multiplication table. -/
theorem normalizedSourceRoots_relations :
    (normalizedSourceRoots Q split hK μ n short hm hne).CharTwoRelations := by
  rw [←normalizedLocalModels_roots Q split hK μ n short hm hne]
  apply aligned_positive_relations_of_dc Q split hK _ n short hm
  rw [normalizedLocalModels_roots]
  exact normalizedSourceRoots_dc Q split hK μ n short hm hne

/-- Full source torus and Weyl maps constructed from the compatible whole pinnings. -/
def normalizedBorelWeyl : BorelWeylData F (X ⧸ Q.D) :=
  sourceBorelWeyl Q split hK (normalizedLocalModels Q split hK μ n short hm hne) n short split.abelian

theorem normalizedBorelWeyl_roots :
    (normalizedBorelWeyl Q split hK μ n short hm hne).toPositiveRoots =
      normalizedSourceRoots Q split hK μ n short hm hne :=
  normalizedLocalModels_roots Q split hK μ n short hm hne

/-- All positive, torus, Weyl and rank-one equations are now theorems on the
actual quotient, without a polynomial or field-alignment premise. -/
theorem normalizedBorelWeyl_relations :
    (normalizedBorelWeyl Q split hK μ n short hm hne).Relations := by
  apply sourceBorelWeyl_relations_of_dc Q split hK _ n short hm
  rw [normalizedLocalModels_roots]
  exact normalizedSourceRoots_dc Q split hK μ n short hm hne

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
