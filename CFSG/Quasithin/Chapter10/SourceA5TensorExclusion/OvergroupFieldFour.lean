module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OvergroupA7
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SpecialLinearThree
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Symplectic
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2
public import Theory.SpecificGroups.SymplecticFour.Binary.FieldTransport
public import Theory.AtlasPort.LinearGroups.G2.FieldTransport

/-!
# Field-four markings in the tensor overgroup action

A proper local component with an A₅ two-core quotient forces the defining
field to have four elements in each surviving tensor action family. We
transport the given subgroup, full Sylow and quotient marking through the
actual actor equivalence, and apply the proved local-placement theorems.
The single and repeated linear-three rows have the same actor, so both use
the same field-size argument.

The refined selector preserves every original action marking and appends
the field-cardinality theorem. Coefficientwise field transport also gives
the three concrete possible carriers for the same acting component. No
identification with the original component's two-core quotient is made.

Source: Aschbacher–Smith 9.3.7, combined manuscript of 1 March 2004,
printed p.734, using the local embeddings of A.3.14 and the B.5.1 actions.
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.SourceA5TensorExclusion
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings.FiveLocalFF
open ChapterB.QuasisimpleSource ChapterB.SourceInduction.ProjectiveLine
variable {D : Type*} [Group D] [Finite D]

private theorem local_five_equiv_transport {E : Type*} [Group E] [Finite E]
    (a : D ≃* E) (S : Sylow 2 D) (B : Subgroup D)
    (hB : B ∈ localCComponents S) (hp : B ≠ ⊤)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    B.map a.toMonoidHom ∈ localCComponents (S.mapSurjective (f := a.toMonoidHom) a.surjective) ∧
    B.map a.toMonoidHom ≠ ⊤ ∧
    Nonempty (((B.map a.toMonoidHom) ⧸ pCore 2 (B.map a.toMonoidHom)) ≃*
      alternatingGroup (Fin 5)) := by
  let : Group.IsSolvable a.toMonoidHom.ker := by
    rw [a.toMonoidHom.ker_eq_bot_iff.mpr a.injective]
    infer_instance
  refine ⟨Chapter1.Section02.localCComponents_map_of_solvable_ker hB a.toMonoidHom, ?_, ?_⟩
  · intro ht
    apply hp
    apply Subgroup.map_injective (f := a.toMonoidHom) a.injective
    rw [ht,map_top_of_surjective _ a.surjective]
  · let b := a.subgroupMap B
    exact ⟨(QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).symm.trans eB⟩

theorem linear_three_field_four_of_local_five (F : BinaryField)
    (a : D ≃* SL(3,F.Carrier)) (S : Sylow 2 D) (B : Subgroup D)
    (hB : B ∈ localCComponents S) (hp : B ≠ ⊤)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    Nat.card F.Carrier = 4 := by
  obtain ⟨hl,hp,⟨e⟩⟩ := local_five_equiv_transport a S B hB hp eB
  exact (special_linear_three_five_section_placement_all F.card_eq _ _ hl hp e).1

theorem symplectic_field_four_of_local_five (F : BinaryField) (hlarge : 1 < F.degree)
    (a : D ≃* Matrix.symplecticGroup (Fin 2) F.Carrier)
    (S : Sylow 2 D) (B : Subgroup D) (hB : B ∈ localCComponents S) (hp : B ≠ ⊤)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    Nat.card F.Carrier = 4 := by
  obtain ⟨hl,hp,⟨e⟩⟩ := local_five_equiv_transport a S B hB hp eB
  exact (symplectic_five_section_placement F.card_eq hlarge _ _ hl hp e).1

theorem g2_field_four_of_local_five (F : BinaryField) (hlarge : 1 < F.degree)
    (a : D ≃* Atlas.G2.Model F.Carrier)
    (S : Sylow 2 D) (B : Subgroup D) (hB : B ∈ localCComponents S) (hp : B ≠ ⊤)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    Nat.card F.Carrier = 4 := by
  obtain ⟨hl,hp,⟨e⟩⟩ := local_five_equiv_transport a S B hB hp eB
  have hq : 2 < Nat.card F.Carrier := by
    rw [F.card_eq]
    exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
      (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ F.degree))
  exact (G2.five_section_placement hq _ _ hl hp e).1

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The surviving tensor models retain their actual field-four action markings. -/
inductive FourWayFourField (ρ : Representation (ZMod 2) D V) (L : Subgroup D)
    (s : MovedSection ρ L) : Prop
  | linearThree (F : BinaryField) (field_four : Nat.card F.Carrier = 4)
      (faithful : Function.Injective s.action)
      (action : ActionEquiv (s.action.comp L.subtype) (linearNatural F 3))
  | doubleThree (F : BinaryField) (field_four : Nat.card F.Carrier = 4)
      (action : ActionEquiv (s.space.toRepresentation.comp L.subtype)
        (repeated (linearNatural F 3) 2))
  | symplectic (F : BinaryField) (field_four : Nat.card F.Carrier = 4)
      (large : 1 < F.degree) (faithful : Function.Injective s.action)
      (action : ActionEquiv (s.action.comp L.subtype) (binarySymplectic F))
  | g2 (F : BinaryField) (field_four : Nat.card F.Carrier = 4)
      (large : 1 < F.degree) (faithful : Function.Injective s.action)
      (action : ActionEquiv (s.action.comp L.subtype) (binaryG2 F))

omit [Finite D] in
/-- Forgetting the proved field cardinality preserves the earlier action API. -/
theorem FourWayFourField.toFourWay
    {ρ : Representation (ZMod 2) D V} {L : Subgroup D} {s : MovedSection ρ L}
    (h : FourWayFourField ρ L s) : FourWay ρ L s := by
  cases h with
  | linearThree F _ hf a => exact .linearThree F hf a
  | doubleThree F _ a => exact .doubleThree F a
  | symplectic F _ hl hf a => exact .symplectic F hl hf a
  | g2 F _ hl hf a => exact .g2 F hl hf a

theorem fourWayFourField_of_local_five
    (ρ : Representation (ZMod 2) D V) (L : Subgroup D) (s : MovedSection ρ L)
    (h : FourWay ρ L s) (S : Sylow 2 L) (B : Subgroup L)
    (hB : B ∈ localCComponents S) (hp : B ≠ ⊤)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) : FourWayFourField ρ L s := by
  cases h with
  | linearThree F hf a =>
    exact .linearThree F (linear_three_field_four_of_local_five F a.groupEquiv S B hB hp eB) hf a
  | doubleThree F a =>
    exact .doubleThree F (linear_three_field_four_of_local_five F a.groupEquiv S B hB hp eB) a
  | symplectic F hl hf a =>
    exact .symplectic F (symplectic_field_four_of_local_five F hl a.groupEquiv S B hB hp eB) hl hf a
  | g2 F hl hf a =>
    exact .g2 F (g2_field_four_of_local_five F hl a.groupEquiv S B hB hp eB) hl hf a

private def fieldFourEquiv (F : BinaryField) (hF : Nat.card F.Carrier = 4) :
    F.Carrier ≃+* BinaryField.four.Carrier := by
  let := Fintype.ofFinite F.Carrier
  let := Fintype.ofFinite BinaryField.four.Carrier
  apply FiniteField.ringEquivOfCardEq
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF,
    BinaryField.four.card_eq]
  rfl

omit [Finite D] in
/-- The three concrete field-four carriers refer to the same literal actor. -/
theorem FourWayFourField.actor_models
    {ρ : Representation (ZMod 2) D V} {L : Subgroup D} {s : MovedSection ρ L}
    (h : FourWayFourField ρ L s) :
    Nonempty (L ≃* SL(3,BinaryField.four.Carrier)) ∨
    Nonempty (L ≃* Matrix.symplecticGroup (Fin 2) BinaryField.four.Carrier) ∨
    Nonempty (L ≃* Atlas.G2.Model BinaryField.four.Carrier) := by
  cases h with
  | linearThree F hc _ a =>
    exact Or.inl ⟨a.groupEquiv.trans (Atlas.fieldEquivSL 3 (fieldFourEquiv F hc))⟩
  | doubleThree F hc a =>
    exact Or.inl ⟨a.groupEquiv.trans (Atlas.fieldEquivSL 3 (fieldFourEquiv F hc))⟩
  | symplectic F hc _ _ a =>
    exact Or.inr (Or.inl ⟨a.groupEquiv.trans
      (Theory.SpecificGroups.SymplecticFour.Binary.fieldEquivSp (fieldFourEquiv F hc))⟩)
  | g2 F hc _ _ a =>
    exact Or.inr (Or.inr ⟨a.groupEquiv.trans (Atlas.G2.fieldEquiv (fieldFourEquiv F hc))⟩)
end CFSG.Quasithin.Chapter10.SourceA5TensorExclusion
