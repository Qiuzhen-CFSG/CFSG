module
public import CFSG.Quasithin.ChapterF.Section01.SourceIncidence
public import CFSG.Quasithin.ChapterF.Section01.SourceLocalSylow
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.HallJanko.Assembly
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourExtension.BinaryOrders
public import Theory.Quasithin

/-!
# The numerical part of the mixed A5/S3 recognition argument

The whole common Borel in the concrete U4(2), J2 and Aut(J2) models has
order 192, 384 or 768. We also allow the binary unitary degree-two
extension, whose Borel has order 384: eliminating this additional model
is unnecessary for the bound. An actual isomorphism to any of these
Borels therefore determines its Sylow order as 64, 128 or 256.

The corrected F.1.1 hypotheses make the original S Sylow in the common
Borel. This transfers the concrete calculation without identifying the
ambient generated group, making the overlap itself a two-group, or
requiring S to lie in either local factor. The S3 quotient also identifies
its local Borel with the local Sylow intersection.

`MixedA5S3BorelRecognition` is the remaining structural recognition
obligation. It asserts an actual isomorphism of the original common Borel;
the definition and the numerical implication do not prove that obligation.
Parabolic isomorphisms from the source alternatives would suffice, using
only their middle components.

Source: Aschbacher--Smith, F.1.12(I), printed pp.262--264, and its
application in original 9.3.1, printed p.732 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source
open GreenBook

/-- Actual middle-group isomorphisms sufficient for the mixed size consequence. -/
inductive MixedBorelModel (B : Type*) [Group B] : Prop
  | unitary (iso : Nonempty (B ≃* LieModels.UnitaryFour.overlap 1 (by decide)))
  | unitaryExtension
      (iso : Nonempty (B ≃* LieModels.UnitaryFour.Extension.overlap 1 (by decide)))
  | hallJanko (iso : Nonempty (B ≃* HallJanko.j2Model.toMarking.B))
  | hallJankoAut (iso : Nonempty (B ≃* HallJanko.autJ2Model.toMarking.B))

/-- The odd part of the whole Borel is retained in each concrete order. -/
theorem MixedBorelModel.card {B : Type*} [Group B] (h : MixedBorelModel B) :
    Nat.card B = 192 ∨ Nat.card B = 384 ∨ Nat.card B = 768 := by
  cases h with
  | unitary e =>
    exact Or.inl ((Nat.card_congr e.some.toEquiv).trans
      LieModels.UnitaryFour.BinaryCompletion.middle_card)
  | unitaryExtension e =>
    exact Or.inr (Or.inl ((Nat.card_congr e.some.toEquiv).trans
      LieModels.UnitaryFour.Extension.binary_overlap_card))
  | hallJanko e =>
    exact Or.inr (Or.inl ((Nat.card_congr e.some.toEquiv).trans HallJanko.card_j2Model_B))
  | hallJankoAut e =>
    exact Or.inr (Or.inr ((Nat.card_congr e.some.toEquiv).trans HallJanko.card_autJ2Model_B))

variable {G : Type*} [Group G] [Finite G]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Transport the source Sylow witness under the literal inclusion of the Borel. -/
theorem HypothesisF11.sylow_card_eq_twoPart_commonBorel (h : HypothesisF11 L S) :
    Nat.card S = 2 ^ (Nat.card (commonBorel L S)).factorization 2 := by
  obtain ⟨P, hP⟩ := h.sylow_commonBorel
  calc
    Nat.card S = Nat.card P :=
      (congrArg (fun A : Subgroup G => Nat.card A) hP).symm.trans
        (card_map_of_injective (commonBorel L S).subtype_injective)
    _ = _ := P.card_eq_multiplicity

/-- All possible Sylow orders after the structural Borel recognition. -/
theorem HypothesisF11.sylow_card_of_mixedBorelModel (h : HypothesisF11 L S)
    (hm : MixedBorelModel (commonBorel L S)) :
    Nat.card S = 64 ∨ Nat.card S = 128 ∨ Nat.card S = 256 := by
  have hf (n : ℕ) : (2 ^ n * 3).factorization 2 = n := by
    rw [Nat.factorization_mul (pow_ne_zero _ (by decide)) (by decide),
      Nat.factorization_pow]
    simp [Nat.prime_two.factorization, Nat.prime_three.factorization]
  rw [h.sylow_card_eq_twoPart_commonBorel]
  rcases hm.card with hc | hc | hc
  · rw [hc, show 192 = 2 ^ 6 * 3 by norm_num, hf]
    norm_num
  · rw [hc, show 384 = 2 ^ 7 * 3 by norm_num, hf]
    norm_num
  · rw [hc, show 768 = 2 ^ 8 * 3 by norm_num, hf]
    norm_num

/-- The numerical consequence; obtaining the model is a separate source proof. -/
theorem HypothesisF11.sylow_card_le_of_mixedBorelModel (h : HypothesisF11 L S)
    (hm : MixedBorelModel (commonBorel L S)) : Nat.card S ≤ 256 := by
  rcases h.sylow_card_of_mixedBorelModel hm with hc | hc | hc <;> omega

/-- The full S need not lie in the cubic local factor. -/
theorem HypothesisF11.cubic_borel_eq_localSylow (h : HypothesisF11 L S) (i : Fin 2)
    (e : (L i ⧸ pCore 2 (L i)) ≃* Equiv.Perm (Fin 3)) :
    borel (L i) S = S ⊓ L i := by
  have he := borel_eq_of_cubic_local_sylow (L i) (S ⊓ L i) (h.sylow i) e
  simpa only [borel, inf_assoc, inf_idem] using he

/-- The normalized-Borel hypothesis of F.1.12 is automatic at the cubic endpoint. -/
theorem HypothesisF11.cubic_borel_normalizes_S (h : HypothesisF11 L S) (i : Fin 2)
    (e : (L i ⧸ pCore 2 (L i)) ≃* Equiv.Perm (Fin 3)) :
    borel (L i) S ≤ normalizer (S : Set G) := by
  rw [h.cubic_borel_eq_localSylow i e]
  exact inf_le_left.trans S.le_normalizer

/-- The cubic Borel contributes no additional factor beyond the original S. -/
theorem HypothesisF11.commonBorel_eq_of_cubic_second {K U : Subgroup G}
    (h : HypothesisF11 ![K,U] S)
    (e : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) :
    commonBorel ![K,U] S = borel K S ⊔ S := by
  have hb : borel U S = S ⊓ U := h.cubic_borel_eq_localSylow 1 e
  change borel K S ⊔ borel U S ⊔ S = _
  rw [hb, sup_assoc, show S ⊓ U ⊔ S = S from sup_eq_right.mpr inf_le_left]

/-- Structural recognition still required for the mixed F.1.12 consequence.
All original hypotheses are retained, including Sylow placement in the
literal generated subgroup. This is an input contract, not a theorem. -/
@[expose] def MixedA5S3BorelRecognition (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ (K U S : Subgroup G), HypothesisF11 ![K,U] S →
    IsQuasithin (generated ![K,U] S) →
    Chapter1.IsSylowIn 2 S (generated ![K,U] S) →
    Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) →
    Nonempty ((U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) →
    borel U S ≤ normalizer (S : Set G) →
    MixedBorelModel (commonBorel ![K,U] S)

end CFSG.Quasithin.ChapterF.Source
