module

public import Theory.SpecificGroups.PSL3.RadicalParabolicTwoSignalizers.Geometry
public import Theory.SpecificGroups.PSL3.RadicalParabolicTwoSignalizers.MarkedRecognition.FlagGeometry
public import Theory.AtlasPort.LinearGroups.SL2Order

/-!
# Recognition of marked parabolic radicals in PSL₃(5)

Let P be a normal subgroup of B ≤ PSL₃(5), with |P| = 25 and an actual
isomorphism B/P ≃ SL₂(5). Then |B| = 3000. Sylow conjugacy places P inside
the upper unitriangular group. If it lies in neither coordinate root plane,
its normalizer preserves the standard flag and has at most 2000 elements,
contradicting the inclusion of B. In either root plane, equality follows
from the order 25. Undoing conjugation identifies the original embedded P.

This proves the requested elementary-kernel recognition and the stronger
version requiring only the order of P. All normality is relative to B;
the conclusion retains P.map B.subtype, rather than an unmarked isomorphism.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 1.3.8, printed p.513, the assertion that P* is a maximal-parabolic
unipotent radical in Y_C* ≃ L₃(5). The two-signalizer and extension arguments
are separate. The imported coordinate and SL₂ order results retain their
ATLAS attribution and license; no new ATLAS source is copied here.
-/

public section

open scoped MatrixGroups
open Subgroup Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3.RootPlaneGeometry
open Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3.RadicalParabolicTwoSignalizers
local notation "F" => ZMod 5

/-- The flag stabilizer over the five-element field has at most 2000 elements. -/
theorem card_borel_five_le : Nat.card (borel F) ≤ 2000 := by
  rw [borel, card_map_of_injective projection_injective]
  have h := card_borelSL_le F
  norm_num only [Nat.card_zmod, Nat.reduceSub, Nat.reducePow, Nat.reduceMul] at h
  exact h

private theorem normalizer_noncoordinate_le_borel (A : Subgroup (U F))
    (h₁ : ¬ A ≤ V₁ F) (h₂ : ¬ A ≤ V₂ F) :
    normalizer (A.map (projective F) : Set Model) ≤ borel F := by
  change normalizer (A.map ((projection F).comp (specialLinear F)) : Set Model) ≤ _
  rw [← Subgroup.map_map, ← (A.map (specialLinear F)).map_normalizer_eq_of_bijective
    ⟨projection_injective, projection_surjective F⟩]
  exact Subgroup.map_mono (normalizer_noncoordinate_le_borelSL F A h₁ h₂)

private theorem eq_rootPlane_of_le_unipotent (Q : Subgroup Model)
    (hQ : Q ≤ unipotent F) (hcard : Nat.card Q = 25)
    (hn : 2000 < Nat.card (normalizer (Q : Set Model))) :
    ∃ point : Bool, Q = rootPlane F point := by
  let A := Q.comap (projective F)
  have hmap : A.map (projective F) = Q :=
    Subgroup.map_comap_eq_self (by rwa [projective_range])
  have root_case (point : Bool) (ha : A ≤ if point then V₁ F else V₂ F) :
      Q = rootPlane F point := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [← hmap, rootPlane_eq_map]
      exact Subgroup.map_mono ha
    · rw [card_rootPlane, hcard]
  by_cases h₁ : A ≤ V₁ F
  · exact ⟨true, root_case true h₁⟩
  by_cases h₂ : A ≤ V₂ F
  · exact ⟨false, root_case false h₂⟩
  have hnorm : normalizer (Q : Set Model) ≤ borel F := by
    rw [← hmap]
    exact normalizer_noncoordinate_le_borel A h₁ h₂
  have hle := (Subgroup.card_le_of_le hnorm).trans card_borel_five_le
  omega

private theorem exists_conjugate_le_unipotent (Q : Subgroup Model)
    (hcard : Nat.card Q = 25) :
    ∃ g : Model, Q.map (MulAut.conj g).toMonoidHom ≤ unipotent F := by
  have hp : IsPGroup 5 Q := IsPGroup.of_card (n := 2) hcard
  have hu : IsPGroup 5 (unipotent F) :=
    IsPGroup.of_card (n := 3) (by rw [card_unipotent, Nat.card_zmod])
  have hi : ¬ 5 ∣ (unipotent F).index := by
    rw [index_unipotent, Nat.card_zmod]
    decide
  let S := hu.toSylow hi
  obtain ⟨T, hT⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Model T S
  refine ⟨g, (Subgroup.map_mono hT).trans_eq ?_⟩
  exact congrArg (fun R : Sylow 5 Model => (R : Subgroup Model)) hg

/-- An order-25 subgroup with normalizer larger than a flag stabilizer is a radical. -/
theorem isParabolicRadical_of_card_normalizer (Q : Subgroup Model)
    (hcard : Nat.card Q = 25) (hn : 2000 < Nat.card (normalizer (Q : Set Model))) :
    IsParabolicRadical Q := by
  obtain ⟨g, hg⟩ := exists_conjugate_le_unipotent Q hcard
  have hc : Nat.card (Q.map (MulAut.conj g).toMonoidHom) = 25 := by
    rw [card_map_of_injective (MulAut.conj g).injective, hcard]
  have hn' : 2000 < Nat.card (normalizer (Q.map (MulAut.conj g).toMonoidHom : Set Model)) := by
    rw [← Subgroup.map_equiv_normalizer_eq, card_map_of_injective (MulAut.conj g).injective]
    exact hn
  obtain ⟨point, he⟩ := eq_rootPlane_of_le_unipotent _ hg hc hn'
  refine ⟨point, g⁻¹, ?_⟩
  rw [← he, Subgroup.map_map]
  have hid : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id Model := by
    ext x
    change g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x
    group
  rw [hid, Subgroup.map_id]

private theorem card_extension (B : Subgroup Model) (P : Subgroup B) [P.Normal]
    (hcard : Nat.card P = 25) (e : (B ⧸ P) ≃* SL(2,F)) :
    Nat.card B = 3000 := by
  have hi : P.index = 120 := by
    change Nat.card (B ⧸ P) = 120
    rw [Nat.card_congr e.toEquiv, Atlas.card_sl_two, Nat.card_zmod]
    decide
  rw [← P.card_mul_index, hcard, hi]

/-- Recognition preserves the specified embedded kernel. Its order suffices;
no assumption of commutativity or of exponent five is needed. -/
theorem markedKernel_isParabolicRadical_of_card
    (B : Subgroup Model) (P : Subgroup B) [P.Normal]
    (hcard : Nat.card P = 25) (quotientEquiv : (B ⧸ P) ≃* SL(2,F)) :
    IsParabolicRadical (P.map B.subtype) := by
  apply isParabolicRadical_of_card_normalizer
  · rw [card_map_of_injective B.subtype_injective, hcard]
  · have hnormal : B ≤ normalizer (P.map B.subtype : Set Model) := by
      simpa only [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype] using P.le_normalizer_map B.subtype
    have hle := Subgroup.card_le_of_le hnormal
    rw [card_extension B P hcard quotientEquiv] at hle
    omega

/-- A marked elementary kernel with actual SL₂(5) quotient is a parabolic radical. -/
theorem markedKernel_isParabolicRadical
    (B : Subgroup Model) (P : Subgroup B) [P.Normal]
    (_helem : IsElementaryAbelian 5 P) (hcard : Nat.card P = 25)
    (quotientEquiv : (B ⧸ P) ≃* SL(2,F)) :
    IsParabolicRadical (P.map B.subtype) :=
  markedKernel_isParabolicRadical_of_card B P hcard quotientEquiv

end Matrix.PSL3.RadicalParabolicTwoSignalizers
