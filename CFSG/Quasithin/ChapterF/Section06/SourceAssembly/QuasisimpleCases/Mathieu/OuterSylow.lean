module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.Mathieu.OuterSquare
public import Theory.GroupTheory.SpecificGroups.FiveFour
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.Mathieu.InnerSylow
/-!
# The actual C₄²-by-D₈ common Sylow in Aut(M₁₂)

The marked reflection and outer swap generate a dihedral complement of order
eight. Its intersection with the literal C₄² radical is trivial, and the
known Sylow order makes its map onto the quotient an isomorphism.
Source: Aschbacher–Smith, F.6.18(13), printed p.310, and 14.2.21.
-/

public noncomputable section
open Subgroup
open Sporadic.Mathieu Sporadic.Mathieu.M12ExceptionalExtension
open Sporadic.Mathieu.M12ExceptionalExtension.SecondCoordinates
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Mathieu.OuterSquare
@[expose] def rotationPerm : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 5, 10, 16, 15, 12] * List.formPerm [1, 9, 18, 23, 19, 7] *
  List.formPerm [2, 8, 22, 14, 3, 13] * List.formPerm [4, 17, 20, 21, 11, 6]
@[expose] def reflectionPerm : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 4] * List.formPerm [1, 22] * List.formPerm [2, 18] *
  List.formPerm [3, 19] * List.formPerm [5, 6] * List.formPerm [7, 14] *
  List.formPerm [8, 9] * List.formPerm [10, 11] * List.formPerm [12, 17] *
  List.formPerm [13, 23] * List.formPerm [15, 20] * List.formPerm [16, 21]
set_option maxRecDepth 3000 in
theorem rotationPerm_eq : rotationPerm =
    ((movingActor * rightI * leftI : Carrier) : Equiv.Perm (Fin 24)) := by decide +kernel
set_option maxRecDepth 3000 in
theorem reflectionPerm_eq : reflectionPerm =
    ((rightI * leftJ : Carrier) : Equiv.Perm (Fin 24)) := by decide +kernel
@[expose] def rotation : Carrier :=
  ⟨rotationPerm, rotationPerm_eq ▸ (movingActor * rightI * leftI : Carrier).property⟩
@[expose] def reflection : Carrier :=
  ⟨reflectionPerm, reflectionPerm_eq ▸ (rightI * leftJ : Carrier).property⟩
private theorem map_rotation : innerModel.embedding
    (M12SmallPair.movingActor * M12SmallPair.rightI * M12SmallPair.leftI) = rotation := by
  simp only [map_mul, map_movingActor _ innerModel.embedding_originalA innerModel.embedding_originalB,
    map_rightI _ innerModel.embedding_originalA innerModel.embedding_originalB,
    map_leftI _ innerModel.embedding_originalA innerModel.embedding_originalB]
  exact Subtype.ext rotationPerm_eq.symm
private theorem map_reflection : innerModel.embedding
    (M12SmallPair.rightI * M12SmallPair.leftJ) = reflection := by
  simp only [map_mul, map_rightI _ innerModel.embedding_originalA innerModel.embedding_originalB,
    map_leftJ _ innerModel.embedding_originalA innerModel.embedding_originalB]
  exact Subtype.ext reflectionPerm_eq.symm

theorem rotation_mem : rotation ∈ secondParabolic := by
  rw [← map_rotation]
  change _ ∈ secondParabolic.comap innerModel.embedding
  rw [comap_secondParabolic]
  exact (M12SmallPair.SylowEnumeration.mem_secondParabolic_iff _).mpr (by decide +kernel)
theorem reflection_mem : reflection ∈ overlap := by
  rw [← map_reflection]
  change _ ∈ overlap.comap innerModel.embedding
  rw [comap_overlap]
  exact (M12SmallPair.SylowEnumeration.mem_sylowCandidate_iff _).mpr (by decide +kernel)

private def dihedralValue : DihedralGroup 4 → overlap
  | .r i => ⟨(reflection * swap) ^ i.val,
      overlap.pow_mem (overlap.mul_mem reflection_mem swap_mem_overlap) _⟩
  | .sr i => ⟨swap * (reflection * swap) ^ i.val,
      overlap.mul_mem swap_mem_overlap
        (overlap.pow_mem (overlap.mul_mem reflection_mem swap_mem_overlap) _)⟩
private theorem dihedralValue_mul : ∀ x y : DihedralGroup 4,
    dihedralValue (x*y) = dihedralValue x * dihedralValue y := by decide +kernel
private def dihedralHom : DihedralGroup 4 →* overlap where
  toFun := dihedralValue
  map_one' := by decide +kernel
  map_mul' := dihedralValue_mul
private theorem complement_disjoint : ∀ x : DihedralGroup 4, ∀ i j : Fin 4,
    (dihedralValue x : Carrier) = rootOne ^ i.val * rootTwo ^ j.val → x = 1 := by
  decide +kernel
private def quotientHom : DihedralGroup 4 →* overlap ⧸ sylowRadical :=
  (QuotientGroup.mk' sylowRadical).comp dihedralHom
private theorem quotientHom_injective : Function.Injective quotientHom := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro x hx
  have hm : dihedralHom x ∈ sylowRadical := (QuotientGroup.eq_one_iff _).mp hx
  obtain ⟨i,j,hij⟩ := (mem_radical_iff (dihedralHom x : Carrier)).mp hm
  exact complement_disjoint x i j hij.symm
private theorem sylow_quotient_card : Nat.card (overlap ⧸ sylowRadical) = 8 := by
  have h := sylowRadical.card_mul_index
  rw [sylowRadical_card, card_overlap innerModel] at h
  change sylowRadical.index = 8
  omega

def sylowQuotientEquiv : (overlap ⧸ sylowRadical) ≃* DihedralGroup 4 :=
  (MulEquiv.ofBijective quotientHom
    (quotientHom_injective.bijective_of_nat_card_le (by
      rw [sylow_quotient_card, DihedralGroup.nat_card]))).symm

theorem sylow_extension : ∃ N : Subgroup overlap, ∃ _ : N.Normal,
    Nonempty (N ≃* InnerSquare.C4Square) ∧ Nonempty ((overlap ⧸ N) ≃* DihedralGroup 4) :=
  ⟨sylowRadical, inferInstance, ⟨sylowRadicalEquiv⟩, ⟨sylowQuotientEquiv⟩⟩

end CFSG.Quasithin.ChapterF.SourceAssembly.Mathieu.OuterSquare
