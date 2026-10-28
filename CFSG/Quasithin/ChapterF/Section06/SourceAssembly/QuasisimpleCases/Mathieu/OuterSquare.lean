module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.Mathieu.InnerSquare
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.Amalgam

/-!
# The common square radical in the outer Mathieu amalgam

The marked inner C₄² subgroup remains normal in the actual outer second
parabolic. The only additional conjugation is the explicit outer swap;
on its two generators it acts by (a,b) ↦ (a³b²,a²b). This retains the literal
embedded radical and its inclusion in the common Sylow subgroup.

Source: Aschbacher–Smith, F.6.18(13), printed p.310, and 14.2.21.
-/

public noncomputable section
open Subgroup
open Sporadic.Mathieu Sporadic.Mathieu.M12ExceptionalExtension
open Sporadic.Mathieu.M12ExceptionalExtension.SecondCoordinates
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Mathieu.OuterSquare

@[expose] def rootOne : Carrier := markedRightJ
@[expose] def rootTwoPerm : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 16, 4, 21] * List.formPerm [1, 2, 14, 23] *
  List.formPerm [3, 8, 9, 19] * List.formPerm [6, 20, 12, 10] *
  List.formPerm [7, 22] * List.formPerm [13, 18]
set_option maxRecDepth 3000 in
theorem rootTwoPerm_eq : rootTwoPerm =
    ((leftI * (movingActor * leftI * movingActor) : Carrier) : Equiv.Perm (Fin 24)) := by
  decide +kernel
@[expose] def rootTwo : Carrier :=
  ⟨rootTwoPerm, rootTwoPerm_eq ▸ (leftI * (movingActor * leftI * movingActor) : Carrier).property⟩

private theorem map_rootOne : innerModel.embedding M12SmallPair.SecondSquareControl.rootOne =
    rootOne := by
  have h : M12SmallPair.SecondSquareControl.rootOne = M12SmallPair.rightJ := by
    decide +kernel
  rw [h, map_rightJ _ innerModel.embedding_originalA innerModel.embedding_originalB]
  exact Subtype.ext rightJPerm_eq.symm
private theorem map_rootTwo : innerModel.embedding M12SmallPair.SecondSquareControl.rootTwo =
    rootTwo := by
  simp only [M12SmallPair.SecondSquareControl.rootTwo, map_mul,
    map_movingActor _ innerModel.embedding_originalA innerModel.embedding_originalB,
    map_leftI _ innerModel.embedding_originalA innerModel.embedding_originalB]
  exact Subtype.ext rootTwoPerm_eq.symm

@[expose] def radical : Subgroup Carrier :=
  M12SmallPair.SecondSquareControl.radical.map innerModel.embedding

theorem radical_eq_closure : radical = closure ({rootOne, rootTwo} : Set Carrier) := by
  rw [radical, M12SmallPair.SecondSquareControl.radical, MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton, map_rootOne, map_rootTwo]

def radicalEquiv : radical ≃* InnerSquare.C4Square :=
  (M12SmallPair.SecondSquareControl.radical.equivMapOfInjective _
    innerModel.embedding_injective).symm.trans InnerSquare.radicalEquiv

theorem radical_card : Nat.card radical = 16 := by
  rw [Nat.card_congr radicalEquiv.toEquiv]
  simp [InnerSquare.C4Square, Nat.card_eq_fintype_card]

theorem radical_le_overlap : radical ≤ overlap := by
  rw [radical, map_le_iff_le_comap, comap_overlap]
  exact M12SmallPair.SecondSquareControl.radical_le_sylow

theorem mem_radical_iff (x : Carrier) : x ∈ radical ↔
    ∃ i j : Fin 4, rootOne ^ i.val * rootTwo ^ j.val = x := by
  constructor
  · rintro ⟨y,hy,rfl⟩
    obtain ⟨i,j,rfl⟩ := (InnerSquare.mem_radical_iff y).mp hy
    exact ⟨i,j,by simp only [map_mul,map_pow,map_rootOne,map_rootTwo]⟩
  · rintro ⟨i,j,rfl⟩
    rw [radical_eq_closure]
    exact mul_mem (pow_mem (subset_closure (by simp)) _) (pow_mem (subset_closure (by simp)) _)

private theorem swap_rootOne : swap * rootOne * swap⁻¹ = rootOne ^ 3 * rootTwo ^ 2 := by
  apply Subtype.ext
  decide +kernel
private theorem swap_rootTwo : swap * rootTwo * swap⁻¹ = rootOne ^ 2 * rootTwo := by
  apply Subtype.ext
  decide +kernel

attribute [local irreducible] rootOne rootTwo

private theorem swap_normalizes : swap ∈ normalizer (radical : Set Carrier) := by
  have h : radical.map (MulAut.conj swap).toMonoidHom ≤ radical := by
    rw [radical_eq_closure, MonoidHom.map_closure]
    apply (closure_le _).mpr
    rintro y ⟨x,hx,rfl⟩
    rcases hx with rfl | rfl
    · have he : (MulAut.conj swap).toMonoidHom rootOne = rootOne ^ 3 * rootTwo ^ 2 :=
        swap_rootOne
      rw [he]
      exact mul_mem (pow_mem (subset_closure (by simp)) _) (pow_mem (subset_closure (by simp)) _)
    · have he : (MulAut.conj swap).toMonoidHom rootTwo = rootOne ^ 2 * rootTwo :=
        swap_rootTwo
      rw [he]
      exact mul_mem (pow_mem (subset_closure (by simp)) _) (subset_closure (by simp))
  exact mem_normalizer_fintype (fun x hx => h ⟨x,hx,rfl⟩)

theorem swap_mem_overlap : swap ∈ overlap := by
  have h := movement_mem_overlap QuaternionSwapModel.swap
  rwa [movement_swap] at h

/-- The inner second vertex and the marked outer involution generate the actual vertex. -/
theorem second_le_of_inner_swap (N : Subgroup Carrier)
    (hi : M12ExceptionalExtension.inner ⊓ secondParabolic ≤ N) (hs : swap ∈ N) :
    secondParabolic ≤ N := by
  intro g hg
  by_cases hgi : g ∈ M12ExceptionalExtension.inner
  · exact hi ⟨hgi,hg⟩
  · have hx : g * swap⁻¹ ∈ M12ExceptionalExtension.inner :=
      (M12ExceptionalExtension.inner.mul_mem_iff_of_index_two innerModel.index).mpr (by
        simp only [hgi, Subgroup.inv_mem_iff, swap_not_inner])
    have hn := N.mul_mem (hi ⟨hx, secondParabolic.mul_mem hg
      (secondParabolic.inv_mem swap_mem_overlap.2)⟩) hs
    simpa only [inv_mul_cancel_right] using hn

theorem second_normalizes_radical : secondParabolic ≤ normalizer (radical : Set Carrier) := by
  apply second_le_of_inner_swap _ _ swap_normalizes
  have hinner : M12ExceptionalExtension.inner ⊓ secondParabolic =
      M12SmallPair.secondParabolic.map innerModel.embedding := by
    rw [← comap_secondParabolic innerModel, map_comap_eq, innerModel.embedding_range, inf_comm]
  rw [hinner]
  exact (map_mono (le_normalizer_of_normal_subgroupOf
    (M12SmallPair.SecondSquareControl.radical_le_sylow.trans inf_le_right))).trans
      (le_normalizer_map innerModel.embedding)

@[expose] def localRadical : Subgroup secondParabolic := radical.subgroupOf secondParabolic
instance : localRadical.Normal :=
  normal_subgroupOf_of_le_normalizer second_normalizes_radical

def localRadicalEquiv : localRadical ≃* InnerSquare.C4Square :=
  (subgroupOfEquivOfLe (radical_le_overlap.trans inf_le_right)).trans radicalEquiv

theorem localRadical_card : Nat.card localRadical = 16 := by
  rw [Nat.card_congr localRadicalEquiv.toEquiv]
  simp [InnerSquare.C4Square, Nat.card_eq_fintype_card]

@[expose] def sylowRadical : Subgroup overlap := radical.subgroupOf overlap
instance : sylowRadical.Normal :=
  normal_subgroupOf_of_le_normalizer (inf_le_right.trans second_normalizes_radical)

def sylowRadicalEquiv : sylowRadical ≃* InnerSquare.C4Square :=
  (subgroupOfEquivOfLe radical_le_overlap).trans radicalEquiv

theorem sylowRadical_card : Nat.card sylowRadical = 16 := by
  rw [Nat.card_congr sylowRadicalEquiv.toEquiv]
  simp [InnerSquare.C4Square, Nat.card_eq_fintype_card]

end CFSG.Quasithin.ChapterF.SourceAssembly.Mathieu.OuterSquare
