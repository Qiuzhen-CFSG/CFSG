module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceSylow
public import Theory.SpecificGroups.PSL5Two.UniversalCover.Faithfulness.RootCalculus
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.ElementaryAbelian.Injective
import Mathlib.Tactic.FinCases

/-!
# The marked flag Sylow and its elementary rectangular subgroups

Collect the ten positive binary roots in descending row order. Their matrices
have no cross terms, so their entries exhibit every unitriangular element as
a root word. The existing binary Steinberg relations show that conjugation
by a positive root preserves each rectangular root group. They also show
that the rectangle generators commute and are involutions.

Transport through the original marking places the two elementary rectangular
groups normally in the same ambient Sylow. This supplies the relative
normality and elementary-abelian assertions in Aschbacher, *Sporadic Groups*
(1994), 39.1(3), printed p.213, with the Sylow promotion of 39.2.
Maximality among elementary subgroups, fusion control in 39.6, and the
40.3–41.4 source comparison remain separate assertions.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear
open Theory.SpecificGroups.LinearSylowNormalizers
private abbrev trans {i j : Fin 5} (h : i < j) (a : ZMod 2) : SL :=
  Matrix.SpecialLinearGroup.transvection (ne_of_lt h) a

private def upperWord (A : Matrix (Fin 5) (Fin 5) (ZMod 2)) : SL :=
  trans (by decide : (3 : Fin 5) < 4) (A 3 4) *
  trans (by decide : (2 : Fin 5) < 3) (A 2 3) *
  trans (by decide : (2 : Fin 5) < 4) (A 2 4) *
  trans (by decide : (1 : Fin 5) < 2) (A 1 2) *
  trans (by decide : (1 : Fin 5) < 3) (A 1 3) *
  trans (by decide : (1 : Fin 5) < 4) (A 1 4) *
  trans (by decide : (0 : Fin 5) < 1) (A 0 1) *
  trans (by decide : (0 : Fin 5) < 2) (A 0 2) *
  trans (by decide : (0 : Fin 5) < 3) (A 0 3) *
  trans (by decide : (0 : Fin 5) < 4) (A 0 4)

private theorem upperWord_val (A : Matrix (Fin 5) (Fin 5) (ZMod 2)) :
    (upperWord A).val = 1 +
      Matrix.single 3 4 (A 3 4) + Matrix.single 2 3 (A 2 3) +
      Matrix.single 2 4 (A 2 4) + Matrix.single 1 2 (A 1 2) +
      Matrix.single 1 3 (A 1 3) + Matrix.single 1 4 (A 1 4) +
      Matrix.single 0 1 (A 0 1) + Matrix.single 0 2 (A 0 2) +
      Matrix.single 0 3 (A 0 3) + Matrix.single 0 4 (A 0 4) := by
  simp [upperWord, trans, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.add_mul, Matrix.mul_add, Matrix.single_mul_single_of_ne, add_assoc]

private theorem upperWord_eq (g : SL) (hg : g ∈ unipotent 5 (ZMod 2)) :
    upperWord g.val = g := by
  obtain ⟨hu, hd⟩ := (mem_unipotent 5 (ZMod 2) g).mp hg
  have hu := (mem_borel 5 (ZMod 2) g).mp hu
  apply Subtype.ext
  rw [upperWord_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.single, hd]
  all_goals exact (hu (by decide)).symm

private theorem trans_mem_upper {i j : Fin 5} (h : i < j) (a : ZMod 2) :
    trans h a ∈ upper := by
  rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with rfl | rfl
  · simp [trans]
  · exact subset_closure ⟨i, j, h, rfl⟩

private theorem upperWord_mem (A : Matrix (Fin 5) (Fin 5) (ZMod 2)) : upperWord A ∈ upper := by
  unfold upperWord
  repeat' apply upper.mul_mem
  all_goals exact trans_mem_upper _ _

/-- The root-generated positive subgroup is exactly the standard unitriangular Sylow. -/
theorem model_upper_eq_unipotent : upper = unipotent 5 (ZMod 2) := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro _ ⟨i, j, hij, rfl⟩
    change root hij ∈ unipotent 5 (ZMod 2)
    apply (mem_unipotent 5 (ZMod 2) _).mpr
    constructor
    · apply (mem_borel 5 (ZMod 2) _).mpr
      exact Matrix.blockTriangular_transvection hij.le 1
    · intro k
      simp [root, Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply]
      aesop
  · intro g hg
    rw [← upperWord_eq g hg]
    exact upperWord_mem g.val

private theorem root_conj_mem_rectangle (c : ℕ) (i j k l : Fin 5)
    (hij : i < j) (hkl : k < l) (hk : k.val < c) (hl : c ≤ l.val) :
    MulAut.conj (root hij) (root hkl) ∈ rectangle c := by
  have hs : root hkl ∈ rectangle c := subset_closure ⟨k, l, hkl, hk, hl, rfl⟩
  by_cases hjk : j = k
  · subst k
    have he : MulAut.conj (root hij) (root hkl) = root (lt_trans hij hkl) * root hkl :=
      Theory.SpecificGroups.PSL5Two.UniversalCover.matrixRoot_relations.conj_chain
        i j l (ne_of_lt hij) (ne_of_lt hkl) (ne_of_lt (lt_trans hij hkl))
    rw [he]
    exact (rectangle c).mul_mem (subset_closure ⟨i, l, lt_trans hij hkl,
      by omega, hl, rfl⟩) hs
  by_cases hli : l = i
  · subst l
    have he : MulAut.conj (root hij) (root hkl) = root (lt_trans hkl hij) * root hkl :=
      Theory.SpecificGroups.PSL5Two.UniversalCover.matrixRoot_relations.conj_chain_reverse
        k i j (ne_of_lt hkl) (ne_of_lt hij) (ne_of_lt (lt_trans hkl hij))
    rw [he]
    exact (rectangle c).mul_mem (subset_closure ⟨k, j, lt_trans hkl hij,
      hk, by omega, rfl⟩) hs
  have he : MulAut.conj (root hij) (root hkl) = root hkl :=
    Theory.SpecificGroups.PSL5Two.UniversalCover.matrixRoot_relations.conj_distant
      (Theory.SpecificGroups.PSL5Two.UniversalCover.root i j (ne_of_lt hij))
      (Theory.SpecificGroups.PSL5Two.UniversalCover.root k l (ne_of_lt hkl)) hjk hli
  rwa [he]

private theorem mem_normalizer_closure_of_conj {A : Type*} [Group A] [Finite A]
    (g : A) (s : Set A) (h : ∀ x ∈ s, MulAut.conj g x ∈ closure s) :
    g ∈ normalizer (closure s : Set A) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rw [map_le_iff_le_comap]
    exact (closure_le _).mpr h
  · rw [card_map_of_injective (MulAut.conj g).injective]

/-- The positive-root Sylow normalizes each actual rectangular subgroup. -/
theorem model_upper_normalizes_rectangle (c : ℕ) : upper ≤ normalizer (rectangle c : Set SL) := by
  apply (closure_le _).mpr
  rintro _ ⟨i, j, hij, rfl⟩
  apply mem_normalizer_closure_of_conj
  rintro _ ⟨k, l, hkl, hk, hl, rfl⟩
  exact root_conj_mem_rectangle c i j k l hij hkl hk hl

/-- The rectangular root groups are abelian in their actual matrix embedding. -/
theorem model_rectangle_commutative (c : ℕ) : IsMulCommutative (rectangle c) := by
  apply isMulCommutative_closure
  rintro _ ⟨i, j, hij, hi, hj, rfl⟩ _ ⟨k, l, hkl, hk, hl, rfl⟩
  exact Theory.SpecificGroups.PSL5Two.UniversalCover.matrixRoot_relations.commute
    (Theory.SpecificGroups.PSL5Two.UniversalCover.root i j (ne_of_lt hij))
    (Theory.SpecificGroups.PSL5Two.UniversalCover.root k l (ne_of_lt hkl))
    (by change j ≠ k; intro h; subst k; omega)
    (by change l ≠ i; intro h; subst l; omega)

/-- The rectangular groups have exponent two as well as commuting generators. -/
theorem model_rectangle_elementary (c : ℕ) : IsElementaryAbelian 2 (rectangle c) := by
  have hcomm := model_rectangle_commutative c
  unfold rectangle at hcomm ⊢
  let := hcomm
  apply IsElementaryAbelian.closure_of_isMulCommutative
  rintro _ ⟨i, j, hij, _, _, rfl⟩
  exact Theory.SpecificGroups.PSL5Two.UniversalCover.matrixRoot_relations.square
    (Theory.SpecificGroups.PSL5Two.UniversalCover.root i j (ne_of_lt hij))

variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z)

omit [Finite G] in
/-- Elementary abelianity is transported with the original full-centralizer marking. -/
theorem marked_rectangle_elementary (c : ℕ) : IsElementaryAbelian 2 (F.pullback (rectangle c)) := by
  let := model_rectangle_elementary c
  let e := F.pullbackEquiv (rectangle c) ((rectangle_le_upper c).trans upper_le_centralizer)
  exact IsElementaryAbelian.of_injective e.toMonoidHom e.injective


/-- The source Sylow is the pullback of the original positive-root subgroup. -/
theorem sourceSylow_eq_pullback_upper : (sourceSylow F : Subgroup G) = F.pullback upper := by
  rw [coe_sourceSylow, model_upper_eq_unipotent]

/-- Relative normality of the original rectangular groups in the actual source Sylow. -/
theorem sourceSylow_normalizes_rectangle (c : ℕ) :
    (sourceSylow F : Subgroup G) ≤ normalizer (F.pullback (rectangle c) : Set G) := by
  have he := F.pullback_relativeNormalizer (rectangle c)
    ((rectangle_le_upper c).trans upper_le_centralizer)
  rw [sourceSylow_eq_pullback_upper]
  have hm : F.pullback upper ≤ F.pullback (centralizer ⊓ normalizer (rectangle c : Set SL)) :=
    map_mono (map_mono (comap_mono (le_inf upper_le_centralizer
      (model_upper_normalizes_rectangle c))))
  rw [he] at hm
  exact hm.trans inf_le_right

/-- Both line and local-plane normalizers contain the same actual ambient Sylow. -/
theorem plane_normalizers_contain_sourceSylow :
    (sourceSylow F : Subgroup G) ≤ normalizer (F.plane : Set G) ∧
    (sourceSylow F : Subgroup G) ≤ normalizer (F.threeSpace : Set G) :=
  ⟨sourceSylow_normalizes_rectangle F 2, sourceSylow_normalizes_rectangle F 3⟩

/-- Source 39.1(3)'s normality of A₁ and A₂ is relative to T, not to G. -/
theorem planes_normal_in_sourceSylow :
    (F.plane.subgroupOf (sourceSylow F : Subgroup G)).Normal ∧
    (F.threeSpace.subgroupOf (sourceSylow F : Subgroup G)).Normal :=
  ⟨(normal_subgroupOf_iff_le_normalizer (flag_le_sourceSylow F).2.2.1).mpr
      (plane_normalizers_contain_sourceSylow F).1,
    (normal_subgroupOf_iff_le_normalizer (flag_le_sourceSylow F).2.2.2).mpr
      (plane_normalizers_contain_sourceSylow F).2⟩

end Theory.GroupTheory.TransvectionFive.UniquenessLinear
