module

public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Model.Maps
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.SpecificGroups.SL2.TwoSubgroupExponent

/-!
# The original marked images in the determinant group

The actual star image of L has order nine and is normal in LU*. The
image of U is a two-group and supplements it. Coprime intersection and
product counting give order four for U*. Binary SL₂ two-subgroups have
exponent two, so the two matrix projections also give exponent two for
U*. These are inputs to the singular-point stabilizer calculation, not
assumptions identifying that stabilizer.

Source: Aschbacher–Smith, G.2.6, printed p.336.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
open Setup ClassicalOrthogonal.FourPlusMatrix
namespace Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G} (d : Hypothesis D g)
include d

/-- The image definition agrees with the literal original starred subgroup. -/
theorem modelImage_eq_star (A : Subgroup G) (hA : A ≤ D.L ⊔ D.U) :
    d.modelImage A = ((D.star A).subgroupOf (D.star (D.L ⊔ D.U))).map d.model.toMonoidHom := by
  have he : (A.subgroupOf (D.L ⊔ D.U)).map (starProjection D (D.L ⊔ D.U) d.LU_le_LT) =
      (D.star A).subgroupOf (D.star (D.L ⊔ D.U)) := by
    ext q
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨inclusion d.LU_le_LT a, ha, rfl⟩
    · rintro ⟨a, ha, he⟩
      exact ⟨⟨a, hA ha⟩, ha, Subtype.ext he⟩
  rw [modelImage, matrixProjection, ← Subgroup.map_map, he]

/-- The comparison of marked images preserves the actual group structure. -/
def starModelImageEquiv (A : Subgroup G) (hA : A ≤ D.L ⊔ D.U) :
    D.star A ≃* d.modelImage A :=
  (subgroupOfEquivOfLe (binary_star_mono hA)).symm.trans
    ((d.model.subgroupMap ((D.star A).subgroupOf (D.star (D.L ⊔ D.U)))).trans
      (MulEquiv.subgroupCongr (d.modelImage_eq_star A hA).symm))

theorem modelImage_card (A : Subgroup G) (hA : A ≤ D.L ⊔ D.U) :
    Nat.card (d.modelImage A) = Nat.card (D.star A) :=
  Nat.card_congr (d.starModelImageEquiv A hA).symm.toEquiv

theorem modelImage_L_card : Nat.card (d.modelImage D.L) = 9 := by
  rw [d.modelImage_card D.L le_sup_left, Nat.card_congr d.L_model.toEquiv]
  simp [Nat.card_eq_fintype_card]

theorem modelImage_U_isPGroup : IsPGroup 2 (d.modelImage D.U) :=
  (U_isPGroup d.base d.closure).comap_subtype.map d.matrixProjection

/-- L is normal in LU by the original T-normalization hypothesis. -/
theorem modelImage_L_normal : (d.modelImage D.L).Normal := by
  have hL : (D.L.subgroupOf (D.L ⊔ D.U)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le D.L.le_normalizer (d.closure.normal.1.trans d.base.T_normalizes_L))
  exact hL.map d.matrixProjection d.matrixProjection_surjective

theorem modelImage_L_disjoint_U : Disjoint (d.modelImage D.L) (d.modelImage D.U) := by
  obtain ⟨n, hn⟩ := d.modelImage_U_isPGroup.exists_card_eq
  apply disjoint_of_coprime_natCard
  rw [d.modelImage_L_card, hn]
  exact (by decide : Nat.Coprime 9 2).pow_right n

omit d [Finite G] in
theorem pairSL_card : Nat.card (PairSL (F := ZMod 2)) = 36 := by
  rw [Nat.card_congr pairPermEquiv.toEquiv, Nat.card_prod]
  simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

/-- The full determinant image and E₉ force the marked two-group to have order four. -/
theorem modelImage_U_card : Nat.card (d.modelImage D.U) = 4 := by
  let := d.modelImage_L_normal
  have he := card_sup_eq_mul_of_normalizes_of_disjoint
    (d.modelImage D.L) (d.modelImage D.U) le_normalizer_of_normal d.modelImage_L_disjoint_U
  rw [d.modelImage_L_sup_U, Nat.card_congr topEquiv.toEquiv, pairSL_card,
    d.modelImage_L_card] at he
  omega

/-- In particular this is the order of the original starred subgroup U. -/
theorem star_U_card : Nat.card (D.star D.U) = 4 := by
  rw [← d.modelImage_card D.U le_sup_right]
  exact d.modelImage_U_card

/-- Each matrix projection has exponent two on the marked two-group. -/
theorem modelImage_U_square (u : d.modelImage D.U) : u ^ 2 = 1 := by
  apply Subtype.ext
  apply Prod.ext
  · let f := MonoidHom.fst (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
      (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
    exact congrArg Subtype.val (Matrix.SpecialLinearGroup.twoSubgroup_pow_two
      ((d.modelImage D.U).map f) (d.modelImage_U_isPGroup.map f)
      ⟨f u, mem_map_of_mem f u.property⟩)
  · let f := MonoidHom.snd (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
      (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
    exact congrArg Subtype.val (Matrix.SpecialLinearGroup.twoSubgroup_pow_two
      ((d.modelImage D.U).map f) (d.modelImage_U_isPGroup.map f)
      ⟨f u, mem_map_of_mem f u.property⟩)

/-- The marked determinant image is an elementary four-group. -/
theorem modelImage_U_elementary : IsElementaryAbelian 2 (d.modelImage D.U) where
  toIsMulCommutative := IsPGroup.isMulCommutative_of_card_eq_prime_sq
    (p := 2) d.modelImage_U_card
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr d.modelImage_U_square

/-- Elementarity is transported back to the original starred U. -/
theorem star_U_elementary : IsElementaryAbelian 2 (D.star D.U) := by
  let e := d.starModelImageEquiv D.U le_sup_right
  let he := d.modelImage_U_elementary
  refine { toIsMulCommutative := ⟨⟨fun x y => e.injective ?_⟩⟩
           exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  · simp only [map_mul]
    exact he.toIsMulCommutative.is_comm.comm _ _
  · intro u
    apply e.injective
    rw [map_pow, map_one]
    exact d.modelImage_U_square _

/-- Star generation also gives the exact source index |U:W|=4. -/
theorem W_index_eq_four_of_star (hstar : D.star (D.I g) = D.star (D.L ⊔ D.U)) :
    (D.W g).relIndex D.U = 4 :=
  (d.W_index_of_star hstar).trans d.star_U_card

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
