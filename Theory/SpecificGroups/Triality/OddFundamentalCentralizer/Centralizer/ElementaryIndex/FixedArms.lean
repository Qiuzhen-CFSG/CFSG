module
public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Centralizer.Lifts
public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.RankOne.Scalars
public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.RankOne.Kernels

/-!
# Fixed points of the three-arm central product

The three pinned arm scalar involutions coincide on the integral D4 lattice.
Consequently a kernel element of the arm product has scalar coordinates, and
any graph-field fixed product can be corrected by these signs to the literal
Frobenius diagonal. This proves the fixed-part range in every characteristic,
including odd characteristic and q = 3, without assuming product injectivity.

Source: GLS3 §§2.4, 2.6, especially Proposition 2.6.2(a,b)
(`refs/KGroup/GLS3/chapter2.tex`). The conjugated application in `ElementaryIndex`
uses exactly the inverse conjugation of `Centralizer/Lifts`.
-/

@[expose] public section
noncomputable section
open Matrix
open scoped MatrixGroups
namespace Triality.Standard.OddFundamentalCentralizer.ElementaryIndex
open Parabolics

variable {P : Parameters} (D : PinnedRankOneMaps P) (C : ArmRootCommutation P)

/-- The two pinned transvections uniquely determine the rank-one homomorphism. -/
theorem pinned_hom_eq (E : PinnedRankOneMaps P) (i : Fin 4)
    (a : SL(2, ExtensionField P)) : D.hom i a = E.hom i a := by
  apply sl2_root_induction (fun a => D.hom i a = E.hom i a) ?_ ?_ ?_ a
  · intro t
    rw [D.positive, E.positive]
  · intro t
    rw [D.negative, E.negative]
  · intro a b ha hb
    simp only [map_mul, ha, hb]

/-- All three arm scalar involutions agree for any maps with the given pinning. -/
theorem scalar_arms (i j : Fin 4) (hi : i ≠ 1) (hj : j ≠ 1) :
    D.hom i (-1) = D.hom j (-1) := by
  rw [pinned_hom_eq D (RankOne.pinnedRankOneMaps P) i,
    pinned_hom_eq D (RankOne.pinnedRankOneMaps P) j]
  exact RankOne.pinned_scalar_arms P i j hi hj

private theorem center_of_mul_eq_one {A G : Type*} [Group A] [Group G]
    (f : A →* G) (hf : Function.Injective f) (a : A) (b : G)
    (hab : f a * b = 1) (hc : ∀ x, Commute (f x) b) :
    a ∈ Subgroup.center A := by
  rw [Subgroup.mem_center_iff]
  intro x
  apply hf
  simp only [map_mul]
  rw [eq_inv_of_mul_eq_one_left hab]
  exact (hc x).inv_right.eq

private theorem kernel_scalar_coordinates
    (a b c : SL(2, ExtensionField P)) (h : D.armsProduct C ((a, b), c) = 1) :
    (a = 1 ∨ a = -1) ∧ (b = 1 ∨ b = -1) ∧ (c = 1 ∨ c = -1) := by
  have ha : D.hom 0 a * (D.hom 2 b * D.hom 3 c) = 1 := by
    simpa only [PinnedRankOneMaps.armsProduct_apply, mul_assoc] using h
  have hb : D.hom 2 b * (D.hom 0 a * D.hom 3 c) = 1 := by
    rw [← mul_assoc, (D.commute C 0 2 (by decide) (by decide) (by decide) a b).symm.eq]
    exact h
  have hc : D.hom 3 c * (D.hom 0 a * D.hom 2 b) = 1 :=
    mul_eq_one_comm.mpr h
  exact ⟨RankOne.scalar_cases _ (center_of_mul_eq_one _ (D.injective 0) a _ ha
      (fun x => (D.commute C 0 2 (by decide) (by decide) (by decide) x b).mul_right
        (D.commute C 0 3 (by decide) (by decide) (by decide) x c))),
    RankOne.scalar_cases _ (center_of_mul_eq_one _ (D.injective 2) b _ hb
      (fun x => (D.commute C 2 0 (by decide) (by decide) (by decide) x a).mul_right
        (D.commute C 2 3 (by decide) (by decide) (by decide) x c))),
    RankOne.scalar_cases _ (center_of_mul_eq_one _ (D.injective 3) c _ hc
      (fun x => (D.commute C 3 0 (by decide) (by decide) (by decide) x a).mul_right
        (D.commute C 3 2 (by decide) (by decide) (by decide) x b)))⟩

private theorem scalar_mul_inv_cases {F : Type*} [Field F] (a b : SL(2, F))
    (h : a * b⁻¹ = 1 ∨ a * b⁻¹ = -1) : a = b ∨ a = -b := by
  rcases h with h | h
  · exact Or.inl (mul_inv_eq_one.mp h)
  · right
    have hh := congrArg (fun x => x * b) h
    simpa only [inv_mul_cancel_right, neg_one_mul] using hh

private theorem frobenius_neg (g : SL(2, ExtensionField P)) :
    sl2Frobenius P (-g) = -sl2Frobenius P g := by
  rw [← neg_one_mul g, map_mul, RankOne.sl2Frobenius_neg_one, neg_one_mul]

private theorem armsProduct_neg_first (a b c : SL(2, ExtensionField P)) :
    D.armsProduct C ((-a, b), c) = D.hom 0 (-1) * D.armsProduct C ((a, b), c) := by
  simp only [PinnedRankOneMaps.armsProduct_apply, ← neg_one_mul a, map_mul, mul_assoc]

private theorem armsProduct_neg_second (a b c : SL(2, ExtensionField P)) :
    D.armsProduct C ((a, -b), c) = D.hom 0 (-1) * D.armsProduct C ((a, b), c) := by
  simp only [PinnedRankOneMaps.armsProduct_apply, ← neg_one_mul b, map_mul]
  calc
    _ = D.hom 2 (-1) * (D.hom 0 a * D.hom 2 b * D.hom 3 c) := by
      exact congrArg (fun z => z * D.hom 3 c)
        ((mul_assoc _ _ _).symm.trans
          ((congrArg (fun z => z * D.hom 2 b)
            (D.commute C 0 2 (by decide) (by decide) (by decide) a (-1)).eq).trans
            (mul_assoc _ _ _))) |>.trans (mul_assoc _ _ _)
    _ = _ := congrArg (fun z => z * _) (scalar_arms D 0 2 (by decide) (by decide)).symm

private theorem armsProduct_neg_third (a b c : SL(2, ExtensionField P)) :
    D.armsProduct C ((a, b), -c) = D.hom 0 (-1) * D.armsProduct C ((a, b), c) := by
  simp only [PinnedRankOneMaps.armsProduct_apply, ← neg_one_mul c, map_mul]
  calc
    _ = D.hom 3 (-1) * (D.hom 0 a * D.hom 2 b * D.hom 3 c) :=
      (mul_assoc _ _ _).symm.trans
        ((congrArg (fun z => z * D.hom 3 c)
          ((D.commute C 0 3 (by decide) (by decide) (by decide) a (-1)).mul_left
            (D.commute C 2 3 (by decide) (by decide) (by decide) b (-1))).eq).trans
          (mul_assoc _ _ _))
    _ = _ := congrArg (fun z => z * _) (scalar_arms D 0 3 (by decide) (by decide)).symm

private theorem scalar_square : D.hom 0 (-1) * D.hom 0 (-1) = 1 := by
  rw [← map_mul]
  simp

private theorem armsFixedEmbedding_neg (a : SL(2, ExtensionField P)) :
    D.armsFixedEmbedding C (-a) = D.hom 0 (-1) * D.armsFixedEmbedding C a := by
  change D.armsProduct C ((-a, sl2Frobenius P (-a)),
    sl2Frobenius P (sl2Frobenius P (-a))) = _
  simp only [frobenius_neg,
    armsProduct_neg_first, armsProduct_neg_second, armsProduct_neg_third,
    ← mul_assoc, scalar_square, one_mul]
  rfl

/-- The full fixed part of the arm central product is its Frobenius diagonal. -/
theorem range_armsFixedEmbedding :
    (D.armsFixedEmbedding C).range = splitLevi P .arms ⊓ fixedSubgroup P := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    exact ⟨by rw [← D.range_armsProduct C]; exact ⟨PinnedRankOneMaps.armsDiagonal P a, rfl⟩,
      armsFixed_mem D C a⟩
  · rintro x ⟨hx, hfixed⟩
    rw [← D.range_armsProduct C] at hx
    obtain ⟨⟨⟨a, b⟩, c⟩, rfl⟩ := hx
    have he : D.armsProduct C ((sl2Frobenius P c, sl2Frobenius P a), sl2Frobenius P b) =
        D.armsProduct C ((a, b), c) :=
      (D.graphField_armsProduct C ((a, b), c)).symm.trans hfixed
    have hk : D.armsProduct C
        (((sl2Frobenius P c * a⁻¹), (sl2Frobenius P a * b⁻¹)),
          (sl2Frobenius P b * c⁻¹)) = 1 := by
      change D.armsProduct C
        (((sl2Frobenius P c, sl2Frobenius P a), sl2Frobenius P b) * ((a, b), c)⁻¹) = 1
      exact ((D.armsProduct C).map_mul _ _).trans
        ((congrArg₂ (· * ·) he ((D.armsProduct C).map_inv _)).trans (mul_inv_cancel _))
    have hs := kernel_scalar_coordinates D C _ _ _ hk
    have hb := scalar_mul_inv_cases _ _ hs.2.1
    have hc := scalar_mul_inv_cases _ _ hs.2.2
    have hbc : b = sl2Frobenius P a ∨ b = -sl2Frobenius P a := by
      rcases hb with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h, neg_neg])
    have hcc : c = sl2Frobenius P (sl2Frobenius P a) ∨
        c = -sl2Frobenius P (sl2Frobenius P a) := by
      rcases hbc with h | h <;> rw [h] at hc
      · rcases hc with h | h
        · exact Or.inl h.symm
        · exact Or.inr (by rw [h, neg_neg])
      · rw [frobenius_neg] at hc
        rcases hc with h | h
        · exact Or.inr h.symm
        · exact Or.inl (neg_injective h).symm
    rcases hbc with rfl | rfl <;> rcases hcc with rfl | rfl
    · exact ⟨a, rfl⟩
    · exact ⟨-a, (armsFixedEmbedding_neg D C a).trans
        (armsProduct_neg_third D C _ _ _).symm⟩
    · exact ⟨-a, (armsFixedEmbedding_neg D C a).trans
        (armsProduct_neg_second D C _ _ _).symm⟩
    · refine ⟨a, ?_⟩
      simp only [armsProduct_neg_second, armsProduct_neg_third, ← mul_assoc, scalar_square, one_mul]
      rfl
end Triality.Standard.OddFundamentalCentralizer.ElementaryIndex
