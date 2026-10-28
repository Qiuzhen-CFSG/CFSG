module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.Recognition.BorelHull.Cover
public import CFSG.Quasithin.MainConverse.EvenLinearLocal.LinearThreeGeometry
public import Theory.GroupTheory.SylowNormalizerOvergroupAlignment
public import Theory.SpecificGroups.PSL3.FullParabolicProperness
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover
public import Theory.SpecificGroups.SymplecticFour.Sylow

/-!
# Classical normalizer covers without an order-four restriction

The intrinsic two-local covers in PSL₃ and PSp₄ apply to every nonidentity
two-subgroup. Each standard parabolic contains the standard Sylow normalizer.
Sylow conjugacy within the chosen parabolic aligns the prescribed Sylow,
so both normalizers lie in the same proper subgroup. Projective model
equivalences retain the actual field and the trivial symplectic center.

Source: Aschbacher--Smith, 15.3.41 and the parabolic step of 15.3.35,
printed pp.1138--1139; defining-characteristic two-local geometry.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection.BorelHull

private theorem linear_matrix_cover (F : Type*) [Field F] [Finite F]
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n) :
    TwoSubgroupNormalizerCover PSL(3,F) := by
  intro P R hR hp hPR
  have hM : IsTwoLocal (normalizer (R : Set PSL(3,F))) := ⟨R, hR, hp, rfl⟩
  obtain ⟨g, point, hg⟩ := MainConverse.LinearThreeGeometry.twoLocal_conjugate_le
    F (by omega) hF (normalizer (R : Set PSL(3,F))) hM
  apply Sylow.normalizer_sup_lt_top_of_map_le
    (Matrix.PSL3.LinearThree.unipotentSylow F (by omega) hF) P
    (normalizer (R : Set PSL(3,F))) (Matrix.PSL3.RootPlaneGeometry.parabolic F point)
    (MulAut.conj g) hPR hg ?_ (Matrix.PSL3.RootPlaneGeometry.parabolic_lt_top F point)
  change normalizer (Matrix.PSL3.LinearThree.unipotent F : Set PSL(3,F)) ≤ _
  rw [Matrix.PSL3.LinearThree.normalizer_unipotent F (by omega) hF]
  cases point
  · exact map_mono (show Matrix.PSL3.LinearThree.borelSL F ≤
      Matrix.PSL3.LinearThree.lineParabolicSL F from inf_le_right)
  · exact map_mono (show Matrix.PSL3.LinearThree.borelSL F ≤
      Matrix.PSL3.LinearThree.pointParabolicSL F from inf_le_left)

/-- Simultaneous normalizer coverage in the actual PSL₃ model. -/
theorem linear_twoSubgroupNormalizerCover {K : Type*} [Group K] [Finite K]
    {n : ℕ} (hn : 1 < n) (hK : ClassicalGroup.IsPSL K 3 (2 ^ n)) :
    TwoSubgroupNormalizerCover K := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hK
  exact (linear_matrix_cover F hn hF).of_mulEquiv e

open Theory.SpecificGroups.SymplecticFour in
private theorem symplectic_matrix_cover (F : Type*) [Field F] [Finite F]
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n) :
    TwoSubgroupNormalizerCover (Sp F) := by
  intro P R hR hp hPR
  have hM : IsTwoLocal (normalizer (R : Set (Sp F))) := ⟨R, hR, hp, rfl⟩
  obtain ⟨g, hg⟩ := twoLocal_parabolic_cover hF (by omega)
    (normalizer (R : Set (Sp F))) hM
  have hcover (H : Subgroup (Sp F))
      (hH : (normalizer (R : Set (Sp F))).map (MulAut.conj g).toMonoidHom ≤ H)
      (hB : borel ≤ H) (hlt : H < ⊤) :
      normalizer (P : Set (Sp F)) ⊔ normalizer (R : Set (Sp F)) < ⊤ := by
    apply Sylow.normalizer_sup_lt_top_of_map_le (unipotentSylow hF hn.le) P
      (normalizer (R : Set (Sp F))) H (MulAut.conj g) hPR hH ?_ hlt
    change normalizer (unipotent (F := F) : Set (Sp F)) ≤ H
    rwa [← borel_eq_normalizer_unipotent]
  rcases hg with hp | hl
  · exact hcover pointParabolic hp inf_le_left (lt_top_iff_ne_top.mpr pointParabolic_ne_top)
  · exact hcover planeParabolic hl inf_le_right (lt_top_iff_ne_top.mpr planeParabolic_ne_top)

/-- Simultaneous normalizer coverage in the actual projective symplectic model. -/
theorem symplectic_twoSubgroupNormalizerCover {K : Type*} [Group K] [Finite K]
    {n : ℕ} (hn : 1 < n) (hK : ClassicalGroup.IsPSp K 2 (2 ^ n)) :
    TwoSubgroupNormalizerCover K := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hK
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  exact (symplectic_matrix_cover F hn hF).of_mulEquiv
    (e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm)

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection.BorelHull
