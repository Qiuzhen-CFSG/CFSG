module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.Recognition.RankTwoHull.LocalCover
public import CFSG.Quasithin.ClassicalModels
public import CFSG.Quasithin.MainConverse.EvenLinearLocal.LinearThreeGeometry
public import Theory.GroupTheory.SylowNormalizerOvergroup
public import Theory.SpecificGroups.PSL3.FullParabolicProperness
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover
public import Theory.SpecificGroups.SymplecticFour.Sylow

/-!
# Simultaneous classical rank-two normalizer covers

For PSL₃(2ⁿ) and PSp₄(2ⁿ), the normalizer of a nontrivial two-subgroup
lies in a conjugate full geometric parabolic. If it contains a chosen Sylow
subgroup P, internal Sylow conjugacy puts N(P) in that same parabolic:
each standard parabolic already contains the full normalizer of the standard
unipotent Sylow. Thus the join of the two normalizers is proper.

In particular this applies to the source four-group R normalized by P.
Sylow maximality also gives R ≤ P. The model predicates supply genuine
matrix isomorphisms; the symplectic projective quotient is identified with
Sp₄ by its trivial centre in characteristic two.

These are the intrinsic classical inputs to the parent's invariant hull,
not a proof of the remaining source classification or its other model branches.
Source: Aschbacher--Smith, 15.3.43(e) and the characteristic-two paragraph,
printed p.1140; 1.1.5(3)(a)--(c), pp.501--502; A.2.3--4, p.33.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection

private theorem fourGroup_local {K : Type*} [Group K]
    (P : Sylow 2 K) (R : Subgroup K) (he : IsElementaryAbelian 2 R)
    (hc : Nat.card R = 4) (hn : (P : Subgroup K) ≤ normalizer (R : Set K)) :
    R ≤ P ∧ IsTwoLocal (normalizer (R : Set K)) := by
  let : IsElementaryAbelian 2 R := he
  have hp := IsElementaryAbelian.isPGroup 2 R
  refine ⟨hp.le_sylow_of_normalized P hn, R, ?_, hp, rfl⟩
  intro h
  simp [h] at hc

private theorem linear_matrix_cover (F : Type*) [Field F] [Finite F]
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n) :
    FourGroupNormalizerCover PSL(3,F) := by
  intro P R he hc hPR
  have hM := (fourGroup_local P R he hc hPR).2
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

/-- The full Sylow and invariant four-group normalizers in PSL₃(2ⁿ), n > 1,
generate a proper subgroup. -/
theorem linear_fourGroupNormalizerCover {K : Type*} [Group K] [Finite K]
    {n : ℕ} (hn : 1 < n) (hK : ClassicalGroup.IsPSL K 3 (2 ^ n)) :
    FourGroupNormalizerCover K := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hK
  exact (linear_matrix_cover F hn hF).of_mulEquiv e

open Theory.SpecificGroups.SymplecticFour in
private theorem symplectic_matrix_cover (F : Type*) [Field F] [Finite F]
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n) :
    FourGroupNormalizerCover (Sp F) := by
  intro P R he hc hPR
  have hM := (fourGroup_local P R he hc hPR).2
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

/-- The full Sylow and invariant four-group normalizers in PSp₄(2ⁿ), n > 1,
generate a proper subgroup, transported through the actual projective model. -/
theorem symplectic_fourGroupNormalizerCover {K : Type*} [Group K] [Finite K]
    {n : ℕ} (hn : 1 < n) (hK : ClassicalGroup.IsPSp K 2 (2 ^ n)) :
    FourGroupNormalizerCover K := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hK
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  exact (symplectic_matrix_cover F hn hF).of_mulEquiv
    (e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm)

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection
