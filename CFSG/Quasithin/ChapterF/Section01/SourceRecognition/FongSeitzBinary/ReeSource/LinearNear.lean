module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.PositiveNearEquality

/-!
# The linear near-root clause for all Suzuki parameters

The Suzuki near equality writes the internal linear root D as [C,E].
The adjacent linear root B centralizes C, while (6.4), reflected on the
same octagon, bounds [E,B] by Omega(C). That Omega centralizes C. The
three-subgroup lemma therefore makes B commute with D. Reflecting back
gives the first clause of (6H)(b), including Sz(2).

Source: Fong--Seitz I (6H)(b), printed p.54. This uses the already proved
near equality and (6.4), retaining natural panel markings, odd linear degree
and faithful Borel. It does not assume the desired vanishing or positivity
of the Suzuki parameter. OriginalPositivePerpendicular and
Section10Perpendicular retain the original quotient and (10.2)(i) consumers.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (n : ℕ) (hn : Odd n) (m : ℕ)
  (ν : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hC : (quotientBorel Q 0).map ν.toMonoidHom = normalizer (T : Set _))
  (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q 1).map μ.toMonoidHom = normalizer (SuzukiRootSubgroup m : Set _))
private theorem ssq (k : Fin 2) : Q.simple k*Q.simple k = 1 := by
  simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem k)).2
private theorem right_comm (A B : Subgroup (X ⧸ Q.D)) (w : Weyl Q) :
    rightConjugate ⁅A,B⁆ (representative w : X ⧸ Q.D) =
      ⁅rightConjugate A (representative w : X ⧸ Q.D),rightConjugate B (representative w : X ⧸ Q.D)⁆ := by
  simp only [rightConjugate,comap_equiv_eq_map_symm',map_commutator]
private theorem right_bot (w : Weyl Q) :
    rightConjugate (⊥ : Subgroup (X ⧸ Q.D)) (representative w : X ⧸ Q.D) = ⊥ := by
  simp only [rightConjugate,comap_equiv_eq_map_symm',Subgroup.map_bot]
private theorem right_rep (k : Fin 2) (v w : Weyl Q) :
    rightConjugate (rootAt Q split k v) (representative w : X ⧸ Q.D) = rootAt Q split k (v*w) :=
  rootAt_right Q split k v w _ (representative_spec _)
private theorem right_simple (k : Fin 2) (w : Weyl Q) :
    rightConjugate (simpleRoot Q split k) (representative w : X ⧸ Q.D) = rootAt Q split k w := rfl
private theorem right_omega (A : Subgroup (X ⧸ Q.D)) (w : Weyl Q) :
    rightConjugate (omegaOneAmbient A) (representative w : X ⧸ Q.D) =
      omegaOneAmbient (rightConjugate A (representative w : X ⧸ Q.D)) := by
  simp only [rightConjugate,comap_equiv_eq_map_symm']
  exact map_omegaOneAmbient_injective _ (MulEquiv.injective _) _

include ν hC μ hB hn in
/-- The linear part of (6H)(b), including the binary row. -/
theorem source_linear_near_commute
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    ⁅simpleRoot Q split 0,rootAt Q split 0 (Q.simple 1*Q.simple 0)⁆ = ⊥ := by
  let B := rootAt Q split 0 (Q.simple 1)
  let C := rootAt Q split 1 (Q.simple 0*Q.simple 1)
  let D := rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)
  let E := rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)
  have hBC : ⁅B,C⁆ = ⊥ := by
    have hh := congrArg (fun A => rightConjugate A (representative (Q.simple 1) : X ⧸ Q.D))
      (adjacent_commutator_eq_bot Q split hm 0 1 (by decide)
        (marked_linear_remainder_le_kernel Q split 0 ν T hC)
        (marked_suzuki_remainder_le_kernel Q split 1 m μ hB))
    simpa only [right_comm,right_bot,right_rep,right_simple] using hh
  have hEB : ⁅E,B⁆ ≤ omegaOneAmbient C := by
    let w := Q.simple 0*Q.simple 1*Q.simple 0
    have hh := map_mono (f := (MulAut.conj (representative w : X ⧸ Q.D)).symm.toMonoidHom)
      (source_six_four_of_odd_degree Q split hc hm n hn m ν T hC μ hB hcore).1
    have hmap (A : Subgroup (X ⧸ Q.D)) : A.map
        (MulAut.conj (representative w : X ⧸ Q.D)).symm.toMonoidHom =
        rightConjugate A (representative w : X ⧸ Q.D) := by
      simp only [rightConjugate,comap_equiv_eq_map_symm']
    simp only [hmap,right_comm,right_simple,right_omega] at hh
    have ht := four_interval_reflection Q split hm 1 0 (by decide) (representative w) (representative_spec _)
    rw [ht.2.1,ht.2.2] at hh
    exact hh
  have hOmega : ⁅omegaOneAmbient C,C⁆ = ⊥ := by
    have hh := congrArg (fun A => rightConjugate A (representative (Q.simple 0*Q.simple 1) : X ⧸ Q.D))
      (commutator_eq_bot_iff_le_centralizer.mpr (suzukiOmega_centralizes Q split 1 m μ hB))
    simpa only [right_comm,right_bot,right_omega,right_simple] using hh
  have hCE : ⁅C,E⁆ = D := by
    have hh := congrArg (fun A => rightConjugate A (representative (Q.simple 0*Q.simple 1) : X ⧸ Q.D))
      (source_near_eq_of_odd_degree Q split n hn m ν T hC μ hB hm hcore hc)
    rw [right_comm,right_simple,right_rep,right_rep] at hh
    have hE : rootAt Q split 1 ((Q.simple 0*Q.simple 1)*(Q.simple 0*Q.simple 1)) = E := by
      rw [←mul_assoc,←right_rep]
      exact perpendicular_root_stable Q split hm 1 0 (by decide) _ (representative_spec _)
    rw [hE] at hh
    simpa only [C,D,mul_assoc] using hh
  have htriple : ⁅⁅C,E⁆,B⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate
    (eq_bot_iff.mpr ((commutator_mono hEB le_rfl).trans hOmega.le))
    (by rw [hBC,commutator_bot_left])
  rw [hCE,commutator_comm] at htriple
  have hh := congrArg (fun A => rightConjugate A (representative (Q.simple 1) : X ⧸ Q.D)) htriple
  dsimp only [B,D] at hh
  simpa only [right_comm,right_bot,right_rep,mul_assoc,ssq,mul_one,rootAt_one] using hh
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
