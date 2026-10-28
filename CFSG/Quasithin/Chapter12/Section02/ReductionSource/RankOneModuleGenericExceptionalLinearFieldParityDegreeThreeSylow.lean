module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupDegreeThreeSylow
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldParityPointSylowAction

/-!
# The original Chapter12 Cartan as a full kernel Sylow in degree three

The literal residual quotient is PSL₃(4), so its quotient-centralizer has
seven-rank at most one. Apply the degree-three Sylow theorem to the original
chosen module and the original Cartan. The Cartan itself is Sylow in all
C_K, the local L/O₂(L) action kernel vanishes, and the residual normalizer
is C_K N_{N_G(K)}(D_L). The unchanged natural point is TI under N_G(D_L).

This discharges the point-invariance step in degree three. Extension of TI
to the full residual normalizer and the higher odd degrees remain with
qt-d-1222-linear-field-parity; the Frattini product alone is not such an
extension. The independent Suzuki source remains the explicit solvability
premise on the literal action kernel, to be discharged by
qt-f112-linear-suzuki-containment in final assembly.
Source: Aschbacher–Smith, 5.1.17, printed p.640 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B : Subgroup G}
  (D : ChosenModule T L V)
include D
local instance degreeThreeSylowSevenPrime : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The source Cartan is itself a Sylow of the whole quotient-centralizer,
and the point TI statement uses the same original V. -/
theorem rankOne_degree_three_cartan_sylow
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^3))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker) :
    let N := normalizer (residual H : Set G)
    let C := (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker.map N.subtype
    let Cₗ := (normalizerQuotientAction L (pCore 2 L)).ker.map
      (normalizer (L : Set G)).subtype
    let Z := (setup T L V H A).V₁
    (∃ P : Sylow 7 C, (P : Subgroup C).map C.subtype = A) ∧
      A ⊓ Cₗ = ⊥ ∧ A ≤ normalizer (Z : Set G) ∧
      N = C ⊔ (N ⊓ normalizer (A : Set G)) ∧
      ∀ g ∈ normalizer (A : Set G),
        Z ⊓ Z.map (MulAut.conj g).toMonoidHom = ⊥ ∨
          Z.map (MulAut.conj g).toMonoidHom = Z := by
  obtain ⟨F,he,hnat⟩ := D.rankOne_odd_natural_fundamental_exists
    h hmany (by decide) hpsl hH hlinear (by decide)
  obtain ⟨hm,hnf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  obtain ⟨P,hP,hker,hpoint,_,hfactor,hti⟩ :=
    fundamental_degree_three_full_sylow_point_action
      (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany (by decide) hpsl)
      hH hm hnf hlinear hsolv F hnat c
  simp only [he,hP] at hker hpoint hfactor hti
  exact ⟨⟨P,hP⟩,hker,hpoint,hfactor,hti⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
