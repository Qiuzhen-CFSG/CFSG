module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupPointCentralizers
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldParityDegreeThreeSylow

/-!
# Intersecting original Chapter12 points and their common centralizer

Apply the degree-three point-centralizer theorem to the unchanged
ChosenModule. The original Cartan supplies the C_K point-stabilizer
action, and every nonidentity point has the same pointwise centralizer
in C_K. That subgroup has order prime to seven. A transporter in the
actual residual normalizer producing a nontrivial point intersection
must normalize this common centralizer.

This is an intersection reduction, not residual or global TI. Higher
odd degrees and the remaining point equality and parity arguments stay
with qt-d-1222-linear-field-parity. Solvability of the literal quotient
action kernel remains the independent Suzuki input, to be discharged by
qt-f112-linear-suzuki-containment in final assembly.
Source: Aschbacher–Smith, 5.1.17, printed p.640, used in 12.2.2, p.795
(refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B : Subgroup G}
  (D : ChosenModule T L V)
include D

/-- Intersecting original points have the same seven-free C_K centralizer;
the intersecting transporter normalizes that literal subgroup. -/
theorem rankOne_degree_three_point_centralizers
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
    let Z := (setup T L V H A).V₁
    C ⊓ normalizer (Z : Set G) = A ⊔ (C ⊓ centralizer (Z : Set G)) ∧
      (¬ 7 ∣ Nat.card (C ⊓ centralizer (Z : Set G) : Subgroup G)) ∧
      (∀ z ∈ Z, z ≠ 1 → C ⊓ centralizer ({z} : Set G) = C ⊓ centralizer (Z : Set G)) ∧
      ∀ g ∈ N, Z ⊓ Z.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
        C ⊓ centralizer (Z : Set G) = C ⊓ centralizer (Z.map (MulAut.conj g).toMonoidHom : Set G) ∧
          g ∈ normalizer ((C ⊓ centralizer (Z : Set G) : Subgroup G) : Set G) := by
  obtain ⟨F,he,hnat⟩ := D.rankOne_odd_natural_fundamental_exists
    h hmany (by decide) hpsl hH hlinear (by decide)
  obtain ⟨hm,hnf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  have ht := fundamental_degree_three_point_centralizers
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany (by decide) hpsl)
    hH hm hnf hlinear hsolv F hnat c
  simpa only [he] using ht
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
