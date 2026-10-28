module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupCartanSylowAction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldParitySylowFactorization

/-!
# The Cartan Sylow action on the literal Chapter12 point

The original odd-degree setup supplies a full Sylow of the solvable
residual quotient-centralizer. Its intersection with N_G(L) is the
product of the original Cartan Sylow and its kernel on L/O₂(L), with
disjoint commuting factors. Applying that factorization to the chosen
module shows that preservation of Z₁ reduces to this latter kernel;
under that remaining condition the full Sylow normalizer has point TI.
The residual-normalizer Frattini product retains the same Sylow.

This isolates, but does not discharge, the source point-action step.
Residual/global TI and final parity remain with
qt-d-1222-linear-field-parity. The independent Suzuki input remains
explicit as solvability of the literal residual quotient-action kernel.

Source: Aschbacher–Smith 5.1.17, printed p.640 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} {n : ℕ}
  (D : ChosenModule T L V)
include D

theorem rankOne_odd_full_kernel_sylow_local_factors
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker)
    {A B : Subgroup G} (c : CartanPair T L H A B) (hodd : Odd n) :
    let C := (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker.map
      (normalizer (residual H : Set G)).subtype
    let Z₀ := conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) C
    let Cₗ := (normalizerQuotientAction L (pCore 2 L)).ker.map
      (normalizer (L : Set G)).subtype
    ∃ (p : ℕ) (_hp : Fact p.Prime) (E : Subgroup G) (P : Sylow p C) (R : Sylow p A),
      p ≠ 2 ∧ orderOf (2 : ZMod p) = n ∧ E ≤ A ∧ Nat.card E = p ∧
      E ≤ (P : Subgroup C).map C.subtype ∧
      (R : Subgroup A).map A.subtype = (P : Subgroup C).map C.subtype ⊓ A ∧
      (P : Subgroup C).map C.subtype ⊓ normalizer (L : Set G) =
        (R : Subgroup A).map A.subtype ⊔ ((P : Subgroup C).map C.subtype ⊓ Cₗ) ∧
      Disjoint ((R : Subgroup A).map A.subtype) ((P : Subgroup C).map C.subtype ⊓ Cₗ) ∧
      (P : Subgroup C).map C.subtype ⊓ normalizer (L : Set G) ≤
        centralizer ((R : Subgroup A).map A.subtype : Set G) ∧
      (P : Subgroup C).map C.subtype =
        ((P : Subgroup C).map C.subtype ⊓ centralizer (Z₀ : Set G)) ⊔
          (R : Subgroup A).map A.subtype ⊔ ((P : Subgroup C).map C.subtype ⊓ Cₗ) := by
  obtain ⟨hm,hf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  exact residual_kernel_sylow_local_factors
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hm hf hlinear hsolv c hodd

/-- For the literal Chapter12 point, the source Sylow's remaining action
is confined to its kernel on L/O₂(L), which centralizes the Cartan Sylow. -/
theorem rankOne_odd_full_kernel_sylow_point_action
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    {A B : Subgroup G} (c : CartanPair T L H A B) (hodd : Odd n)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker) :
    let N := normalizer (residual H : Set G)
    let C := (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker.map N.subtype
    let Cₗ := (normalizerQuotientAction L (pCore 2 L)).ker.map
      (normalizer (L : Set G)).subtype
    let Z := (setup T L V H A).V₁
    ∃ (p : ℕ) (_hp : Fact p.Prime) (E : Subgroup G) (P : Sylow p C),
      p ≠ 2 ∧ orderOf (2 : ZMod p) = n ∧ E ≤ A ∧ Nat.card E = p ∧
      E ≤ (P : Subgroup C).map C.subtype ∧
      N = C ⊔ (N ⊓ normalizer ((P : Subgroup C).map C.subtype : Set G)) ∧
      ((P : Subgroup C).map C.subtype ⊓ Cₗ ≤ centralizer (E : Set G)) ∧
      (((P : Subgroup C).map C.subtype ≤ normalizer (Z : Set G)) ↔
        ((P : Subgroup C).map C.subtype ⊓ Cₗ ≤ normalizer (Z : Set G))) ∧
      (((P : Subgroup C).map C.subtype ⊓ Cₗ ≤ normalizer (Z : Set G)) →
        ∀ g ∈ normalizer ((P : Subgroup C).map C.subtype : Set G),
          Z ⊓ Z.map (MulAut.conj g).toMonoidHom = ⊥ ∨ Z.map (MulAut.conj g).toMonoidHom = Z) := by
  obtain ⟨F,he,hnat⟩ := D.rankOne_odd_natural_fundamental_exists h hmany hn hpsl hH hlinear hodd
  obtain ⟨p,hp,E,P,R,hp2,ho,hEA,hE,hEP,hR,hlocal,hdis,hcent,hfactor⟩ :=
    D.rankOne_odd_full_kernel_sylow_local_factors h hmany hn hpsl hH hlinear hsolv c hodd
  let C := (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker.map
    (normalizer (residual H : Set G)).subtype
  let Cₗ := (normalizerQuotientAction L (pCore 2 L)).ker.map
    (normalizer (L : Set G)).subtype
  let PG := (P : Subgroup C).map C.subtype
  let RA := (R : Subgroup A).map A.subtype
  let Z := (setup T L V H A).V₁
  let Z₀ := conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) C
  have hAZ : A ≤ normalizer (Z : Set G) := by
    have hh := fundamental_point_normalizer (H := H) (A := A) F
      D.sylow_normalizes_component hpsl hodd hnat
    rw [he] at hh
    exact (c.left_le.trans hh.ge).trans inf_le_right
  have hER : E ≤ RA := by
    change E ≤ (R : Subgroup A).map A.subtype
    rw [hR]
    exact le_inf hEP hEA
  have hkE : PG ⊓ Cₗ ≤ centralizer (E : Set G) :=
    (le_inf inf_le_left (inf_le_right.trans (map_subtype_le _))).trans
      (hcent.trans (centralizer_le hER))
  have hZZ₀ : Z ≤ Z₀ := inf_le_left.trans (le_conjugateSpanBy _ _)
  have hlift (hk : PG ⊓ Cₗ ≤ normalizer (Z : Set G)) :
      PG ≤ normalizer (Z : Set G) := by
    change PG = (PG ⊓ centralizer (Z₀ : Set G)) ⊔ RA ⊔ (PG ⊓ Cₗ) at hfactor
    exact hfactor.le.trans (sup_le
      (sup_le ((inf_le_right.trans (centralizer_le hZZ₀)).trans
        (Subgroup.centralizer_le_normalizer _)) ((map_subtype_le _).trans hAZ)) hk)
  refine ⟨p,hp,E,P,hp2,ho,hEA,hE,hEP,
    residual_normalizer_kernel_sylow_factorization P,hkE,
    ⟨fun hPZ => inf_le_left.trans hPZ,hlift⟩,?_⟩
  intro hk g hg
  subst V
  exact fundamental_point_ti_under_primitive_actor_normalizer F D.sylow_normalizes_component
    hpsl hodd hnat c hp.out hp2 ho E PG hEA hE hEP (hlift hk) hg

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
