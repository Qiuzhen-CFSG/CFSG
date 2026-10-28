module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupPointSylowAction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldParityCartanSylowAction

/-!
# The actual point stabilizer in the full residual-kernel Sylow

Apply the primitive-prime automorphism calculation to the already chosen
Sylow of the entire solvable C_K and the original Chapter12 module.
Its point stabilizer is the Cartan Sylow times its centralizer of Z₁,
with disjoint factors. The residual-normalizer Frattini product retains
that same Sylow.

The earlier three-factor decomposition and the kernel's preservation of
the Sylow subgroups of L identify the exact remaining requirement:
the full Sylow preserves Z₁ if and only if its L/O₂(L) action kernel
preserves the original chosen V. No point or module invariance is assumed
in this result, and it does not assert that the whole Sylow is the point
stabilizer. Global TI and final Seed/parity assembly remain with
qt-d-1222-linear-field-parity, as does discharge of the independent Suzuki
source currently carried by the literal kernel-solvability premise.
Source: Aschbacher–Smith, proof of 5.1.17, printed p.640
(refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} {n : ℕ}
  (D : ChosenModule T L V)
include D

/-- The literal full-kernel Sylow has the source action factorization on
its point stabilizer. Its remaining invariance is precisely invariance
of the original chosen module under the local quotient kernel. -/
theorem rankOne_odd_full_kernel_sylow_point_stabilizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
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
    ∃ (p : ℕ) (_hp : Fact p.Prime) (E : Subgroup G) (P : Sylow p C) (R : Sylow p A),
      p ≠ 2 ∧ orderOf (2 : ZMod p) = n ∧ E ≤ A ∧ Nat.card E = p ∧
      E ≤ (P : Subgroup C).map C.subtype ∧
      (R : Subgroup A).map A.subtype = (P : Subgroup C).map C.subtype ⊓ A ∧
      N = C ⊔ (N ⊓ normalizer ((P : Subgroup C).map C.subtype : Set G)) ∧
      (P : Subgroup C).map C.subtype ⊓ normalizer (Z : Set G) =
        (R : Subgroup A).map A.subtype ⊔
          ((P : Subgroup C).map C.subtype ⊓ centralizer (Z : Set G)) ∧
      Disjoint ((R : Subgroup A).map A.subtype)
        ((P : Subgroup C).map C.subtype ⊓ centralizer (Z : Set G)) ∧
      (((P : Subgroup C).map C.subtype ≤ normalizer (Z : Set G)) ↔
        ((P : Subgroup C).map C.subtype ⊓ Cₗ ≤ normalizer (V : Set G))) := by
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
  have hRA : RA ≤ PG := hR.le.trans inf_le_left
  have hpst := fundamental_primitive_sylow_point_stabilizer F
    D.sylow_normalizes_component hpsl (by omega) hodd hnat c ho PG
    (P.isPGroup'.map C.subtype) R hRA
  rw [he] at hpst
  have hk := fundamental_kernel_point_stabilizer_eq_module_stabilizer (H := H) (A := A)
    F D.sylow_normalizes_component hpsl (by omega) hodd hnat
  rw [he] at hk
  change Cₗ ⊓ normalizer (Z : Set G) = Cₗ ⊓ normalizer (V : Set G) at hk
  have hAZ : A ≤ normalizer (Z : Set G) := by
    have hh := fundamental_point_normalizer (H := H) (A := A) F
      D.sylow_normalizes_component hpsl hodd hnat
    rw [he] at hh
    exact (c.left_le.trans hh.ge).trans inf_le_right
  have hZZ₀ : Z ≤ Z₀ := inf_le_left.trans (le_conjugateSpanBy _ _)
  refine ⟨p,hp,E,P,R,hp2,ho,hEA,hE,hEP,hR,
    residual_normalizer_kernel_sylow_factorization P,hpst.1,hpst.2,?_⟩
  constructor
  · intro hPZ
    exact ((le_inf inf_le_right (inf_le_left.trans hPZ)).trans hk.le).trans inf_le_right
  · intro hKV
    have hKZ : PG ⊓ Cₗ ≤ normalizer (Z : Set G) :=
      ((le_inf inf_le_right hKV).trans hk.ge).trans inf_le_right
    change PG = (PG ⊓ centralizer (Z₀ : Set G)) ⊔ RA ⊔ (PG ⊓ Cₗ) at hfactor
    exact hfactor.le.trans (sup_le
      (sup_le ((inf_le_right.trans (centralizer_le hZZ₀)).trans
        (Subgroup.centralizer_le_normalizer _)) ((map_subtype_le _).trans hAZ)) hKZ)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
