module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupSylowFactorization
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldParityBlockExclusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldParityPrimitiveTI

/-!
# Full-kernel Sylow selection for the literal Chapter12 point

The original ChosenModule hypotheses give Thompson–Baumann factorization
inside C_K itself. A primitive Cartan actor extends to a full Sylow subgroup
of C_K with P ∩ D_L Sylow in D_L, the source centralizer/local-normalizer
product, and M⁺ = C_K N_{M⁺}(P).

Primitive-prime actors in P ∩ N_G(L) induce inner automorphisms on L/O₂(L).
The final reduction identifies the unresolved local action literally:
P stabilizes Ω₁Z(T) ∩ V exactly when P ∩ N_G(L) does. Under that condition,
the proved primitive actor makes the full normalizer of P act with point TI.
This is not residual-normalizer or global TI. Their construction and final
parity remain with qt-d-1222-linear-field-parity. The exact independent
Suzuki consequence remains the kernel-solvability hypothesis.

Source: Aschbacher–Smith 5.1.17, p.640, applied to 12.2.2, p.795
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

/-- Thompson–Baumann factorization on the entire literal quotient-centralizer. -/
theorem rankOne_odd_kernel_baumann_factorization
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker) :
    let C := (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker.map
      (normalizer (residual H : Set G)).subtype
    let Z₀ := conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) C
    C = (C ⊓ centralizer (Z₀ : Set G)) ⊔
      (C ⊓ normalizer (ChapterB.baumann (T : Subgroup G) : Set G)) := by
  obtain ⟨hm,_⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  exact residual_kernel_baumann_factorization
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH hm hlinear hsolv

/-- Full-kernel Sylow selection and the residual Frattini product, with
no point-stability, natural-marking or TI premise. -/
theorem rankOne_odd_full_kernel_sylow_factorization
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
    let Z₀ := conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) C
    ∃ (p : ℕ) (_hp : Fact p.Prime) (E : Subgroup G) (P : Sylow p C) (R : Sylow p A),
      p ≠ 2 ∧ orderOf (2 : ZMod p) = n ∧ E ≤ A ∧ Nat.card E = p ∧
      E ≤ (P : Subgroup C).map C.subtype ∧
      (R : Subgroup A).map A.subtype = (P : Subgroup C).map C.subtype ⊓ A ∧
      (P : Subgroup C).map C.subtype =
        ((P : Subgroup C).map C.subtype ⊓ centralizer (Z₀ : Set G)) ⊔
        ((P : Subgroup C).map C.subtype ⊓ normalizer (L : Set G)) ∧
      N = C ⊔ (N ⊓ normalizer ((P : Subgroup C).map C.subtype : Set G)) := by
  obtain ⟨hm,hf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  obtain ⟨p,hp,E,P,R,hp2,ho,hEA,hE,hEP,hR,hP⟩ :=
    residual_kernel_primitive_sylow_factorization
      (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
      hH hm hf hlinear hsolv c hodd
  exact ⟨p,hp,E,P,R,hp2,ho,hEA,hE,hEP,hR,hP,
    residual_normalizer_kernel_sylow_factorization P⟩

/-- The source full Sylow can be chosen so that its remaining point-stability
obligation lies in P ∩ N_G(L); this subgroup acts by inner automorphisms
on L/O₂(L). Once point stability is established, the full normalizer of P
has point TI by the actual primitive Cartan action. -/
theorem rankOne_odd_full_kernel_sylow_local_action_reduction
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
    let Z := (setup T L V H A).V₁
    ∃ (p : ℕ) (_hp : Fact p.Prime) (P : Sylow p C),
      orderOf (2 : ZMod p) = n ∧
      N = C ⊔ (N ⊓ normalizer ((P : Subgroup C).map C.subtype : Set G)) ∧
      (∀ x : ((P : Subgroup C).map C.subtype ⊓ normalizer (L : Set G) : Subgroup G),
        normalizerQuotientAction L (pCore 2 L) (inclusion inf_le_right x) ∈
          MulAut.innerSubgroup (L ⧸ pCore 2 L)) ∧
      (((P : Subgroup C).map C.subtype ≤ normalizer (Z : Set G)) ↔
        ((P : Subgroup C).map C.subtype ⊓ normalizer (L : Set G) ≤ normalizer (Z : Set G))) ∧
      (((P : Subgroup C).map C.subtype ⊓ normalizer (L : Set G) ≤ normalizer (Z : Set G)) →
        ∀ g ∈ normalizer ((P : Subgroup C).map C.subtype : Set G),
          Z ⊓ Z.map (MulAut.conj g).toMonoidHom = ⊥ ∨ Z.map (MulAut.conj g).toMonoidHom = Z) := by
  obtain ⟨F,he,hnat⟩ := D.rankOne_odd_natural_fundamental_exists h hmany hn hpsl hH hlinear hodd
  obtain ⟨p,hp,E,P,R,hp2,ho,hEA,hE,hEP,hR,hP,hN⟩ :=
    D.rankOne_odd_full_kernel_sylow_factorization h hmany hn hpsl hH hlinear c hodd hsolv
  let C := (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker.map
    (normalizer (residual H : Set G)).subtype
  let PG := (P : Subgroup C).map C.subtype
  let Z := (setup T L V H A).V₁
  let Z₀ := conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) C
  have hZZ₀ : Z ≤ Z₀ := inf_le_left.trans (le_conjugateSpanBy _ _)
  have hlift (hloc : PG ⊓ normalizer (L : Set G) ≤ normalizer (Z : Set G)) :
      PG ≤ normalizer (Z : Set G) := by
    change PG = (PG ⊓ centralizer (Z₀ : Set G)) ⊔ (PG ⊓ normalizer (L : Set G)) at hP
    rw [hP]
    exact sup_le ((inf_le_right.trans (centralizer_le hZZ₀)).trans
      (Subgroup.centralizer_le_normalizer _)) hloc
  have hi (x : (PG ⊓ normalizer (L : Set G) : Subgroup G)) :
      normalizerQuotientAction L (pCore 2 L) (inclusion inf_le_right x) ∈
        MulAut.innerSubgroup (L ⧸ pCore 2 L) := by
    exact primitive_prime_actor_inner_on_left hpsl hn hp2 ho _
      ((P.isPGroup'.map C.subtype).of_injective (inclusion inf_le_left)
        (inclusion_injective inf_le_left)) inf_le_right x
  refine ⟨p,hp,P,ho,hN,hi,⟨fun hPZ => inf_le_left.trans hPZ,hlift⟩,?_⟩
  intro hloc g hg
  subst V
  exact fundamental_point_ti_under_primitive_actor_normalizer F D.sylow_normalizes_component
    hpsl hodd hnat c hp.out hp2 ho E PG hEA hE hEP (hlift hloc) hg

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
