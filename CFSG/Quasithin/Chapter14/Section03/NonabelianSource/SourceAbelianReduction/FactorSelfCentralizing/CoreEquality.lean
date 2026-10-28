module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.FactorSelfCentralizing.Setup
public import Theory.SpecificGroups.AlternatingSix.NaturalSplit.DeletedPointIrreducible
public import Theory.GroupTheory.ConjugateSpanSupplement
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.NormalizingInvolutionCard

/-!
# The global two-core of the marked involution centralizer

The global Sylow assertion puts the core in C_G(z). Normality makes it
centralize the entire A₅-span of z, which is A, so the core lies in the
known elementary group C_G(A). If it contains A, the original seed and
the residual of H generate the nonabelian U inside this elementary group.
Irreducibility therefore makes its intersection with A trivial. The split
C_G(A)=A⟨d⟩ and the faithful A₅ action then give O₂(C_G(d))=⟨d⟩.

This proves the core calculation under the original source hypotheses and
the supplied global Sylow assertion. The later C-component enclosure and
original-seed residual commutator are separate obligations.

Source: Aschbacher--Smith, 14.3.20, printed pp.997--998.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory
open scoped Pointwise commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Recognition BinaryPermutation.SixNaturalSplit
variable {G : Type*} [Group G] [Finite G]
namespace MarkedPoint
variable {T : Sylow 2 G} {V L A : Subgroup G} {F : InvariantFlag T V 2}
variable (P : MarkedPoint F L A)

omit [Finite G] in
theorem blockCentralizer_normalizes_factor :
    P.blockCentralizer ≤ normalizer (A : Set G) := by
  obtain ⟨hn,_⟩ := pointBlockCentralizer_quotient (factorBlock F L A) A P.marking
    P.factor_map P.point P.point_action
  exact (normal_subgroupOf_iff_le_normalizer P.factor_le_blockCentralizer).mp hn

omit [Finite G] in
theorem core_le_factorCentralizer (hVA : V ≤ A) (z : G) (hz : F.Vi 1 = zpowers z)
    (hSylow : Chapter1.IsSylowIn 2 P.sylowCentralizer P.globalCentralizer) :
    P.globalCentralizer.pCoreIn 2 ≤ centralizer (A : Set G) := by
  obtain ⟨S,hS⟩ := hSylow
  have hQT : P.globalCentralizer.pCoreIn 2 ≤ (T : Subgroup G) :=
    ((pCoreIn_le_sylow _ S).trans_eq hS).trans inf_le_left
  have hQz : P.globalCentralizer.pCoreIn 2 ≤ centralizer (zpowers z : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure, ← F.H_eq_centralizer (by decide) z hz]
    exact hQT.trans (F.invariant 1)
  have hnorm : P.globalCentralizer ≤ normalizer (P.globalCentralizer.pCoreIn 2 : Set G) :=
    P.globalCentralizer.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hzA : z ∈ A := hVA (F.le_seed 1 (hz.symm ▸ mem_zpowers z))
  have hz2 : orderOf z = 2 := by
    rw [← Nat.card_zpowers, ← hz]
    simpa using F.card 1 (by decide)
  have hspan := pointBlock_nonzero_span (factorBlock F L A) A P.marking
    P.factor_map P.factor_le P.point P.point_action P.blockCentralizer_normalizes_factor
    z hzA (by intro he; simp [he] at hz2)
  exact (le_centralizer_conjugateSpanBy_of_normalizes _ _ _
    (inf_le_right.trans hnorm) hQz).trans (centralizer_le hspan.ge)

end MarkedPoint

theorem source_global_core_eq
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (A : Subgroup G) (hA : ElementaryFactor F (sourceResidual M Mc) A)
    (hlt : A < centralizer (A : Set G))
    (P : MarkedPoint F (sourceResidual M Mc) A) (z : G) (hz : F.Vi 1 = zpowers z)
    (hSylow : Chapter1.IsSylowIn 2 P.sylowCentralizer P.globalCentralizer) :
    P.globalCentralizer.pCoreIn 2 = zpowers P.element := by
  let := hA.elementary
  let C := centralizer (A : Set G)
  let Q := P.globalCentralizer.pCoreIn 2
  let B := P.blockCentralizer
  let D := zpowers P.element
  have hQC : Q ≤ C := P.core_le_factorCentralizer hA.seed_le z hz hSylow
  have hnorm : P.globalCentralizer ≤ normalizer (Q : Set G) :=
    P.globalCentralizer.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hBQ : B ≤ normalizer (Q : Set G) := inf_le_right.trans hnorm
  have hBA : B ≤ normalizer (A : Set G) := P.blockCentralizer_normalizes_factor
  obtain ⟨hEC,_,hCc⟩ := source_factor_centralizer_elementary_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
    A hA.le_core hA.seed_le hA.card hA.intersection_card hA.normalized
  let := hEC
  have hDC : D ≤ C := zpowers_le.mpr P.centralizes_factor
  have hDB : D ≤ centralizer (B : Set G) := by
    apply zpowers_le.mpr
    intro b hb
    exact mem_centralizer_singleton_iff.mp hb.2
  have hsplit : C = A ⊔ D := by
    apply (eq_of_le_of_card_ge (sup_le hlt.le hDC) ?_).symm
    rw [hCc hlt,card_sup_zpowers_of_normalizing_involution A P.element
      (by rw [← P.point_order]; exact pow_orderOf_eq_one _) P.outside_factor
      (_root_.centralizer_le_normalizer A P.centralizes_factor),hA.card]
  have hnotA : ¬ A ≤ Q := by
    intro hAQ
    let Y := (pResidual 2 F.H).map F.H.subtype
    have hYd : Y ≤ P.globalCentralizer := by
      have hh := source_factor_residual_centralizes_supplement_of_strict_centralizer
        hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
        A hA.le_core hA.seed_le hA.card hA.intersection_card hA.normalized hlt
      exact hh.trans (centralizer_le (Set.singleton_subset_iff.mpr P.mem_supplement))
    have hTH : (T : Subgroup G) ≤ F.H := F.invariant 1
    have hjoin : Y ⊔ (T : Subgroup G) = F.H := by
      have hh := congrArg (map F.H.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTH))
      simpa only [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH,
        ← MonoidHom.range_eq_map,range_subtype] using hh
    have hUV : F.U = conjugateSpanBy (rankTwoSeed T M) Y := by
      change conjugateSpanBy (rankTwoSeed T M) F.H = _
      rw [← hjoin]
      apply conjugateSpanBy_sup_of_normalizes_seed
      · simpa only [F.last] using F.invariant 2
      · exact hTH.trans (le_normalizer_embedded_pResidual 2 F.H)
    have hUQ : F.U ≤ Q := by
      rw [hUV]
      exact conjugateSpanBy_le (hA.seed_le.trans hAQ) (hYd.trans hnorm)
    have hUC : F.U ≤ C := hUQ.trans hQC
    apply hne
    exact le_centralizer_iff_isMulCommutative.mp
      (hUC.trans (C.le_centralizer.trans (centralizer_le hUC)))
  have hQA : Q ⊓ A = ⊥ := by
    rcases pointBlock_invariant_factor (factorBlock F (sourceResidual M Mc) A) A (Q ⊓ A)
      P.marking P.factor_map P.factor_le P.point P.point_action inf_le_right
      ((le_inf hBQ hBA).trans inf_normalizer_le_normalizer_inf) with hb | he
    · exact hb
    · exact False.elim (hnotA (he.symm ▸ (show Q ⊓ A ≤ Q from inf_le_left)))
  have hcomm : ⁅C,B⁆ ≤ A := by
    apply commutator_le.mpr
    intro c hc b hb
    have hp : c ∈ (A : Set G) * (D : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left A D
        (hDC.trans (_root_.centralizer_le_normalizer A)), ← hsplit]
      exact hc
    obtain ⟨a,ha,d,hd,rfl⟩ := hp
    have hdcomm : ⁅d,b⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hDB hd b hb).symm
    rw [commutatorElement_mul_left_eq_conj_mul,hdcomm,mul_one,mul_inv_cancel,one_mul]
    exact le_normalizer_iff_commutator_le_left.mp hBA (commutator_mem_commutator ha hb)
  have hQB : Q ≤ centralizer (B : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_antisymm _ bot_le
    rw [← hQA]
    exact le_inf (le_normalizer_iff_commutator_le_left.mp hBQ)
      ((commutator_mono hQC le_rfl).trans hcomm)
  have hACB : A ⊓ centralizer (B : Set G) = ⊥ :=
    pointBlock_factor_centralizer (factorBlock F (sourceResidual M Mc) A) A hA.card
      P.marking P.factor_map P.factor_le P.point P.point_action
  have hQD : Q ≤ D := by
    intro x hx
    have hp : x ∈ (A : Set G) * (D : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left A D
        (hDC.trans (_root_.centralizer_le_normalizer A)), ← hsplit]
      exact hQC hx
    obtain ⟨a,ha,d,hd,he⟩ := hp
    have haC : a ∈ centralizer (B : Set G) := by
      have hh := (centralizer (B : Set G)).mul_mem (hQB hx)
        ((centralizer (B : Set G)).inv_mem (hDB hd))
      simpa only [← he,mul_inv_cancel_right] using hh
    have ha1 : a = 1 := by
      have hh : a ∈ (⊥ : Subgroup G) := hACB ▸ ⟨ha,haC⟩
      exact hh
    have hdx : d = x := by simpa only [ha1,one_mul] using he
    exact hdx ▸ hd
  have hDQ : D ≤ Q := by
    apply le_pCoreIn_of_normalizes
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers,P.point_order]; decide))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
    have he : centralizer (zpowers P.element : Set G) = P.globalCentralizer := by
      rw [zpowers_eq_closure,centralizer_closure]
    exact he.ge.trans (_root_.centralizer_le_normalizer _)
  exact le_antisymm hQD hDQ

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
