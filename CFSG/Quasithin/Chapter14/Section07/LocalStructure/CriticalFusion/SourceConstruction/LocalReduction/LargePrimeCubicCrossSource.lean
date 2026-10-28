module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeCubicSplittingSource
public import Theory.GroupTheory.Commutator.SplitPair

/-!
# Crossed splittings on the original simultaneous-cubic witness

Write U = W C for the literal moved and fixed factors of the original
normal five-lift, and transport both factors by the selected endpoint g.
The pairing radical W V₁ contains A = [U,Uᵍ]. Splitting its commutator
in the two factors identifies A intersect C with V₁. Applying the same
calculation at the opposite endpoint forces [C,Cᵍ] = 1 and gives the
crossed identities [W,Cᵍ] = V₁ᵍ and [Wᵍ,C] = V₁.

Consequently A has distinct planes A intersect W and A intersect Wᵍ.
Their intersection is exactly [W,Wᵍ], of order two; this subgroup and
the two original point lines generate A. All subgroups are literal
ambient subgroups, before taking any quotient.

The final theorem constructs these identities on the original minimal
witness with its actual five-core quotient and full two-core action
kernel. It adds no local-recognition premise. These are restrictions on
the simultaneous-cubic branch; its exclusion, five-core vanishing and
the remaining reductions through 14.7.52 are still open.

Source: Aschbacher–Smith, 14.5.21(1) and the critical-pair calculation in
14.7.6, printed pp.1019 and 1044–1045, refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Subgroup Theory.GroupTheory Representation
open Chapter12.Section08 CriticalFusion.Source
open Chapter15.Section03.AbelianAmalgam
open Chapter14.Section06.OddCriticalPair.Selection
open Chapter14.Section04.LargerDimension.LocalAction.Components
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]

local instance {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
    (I : Subgroup G) [hU : IsElementaryAbelian 2 (F.UH I)] :
    IsElementaryAbelian 2 (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).UH := hU

/-- Apply the two splittings at the literal critical endpoints. -/
theorem local_split_crossed_points
    {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
    (I : Subgroup G) [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1))
    (hf : (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).Hypothesis)
    (c : SelectedQuadraticEndpoint hf a) (hb : 3 ≤ hf.b)
    (W C : Subgroup G) (hIW : I ≤ normalizer (W : Set G))
    (hIC : I ≤ normalizer (C : Set G))
    (hsplit : W ⊔ C = F.UH I) (hdis : W ⊓ C = ⊥)
    (hZC : F.Vi 1 ≤ C)
    (hrad : W ⊔ F.Vi 1 = F.UH I ⊓ centralizer (I.pCoreIn 2 : Set G))
    (hbase : F.Vi 1 ≤ ⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆)
    (hopp : c.endpoint.conjugate (F.Vi 1) ≤ ⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆)
    (hne : F.Vi 1 ≠ c.endpoint.conjugate (F.Vi 1))
    (hcard : Nat.card (⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆ : Subgroup G) = 8)
    (hcentral : I.pCoreIn 2 ≤ centralizer ((⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆ : Subgroup G) : Set G))
    (hcentralOpp : (c.endpoint.conjugate I).pCoreIn 2 ≤
      centralizer ((⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆ : Subgroup G) : Set G)) :
    let A := ⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆
    ⁅C,c.endpoint.conjugate (F.UH I)⁆ = F.Vi 1 ∧
    ⁅c.endpoint.conjugate C,F.UH I⁆ = c.endpoint.conjugate (F.Vi 1) ∧
    ⁅C,c.endpoint.conjugate C⁆ = ⊥ ∧
    ⁅W,c.endpoint.conjugate C⁆ = c.endpoint.conjugate (F.Vi 1) ∧
    ⁅c.endpoint.conjugate W,C⁆ = F.Vi 1 ∧
    c.endpoint.conjugate (F.Vi 1) ≤ W ∧ F.Vi 1 ≤ c.endpoint.conjugate W ∧
    A ⊓ C = F.Vi 1 ∧ A ⊓ c.endpoint.conjugate C = c.endpoint.conjugate (F.Vi 1) ∧
    (A ⊓ W) ⊔ F.Vi 1 = A ∧
    (A ⊓ c.endpoint.conjugate W) ⊔ c.endpoint.conjugate (F.Vi 1) = A ∧
    Nat.card (A ⊓ W : Subgroup G) = 4 ∧
    Nat.card (A ⊓ c.endpoint.conjugate W : Subgroup G) = 4 ∧
    A ⊓ W ≠ A ⊓ c.endpoint.conjugate W ∧
    (⁅W,c.endpoint.conjugate W⁆ ⊔ c.endpoint.conjugate (F.Vi 1)) ⊔ F.Vi 1 = A ∧
    A ⊓ W ⊓ c.endpoint.conjugate W = ⁅W,c.endpoint.conjugate W⁆ ∧
    Nat.card (⁅W,c.endpoint.conjugate W⁆ : Subgroup G) = 2 := by
  let U := F.UH I
  let A := ⁅U,c.endpoint.conjugate U⁆
  let e := (MulAut.conj c.endpoint.representative).toMonoidHom
  have hWU : W ≤ U := le_sup_left.trans hsplit.le
  have hCU : C ≤ U := le_sup_right.trans hsplit.le
  have hUU : U ≤ centralizer (U : Set G) := le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hWC : W ≤ centralizer (C : Set G) := hWU.trans (hUU.trans (centralizer_le hCU))
  have hUopI : c.endpoint.conjugate U ≤ I :=
    (map_mono (conjugateSpanBy_mono hf.plus_le le_rfl)).trans (c.endpoint.large_le hb)
  have hUIop : U ≤ c.endpoint.conjugate I :=
    (conjugateSpanBy_mono hf.plus_le le_rfl).trans (c.endpoint.reverse_le hb)
  have hUIopW : U ≤ normalizer (c.endpoint.conjugate W : Set G) := by
    have hn := map_mono (f := e) hIW
    rw [map_equiv_normalizer_eq] at hn
    exact hUIop.trans hn
  have hUIopC : U ≤ normalizer (c.endpoint.conjugate C : Set G) := by
    have hn := map_mono (f := e) hIC
    rw [map_equiv_normalizer_eq] at hn
    exact hUIop.trans hn
  have hWCop : c.endpoint.conjugate W ≤ centralizer (c.endpoint.conjugate C : Set G) := by
    have hh := map_mono (f := e) hWC
    rw [map_centralizer_equiv] at hh
    exact hh
  have hsop : c.endpoint.conjugate W ⊔ c.endpoint.conjugate C = c.endpoint.conjugate U := by
    simpa only [Subgroup.map_sup] using congrArg (map e) hsplit
  have hradop : c.endpoint.conjugate W ⊔ c.endpoint.conjugate (F.Vi 1) =
      c.endpoint.conjugate U ⊓ centralizer ((c.endpoint.conjugate I).pCoreIn 2 : Set G) := by
    have hh := congrArg (map e) hrad
    rw [Subgroup.map_sup,map_inf _ _ _ (MulAut.conj c.endpoint.representative).injective,
      map_centralizer_equiv] at hh
    change c.endpoint.conjugate W ⊔ c.endpoint.conjugate (F.Vi 1) =
      c.endpoint.conjugate U ⊓ centralizer ((I.pCoreIn 2).map e : Set G) at hh
    rw [map_pCoreIn_of_injective 2 I e
      (MulAut.conj c.endpoint.representative).injective] at hh
    exact hh
  have hAU : A ≤ U := le_normalizer_iff_commutator_le_left.mp (hUopI.trans a.normalizes)
  have hAUop : A ≤ c.endpoint.conjugate U := by
    apply le_normalizer_iff_commutator_le_right.mp
    have hn := map_mono (f := e) a.normalizes
    rw [map_equiv_normalizer_eq] at hn
    exact hUIop.trans hn
  have hAR : A ≤ W ⊔ F.Vi 1 :=
    (le_inf hAU (le_centralizer_iff.mp hcentral)).trans hrad.ge
  have hARop : A ≤ c.endpoint.conjugate W ⊔ c.endpoint.conjugate (F.Vi 1) :=
    (le_inf hAUop (le_centralizer_iff.mp hcentralOpp)).trans hradop.ge
  have hz : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  have hzop : Nat.card (c.endpoint.conjugate (F.Vi 1)) = 2 :=
    (card_map_of_injective (MulAut.conj c.endpoint.representative).injective).trans hz
  have hZZ : Disjoint (F.Vi 1) (c.endpoint.conjugate (F.Vi 1)) :=
    disjoint_iff.mpr (inf_eq_bot_of_card_two_of_ne _ _ hz hzop hne)
  have hd : Disjoint W C := disjoint_iff.mpr hdis
  have hdop : Disjoint (c.endpoint.conjugate W) (c.endpoint.conjugate C) :=
    disjoint_map (MulAut.conj c.endpoint.representative).injective hd
  have hZCop : c.endpoint.conjugate (F.Vi 1) ≤ c.endpoint.conjugate C := map_mono hZC
  have hp := split_commutator_point U W C (F.Vi 1) (c.endpoint.conjugate U)
    hWC hd hsplit hZC (hUopI.trans hIW) (hUopI.trans hIC) hAR hbase
  have hpop := split_commutator_point (c.endpoint.conjugate U)
    (c.endpoint.conjugate W) (c.endpoint.conjugate C) (c.endpoint.conjugate (F.Vi 1)) U
    hWCop hdop hsop hZCop hUIopW hUIopC
    (commutator_comm U (c.endpoint.conjugate U) ▸ hARop)
    (commutator_comm U (c.endpoint.conjugate U) ▸ hopp)
  rw [commutator_comm (c.endpoint.conjugate U) U] at hpop
  obtain ⟨hCZ,hCZop,hCC,hWZop,hWZ,hZopW,hZWop⟩ :=
    split_commutator_pair_points U W C (F.Vi 1) (c.endpoint.conjugate U)
      (c.endpoint.conjugate W) (c.endpoint.conjugate C) (c.endpoint.conjugate (F.Vi 1))
      hWC hd hsplit hZC hWCop hdop hsop hZCop
      (hUopI.trans hIW) (hUopI.trans hIC) hUIopW hUIopC hAR hARop hbase hopp hZZ
  have hP : Nat.card (A ⊓ W : Subgroup G) = 4 := by
    have hn : F.Vi 1 ≤ normalizer ((A ⊓ W : Subgroup G) : Set G) :=
      (hZC.trans ((le_centralizer_iff.mp hWC).trans (centralizer_le inf_le_right))).trans
        (Subgroup.centralizer_le_normalizer _)
    have hh := card_sup_eq_mul_of_normalizes_of_disjoint (A ⊓ W) (F.Vi 1) hn hp.2.2.2.2
    rw [hp.2.2.2.1,hcard,hz] at hh
    omega
  have hPop : Nat.card (A ⊓ c.endpoint.conjugate W : Subgroup G) = 4 := by
    have hn : c.endpoint.conjugate (F.Vi 1) ≤
        normalizer ((A ⊓ c.endpoint.conjugate W : Subgroup G) : Set G) :=
      (hZCop.trans ((le_centralizer_iff.mp hWCop).trans (centralizer_le inf_le_right))).trans
        (Subgroup.centralizer_le_normalizer _)
    have hh := card_sup_eq_mul_of_normalizes_of_disjoint
      (A ⊓ c.endpoint.conjugate W) (c.endpoint.conjugate (F.Vi 1)) hn hpop.2.2.2.2
    rw [hpop.2.2.2.1,hcard,hzop] at hh
    omega
  have hgen := split_commutator_pair_generation U W C (F.Vi 1)
    (c.endpoint.conjugate U) (c.endpoint.conjugate W) (c.endpoint.conjugate C)
    (c.endpoint.conjugate (F.Vi 1)) hWC hsplit hWCop hsop (hUopI.trans hIC)
    hUIopC hCZ hWZop
  let M := ⁅W,c.endpoint.conjugate W⁆
  have hMop : M ≤ c.endpoint.conjugate W :=
    le_normalizer_iff_commutator_le_right.mp (hWU.trans hUIopW)
  have hMZ : Disjoint M (c.endpoint.conjugate (F.Vi 1)) := hdop.mono hMop hZCop
  have hMP : M ⊔ c.endpoint.conjugate (F.Vi 1) = A ⊓ W := by
    have hh := commutator_sup_of_commuting_factors (c.endpoint.conjugate W)
      (c.endpoint.conjugate C) W hWCop (hWU.trans hUIopC)
    rw [hsop,commutator_comm (c.endpoint.conjugate U) W,
      commutator_comm (c.endpoint.conjugate W) W,
      commutator_comm (c.endpoint.conjugate C) W,hWZop,hp.2.2.1] at hh
    exact hh.symm
  have hmiddle : A ⊓ W ⊓ c.endpoint.conjugate W = M := by
    have hh := sup_inf_sup_eq_of_disjoint_commuting_factors
      (c.endpoint.conjugate W) (c.endpoint.conjugate C)
      M (c.endpoint.conjugate (F.Vi 1)) (c.endpoint.conjugate W) ⊥
      hdop hWCop hMop hZCop le_rfl bot_le
    simpa only [sup_bot_eq,inf_bot_eq,sup_bot_eq,inf_eq_left.mpr hMop,hMP] using hh
  have hMcard : Nat.card M = 2 := by
    have hn : c.endpoint.conjugate (F.Vi 1) ≤ normalizer (M : Set G) :=
      (hZCop.trans ((le_centralizer_iff.mp hWCop).trans (centralizer_le hMop))).trans
        (Subgroup.centralizer_le_normalizer _)
    have hh := card_sup_eq_mul_of_normalizes_of_disjoint M
      (c.endpoint.conjugate (F.Vi 1)) hn hMZ
    rw [hMP,hP,hzop] at hh
    omega
  refine ⟨hCZ,hCZop,hCC,hWZop,hWZ,hZopW,hZWop,hp.1,hpop.1,
    hp.2.2.2.1,hpop.2.2.2.1,hP,hPop,?_,hgen,hmiddle,hMcard⟩
  intro he
  have hZopWop : c.endpoint.conjugate (F.Vi 1) ≤ c.endpoint.conjugate W :=
    (le_inf hopp hZopW).trans (he.le.trans inf_le_right)
  have hzbot : c.endpoint.conjugate (F.Vi 1) = ⊥ :=
    bot_unique ((le_inf hZopWop hZCop).trans (disjoint_iff.mp hdop).le)
  rw [hzbot,card_bot] at hzop
  omega

/-- On the original surviving witness, both fixed eights commute and
both original points lie in the opposite moved summands. The common eight
has two distinct literal moved planes of order four, whose intersection is
the order-two commutator of the moved summands. -/
theorem local_minimal_five_crossed_splitting
    {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hne : pCore 5 (HStar J) ≠ ⊥) :
    ∃ I : Subgroup G, I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      pCore 5 (HStar I) ≠ ⊥ ∧
      (∀ E : Subgroup G, E ∈ F.Hz L (normalizer (L : Set G)) → E < I →
        pCore 5 (HStar E) = ⊥) ∧
      ∃ hU : IsElementaryAbelian 2 (F.UH I),
        let := hU
        ∃ a : LocalQuotientAction I (F.UH I) (F.Vi 1),
          let : IsElementaryAbelian 2 (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).UH := hU
          ∃ hf : (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).Hypothesis,
            ∃ c : SelectedQuadraticEndpoint hf a,
              c.endpoint.representative ∉ F.H ∧
              let A := ⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆
              Nat.card A = 8 ∧ F.Vi 1 ≤ A ∧ c.endpoint.conjugate (F.Vi 1) ≤ A ∧
              F.Vi 1 ≠ c.endpoint.conjugate (F.Vi 1) ∧
              I.pCoreIn 2 ≤ centralizer (A : Set G) ∧
              (c.endpoint.conjugate I).pCoreIn 2 ≤ centralizer (A : Set G) ∧
              ∃ Y : Subgroup I,
                Y.Normal ∧ IsPPerfect 2 Y ∧
                Y.map (QuotientGroup.mk' (pCore 2 I)) = pCore 5 (HStar I) ∧
                ((QuotientGroup.mk' (pCore 2 I)).comp Y.subtype).ker = pCore 2 Y ∧
                Nonempty ((Y ⧸ pCore 2 Y) ≃* pCore 5 (HStar I)) ∧
                ¬ Y.map I.subtype ≤ normalizer (L : Set G) ∧
                I = Y.map I.subtype ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) ∧
                (((F.UH I).normalizerMonoidHom.comp (inclusion a.normalizes)).comp Y.subtype).ker =
                  pCore 2 Y ∧
                let W := ⁅F.UH I,Y.map I.subtype⁆
                let C := F.UH I ⊓ centralizer (Y.map I.subtype : Set G)
                I ≤ normalizer (W : Set G) ∧ I ≤ normalizer (C : Set G) ∧
                W ⊔ C = F.UH I ∧ W ⊓ C = ⊥ ∧
                V ⊔ W = F.UH I ∧ V ⊓ W = ⊥ ∧ Nat.card C = 8 ∧
                V ⊓ C = F.Vi 1 ∧ C ≠ V ∧
                W ⊔ F.Vi 1 = F.UH I ⊓ centralizer (I.pCoreIn 2 : Set G) ∧
                ⁅C,c.endpoint.conjugate (F.UH I)⁆ = F.Vi 1 ∧
                ⁅c.endpoint.conjugate C,F.UH I⁆ = c.endpoint.conjugate (F.Vi 1) ∧
                ⁅C,c.endpoint.conjugate C⁆ = ⊥ ∧
                ⁅W,c.endpoint.conjugate C⁆ = c.endpoint.conjugate (F.Vi 1) ∧
                ⁅c.endpoint.conjugate W,C⁆ = F.Vi 1 ∧
                c.endpoint.conjugate (F.Vi 1) ≤ W ∧ F.Vi 1 ≤ c.endpoint.conjugate W ∧
                A ⊓ C = F.Vi 1 ∧ A ⊓ c.endpoint.conjugate C = c.endpoint.conjugate (F.Vi 1) ∧
                (A ⊓ W) ⊔ F.Vi 1 = A ∧
                (A ⊓ c.endpoint.conjugate W) ⊔ c.endpoint.conjugate (F.Vi 1) = A ∧
                Nat.card (A ⊓ W : Subgroup G) = 4 ∧
                Nat.card (A ⊓ c.endpoint.conjugate W : Subgroup G) = 4 ∧
                A ⊓ W ≠ A ⊓ c.endpoint.conjugate W ∧
                (⁅W,c.endpoint.conjugate W⁆ ⊔ c.endpoint.conjugate (F.Vi 1)) ⊔ F.Vi 1 = A ∧
                A ⊓ W ⊓ c.endpoint.conjugate W = ⁅W,c.endpoint.conjugate W⁆ ∧
                Nat.card (⁅W,c.endpoint.conjugate W⁆ : Subgroup G) = 2 := by
  obtain ⟨I,hIJ,hI,hneI,hmin,hU,a,hf,c,hout,_f,_i,_hAi,_hAc,_hpre,_hCE,hAc,
      hbase,hopp,hnep,_htwo,hcentral,hcentralOpp⟩ :=
    local_minimal_five_simultaneous_cubic h hab structural previous faithful J hJ hne
  let := hU
  let : IsElementaryAbelian 2
      (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).UH := hU
  obtain ⟨Y,hYn,hYp,hYm,hYk,he,hYout,hgen,_hU',_a',hk,hIW,hIC,hsplit,hdis,
      hVW,hVWdis,hCc,hVC,hCV,hrad⟩ :=
    local_minimal_five_split_lift h hab structural previous faithful I hI hneI hmin
  have hZC : F.Vi 1 ≤ F.UH I ⊓ centralizer (Y.map I.subtype : Set G) :=
    hVC.ge.trans inf_le_right
  have hb : 3 ≤ hf.b := (local_f9_critical_bounds h hab structural previous I hI).1
  have hcross := local_split_crossed_points I a hf c hb
    ⁅F.UH I,Y.map I.subtype⁆ (F.UH I ⊓ centralizer (Y.map I.subtype : Set G))
    hIW hIC hsplit hdis hZC hrad hbase hopp hnep hAc hcentral hcentralOpp
  exact ⟨I,hIJ,hI,hneI,hmin,hU,a,hf,c,hout,hAc,hbase,hopp,hnep,hcentral,hcentralOpp,
    Y,hYn,hYp,hYm,hYk,he,hYout,hgen,hk,hIW,hIC,hsplit,hdis,hVW,hVWdis,hCc,hVC,hCV,hrad,hcross⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
