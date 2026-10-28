module
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalTildeGeometry
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryParabolic
public import Theory.GroupTheory.ReducedNormal.MinimalMoved
public import Theory.GroupTheory.CentralPChiefFactorsOddQuotient

/-!
# The original minimal module for a kernel component

For the actual simple-component branch, the corrected quotient-centralizer
preimage yields a nonzero elementary displacement fully moved by K. Its
simple quotient is perfect, so its two-chief factors are central. The minimal
reduced-subgroup lemma gives a normal module inside that displacement.
Coprime splitting on L₁/O₂(L₁) makes the same module fully moved by L₁.
The displacement lies in the literal U₂ of the source.

Source: Aschbacher--Smith 13.7.4(1), printed pp.937--938, using A.4.11.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

theorem source_primitive_component_minimal_tilde_module
    (d : Section08.SourceCompletion.NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hm : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥)
    (J : Subgroup H)
    (hJC : J.map H.subtype ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hJn : H ≤ normalizer (J.map H.subtype : Set G))
    (hp : IsPPerfect 2 (J.map H.subtype)) (hout : ¬ J.map H.subtype ≤ M)
    (hJ : J.IsCComponent) (hs : IsSimpleGroup (J ⧸ pCore 2 J))
    (hcomm : ⁅J.map H.subtype,(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁⁆ ≤
      (J.map H.subtype).pCoreIn 2) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let K := J.map H.subtype
    let X := K ⊔ (F.L₁ ⊔ (T : Subgroup G))
    let W := commutatorPreimage F.UH (F.L₁.pCoreIn 2) F.V₁
    let R := ⁅W,K⁆
    let D := ⁅R,F.L₁⁆
    let U₂ := ⁅⁅fixedLayer F,F.L₁⁆,K⁆
    ∃ U : Subgroup X, U ≤ D.subgroupOf X ∧ U ≤ U₂.subgroupOf X ∧
      IsPReduced 2 U ∧ U ≠ ⊥ ∧ ⁅U,K.subgroupOf X⁆ = U ∧
      ⁅U,F.L₁.subgroupOf X⁆ = U ∧
      ∀ A : Subgroup X, A ≤ U → A.Normal → ⁅A,K.subgroupOf X⁆ ≠ ⊥ → A = U := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let K := J.map H.subtype
  let X := K ⊔ (F.L₁ ⊔ (T : Subgroup G))
  let W := commutatorPreimage F.UH (F.L₁.pCoreIn 2) F.V₁
  let R := ⁅W,K⁆
  let D := ⁅R,F.L₁⁆
  let U₂ := ⁅⁅fixedLayer F,F.L₁⁆,K⁆
  let KX := K.subgroupOf X
  have hKX : K ≤ X := le_sup_left
  have hXH : X ≤ H := sup_le (hJC.trans (kernel_le_H (D := F))) h.local_le
  let : KX.Normal := normal_subgroupOf_of_le_normalizer (hXH.trans hJn)
  let : (K.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hJn
  obtain ⟨hRU,hDR,hRX,hDX,hRn,hDn,hRE,hDE,hDne,hcoreR,hgen⟩ :=
    source_kernel_tilde_module d h1221 h hU eL hm hJC hJn hp hout hcomm
  let := hRn
  let := hDn
  let := hRE
  let := hDE
  let eK : KX ≃* K := subgroupOfEquivOfLe hKX
  let eJ : J ≃* K := J.equivMapOfInjective H.subtype H.subtype_injective
  let e : KX ≃* J := eK.trans eJ.symm
  have hpX : IsPPerfect 2 KX := hp.of_surjective eK.symm.toMonoidHom eK.symm.surjective
  let Q := KX ⧸ pCore 2 KX
  let eQ : Q ≃* J ⧸ pCore 2 J := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let : Group.IsPerfect J := hJ.perfect
  let : Group.IsPerfect KX := Group.IsPerfect.ofSurjective (f:=e.symm.toMonoidHom) e.symm.surjective
  let : Group.IsPerfect Q := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  let : IsSimpleGroup Q := eQ.isSimpleGroup
  have hzQ : center Q=⊥ := by
    rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with hz | hz
    · exact hz
    · exact (Group.IsPerfect.not_isMulCommutative Q (center_eq_top_iff.mp hz)).elim
  let : IsQuasisimple Q := {
    toIsPerfect := inferInstance
    simple := ((QuotientGroup.quotientMulEquivOfEq hzQ).trans QuotientGroup.quotientBot).isSimpleGroup }
  have hchief : HasCentralPChiefFactorsAbove 2 (pCore 2 KX) :=
    (hasCentralPChiefFactorsAbove_iff_quotient _).mpr
      (hasCentralTwoChiefFactors_of_odd_normal_quasisimple_quotient (⊥ : Subgroup Q)
        (by simp) (IsQuasisimple.of_mulEquiv QuotientGroup.quotientBot.symm))
  have hKne : K ≠ ⊥ := by
    intro he
    apply hout
    change K ≤ M
    rw [he]
    exact bot_le
  have hkillK : K.pCoreIn 2 ≤ centralizer (fixedLayer F : Set G) :=
    (subnormal_kernel_structure h hJC (inferInstance : (K.subgroupOf H).Normal).isSubnormal
      hp hKne).2.2.2.2
  have hcoremap : (KX.pCoreIn 2).map X.subtype = K.pCoreIn 2 := by
    rw [map_pCoreIn_of_ker_isPGroup X.subtype
      (by rw [X.ker_subtype]; exact IsPGroup.of_bot),
      map_subgroupOf_eq_of_le hKX]
  have hkillX : KX.pCoreIn 2 ≤ centralizer (D.subgroupOf X : Set X) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro u hu
    apply Subtype.ext
    have hxK : (x : G) ∈ K.pCoreIn 2 := hcoremap ▸ mem_map_of_mem X.subtype hx
    exact (mem_centralizer_iff.mp (hkillK hxK)) u.val (hRU (hDR hu))
  have hmove : ⁅D.subgroupOf X,KX⁆ ≠ ⊥ := by rwa [hgen]
  obtain ⟨U,hUD,hred,hUne,hUK,hmin⟩ :=
    exists_minimal_isPReduced_le_of_normal_moved KX (D.subgroupOf X) hpX hchief hkillX hmove
  let := hred.normal
  let := hred.elementary
  let LX := F.L₁.subgroupOf X
  have hLX : F.L₁ ≤ X := le_sup_left.trans le_sup_right
  have hcardL : Nat.card (F.L₁ ⧸ pCore 2 F.L₁)=3 := by
    rw [source_local_residual_eq d h]
    exact Section03.Noncentrality.ordinary_point_residual_quotient_card d eL
  let eLX := subgroupOfEquivOfLe hLX
  have hcardLX : Nat.card (LX ⧸ pCore 2 LX)=3 := by
    rw [Nat.card_congr (QuotientGroup.congr _ _ eLX (pCore_map_iso 2 eLX)).toEquiv]
    exact hcardL
  have hcoreLmap : (LX.pCoreIn 2).map X.subtype=F.L₁.pCoreIn 2 := by
    rw [map_pCoreIn_of_ker_isPGroup X.subtype
      (by rw [X.ker_subtype];exact IsPGroup.of_bot),map_subgroupOf_eq_of_le hLX]
  have hcoreLX : LX.pCoreIn 2 ≤ centralizer (R.subgroupOf X : Set X) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    exact (mem_centralizer_iff.mp (hcoreR (hcoreLmap ▸ mem_map_of_mem X.subtype hx))) y.val hy
  have hdisp : ⁅R.subgroupOf X,LX⁆=D.subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hRX,map_subgroupOf_eq_of_le hLX,
      map_subgroupOf_eq_of_le hDX]
  have hz : ∃z∈LX,orderOf z=3 := by
    have hd : 3 ∣ Nat.card LX := by
      rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 LX),hcardLX]
      exact dvd_mul_right _ _
    obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G:=LX) 3 hd
    exact ⟨z,z.property,(orderOf_injective LX.subtype LX.subtype_injective z).trans hz⟩
  have hUL : ⁅U,LX⁆=U := commutator_eq_self_of_le_cubic_displacement
    (R.subgroupOf X) LX U (IsElementaryAbelian.isPGroup 2 _)
    hcoreLX hcardLX hz (hUD.trans_eq hdisp.symm)
  have hDU : D ≤ U₂ := source_tilde_displacement_le_mixed d h hJC hJn hp hcomm
  exact ⟨U,hUD,hUD.trans (subgroupOf_mono X hDU),hred,hUne,hUK,hUL,hmin⟩

end CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
