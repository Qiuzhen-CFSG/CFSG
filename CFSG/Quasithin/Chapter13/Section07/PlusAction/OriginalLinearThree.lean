module
public import Theory.SpecificGroups.PSL3Two.Automorphisms.SylowStabilizer
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalKernelSylow
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalComponentExclusion
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalCubicExclusion
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalSelectedModels

/-!
# The original PSL₃(2) kernel row is impossible

The plus kernel meets the point parabolic in a two-group. For its normal
PSL₃(2) component this intersection is Sylow, so the point parabolic
preserves that Sylow and its image in the component quotient. The full
automorphism stabilizer of a PSL₃(2) Sylow is a two-group. Thus the
two-perfect point residual acts trivially on the quotient, supplying the
centralization premise of the checked reduced-module contradiction.

The final theorem combines the cubic exclusion and the earlier five-model
list: a nonfaithful ordinary plus kernel must have an A₅ component. The
Baumann normalizer bound and Source1332OneTwo remain genuine earlier
source inputs, and the A₅ module marking remains the final kernel branch.
Source: Aschbacher–Smith 13.7.4(1), printed pp.937–938.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- The original point residual centralizes a PSL₃(2) kernel component modulo its core. -/
theorem source_primitive_linearThree_centralized
    (d : Section08.SourceCompletion.NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (J : Subgroup H) (hJ : J.IsCComponent) (hs : IsSimpleGroup (J ⧸ pCore 2 J))
    (hJC : J.map H.subtype ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hl : ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 3 2) :
    ⁅J.map H.subtype,(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁⁆ ≤
      (J.map H.subtype).pCoreIn 2 := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let K := J.map H.subtype
  let P := F.L₁ ⊔ (T : Subgroup G)
  have hKn := (source_primitive_kernel_normal_of_small_model d h hne J hJ hs hJC
    (Or.inr hl)).2
  have hPK : P ≤ normalizer (K : Set G) := h.local_le.trans hKn
  have hKP : IsPGroup 2 (K ⊓ P : Subgroup G) :=
    (isPGroup_pCoreIn 2 P).to_le ((inf_le_inf_right P hJC).trans
      (source_kernel_inf_point_le_radical d h eL hne))
  obtain ⟨F₀,hF,hfin,hcard,⟨f⟩⟩ := hl
  let := hF
  let := hfin
  let := Fintype.ofFinite F₀
  let ef : F₀ ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F₀ Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hcard)).symm
  let eJ := J.equivMapOfInjective H.subtype H.subtype_injective
  let e : (K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.SL :=
    (QuotientGroup.congr _ _ eJ.symm (pCore_map_iso 2 eJ.symm)).trans
      ((f.trans (Atlas.fieldEquivPSL 3 ef)).trans Matrix.PSL3Two.equiv.symm)
  let q₀ := QuotientGroup.mk' (pCore 2 K)
  let q := e.toMonoidHom.comp q₀
  let a : P →* MulAut Matrix.PSL3Two.SL := (MulAut.congr e).toMonoidHom.comp
    ((quotientAut (pCore 2 K)).comp (K.normalizerMonoidHom.comp (inclusion hPK)))
  have ha (x : P) (k : K) : a x (q k) =
      q (K.normalizerMonoidHom ⟨x,hPK x.property⟩ k) := by
    change e ((quotientAut (pCore 2 K) (K.normalizerMonoidHom
      ⟨x,hPK x.property⟩)) (e.symm (e (q₀ k)))) = _
    rw [e.symm_apply_apply,quotientAut_apply_mk]
    rfl
  have htriv := Subgroup.NormalSylowQuotientAction.pPerfect_action_eq_one T K P F.L₁
    hPK le_sup_right hKP le_sup_left (isPPerfect_embedded_pResidual 2 _)
    q (e.surjective.comp (QuotientGroup.mk'_surjective _)) a ha
    Matrix.PSL3Two.automorphism_sylow_stabilizer_two
  rw [commutator_comm]
  apply commutator_le.mpr
  intro l hl k hk
  let l' : F.L₁ := ⟨l,hl⟩
  let k' : K := ⟨k,hk⟩
  let n : K := K.normalizerMonoidHom
    ⟨l,hPK (show l ∈ P from mem_sup_left hl)⟩ k'
  have hfix : q n = q k' := by
    have hh := congrArg (fun b : MulAut Matrix.PSL3Two.SL => b (q k')) (htriv l')
    rw [ha] at hh
    exact hh
  have hfix₀ : q₀ n = q₀ k' := e.injective hfix
  have hcore : n * k'⁻¹ ∈ pCore 2 K := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q₀ (n * k'⁻¹) = 1
    rw [map_mul,map_inv,hfix₀,mul_inv_cancel]
  exact mem_map_of_mem K.subtype hcore

/-- The PSL₃(2) kernel row is excluded with normality, escape and centralization proved. -/
theorem source_primitive_linearThree_false_of_source
    (d : Section08.SourceCompletion.NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (hm : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥)
    (J : Subgroup H) (hJ : J.IsCComponent) (hs : IsSimpleGroup (J ⧸ pCore 2 J))
    (hJC : J.map H.subtype ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hB : normalizer (ChapterB.baumann
      (((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔
        (T : Subgroup G)).pCoreIn 2) : Set G) ≤ M)
    (hl : ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 3 2) : False := by
  have hJn := (source_primitive_kernel_normal_of_small_model d h hne J hJ hs hJC
    (Or.inr hl)).2
  have hd : 3 ∣ Nat.card (J ⧸ pCore 2 J) := by
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hl
    rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.card_projective,hF]
    norm_num
  have hout := source_primitive_kernel_not_le_local_of_three_dvd d h1221 h eL hne
    J hJ hs hJC hd
  have hnot : ¬ (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ≤ J.map H.subtype :=
    fun hh => local_residual_not_le_kernel d h hne (hh.trans hJC)
  let : Group.IsPerfect J := hJ.perfect
  let : Group.IsPerfect (J.map H.subtype) := Group.IsPerfect.ofSurjective
    (H.subtype.subgroupMap_surjective J)
  have hp : IsPPerfect 2 (J.map H.subtype) := by
    intro N hN hq
    let := hN
    by_contra hne
    let : Nontrivial ((J.map H.subtype) ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsPerfect ((J.map H.subtype) ⧸ N) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    let : Group.IsNilpotent ((J.map H.subtype) ⧸ N) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable ((J.map H.subtype) ⧸ N) inferInstance
  exact source_primitive_linearThree_false d h1221 h hU eL hm J hJ hs hJC hJn hp hout
    hnot (source_primitive_linearThree_centralized d h eL hne J hJ hs hJC hl) hB hl

/-- All nonfaithful kernel rows except the original A₅ module branch are excluded. -/
theorem source_ordinary_kernel_alternatingFive_branch
    (d : Section08.SourceCompletion.NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (hm : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥)
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hk : kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) ≠ H.pCoreIn 2)
    (hB : normalizer (ChapterB.baumann
      (((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔
        (T : Subgroup G)).pCoreIn 2) : Set G) ≤ M)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    ∃ J : Subgroup H, let K := J.map H.subtype
      K ≤ kernel F ∧ IsPPerfect 2 K ∧ K ≠ ⊥ ∧ ¬ F.L₁ ≤ K ∧
      K ⊓ centralizer (fixedLayer F : Set G) = K.pCoreIn 2 ∧
      J.IsCComponent ∧ IsSimpleGroup (J ⧸ pCore 2 J) ∧
      J.Normal ∧ H ≤ normalizer (K : Set G) ∧
      Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨J,hJC,hp,hJne,hnot,hcent,hJ,hs⟩ :=
    source_ordinary_kernel_component_branch d h1221 h hU eL hne hm hV hk hB
  have hsub : ((J.map H.subtype).subgroupOf H).IsSubnormal := by
    change ((J.map H.subtype).comap H.subtype).IsSubnormal
    rw [comap_map_eq_self_of_injective H.subtype_injective]
    exact hJ.subnormal
  have hmove := (subnormal_kernel_structure h hJC hsub hp hJne).2.1
  obtain ⟨hmodels,hn,hJn⟩ := source_primitive_kernel_small_models_and_normal
    d h hU h1332 hne J hJ hs hJC hmove
  rcases hmodels with ha | hl
  · exact ⟨J,hJC,hp,hJne,hnot,hcent,hJ,hs,hn,hJn,ha⟩
  · exact (source_primitive_linearThree_false_of_source d h1221 h hU eL hne hm
      J hJ hs hJC hB hl).elim

end CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
