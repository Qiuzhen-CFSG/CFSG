module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentModel
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalComponentMaximal
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalComponentResidualMaximal

/-!
# TerminalComponentModel at the original ambient group and Sylow subgroup

These are the same source arguments as `TerminalComponentModel`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 Representation.BinaryOffender.Homogeneous

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

variable {S : Setup T L V} {D : S.LocalAnalysis}

namespace TerminalPoint

variable (P : TerminalPoint S D)

theorem moved_commutator_eq_source_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G)) :
    ⁅⁅P.Z,P.K⁆,P.K⁆ = ⁅P.Z,P.K⁆ := by
  let R := pResidual 2 P.H
  let e : R ≃* P.K := R.equivMapOfInjective P.H.subtype P.H.subtype_injective
  let : Group.IsPerfect P.K := Chapter1.mem_L_isPerfect
    (P.residual_local_and_quasisimple_at structural modules hr hw).1
  let : Group.IsPerfect R := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let U := (RecognitionSource.hstarOmegaModule T P.H).subgroupOf P.H
  let : U.Normal := (RecognitionSource.chosen_hstar_omega_reduced S.hypothesis P.minimal).normal
  have he : ⁅⁅U,R⁆,R⁆ = ⁅U,R⁆ := le_antisymm (commutator_le_left _ _)
    (commutator_le_of_iterated_le U R ⁅⁅U,R⁆,R⁆ le_rfl)
  have hh := congrArg (map P.H.subtype) he
  rw [map_commutator,map_commutator,
    map_subgroupOf_eq_of_le (RecognitionSource.hstarOmegaModule_le P.minimal.1.1.2)] at hh
  change ⁅⁅RecognitionSource.hstarOmegaModule T P.H,P.K⁆,P.K⁆ =
    ⁅RecognitionSource.hstarOmegaModule T P.H,P.K⁆ at hh
  simpa only [P.hstarOmega_commutator_eq] using hh

theorem maximal_moved_irrPlus_source_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G))
    (hm : P.K ∈ Chapter1.LStar G (T : Subgroup G)) :
    let := P.moved_elementary_source
    let f := ChapterD.UniqueFactor.actionHom P.H ⁅P.Z,P.K⁆ P.moved_module_normalized
    IsIrrPlus (ChapterD.UniqueFactor.imageRepresentation P.H ⁅P.Z,P.K⁆ P.moved_module_normalized)
      ((pResidual 2 P.H).map f.rangeRestrict) ⊤ := by
  let U := (⁅P.Z,P.K⁆ : Subgroup G).subgroupOf P.H
  let := P.moved_elementary_source
  let := P.moved_reduced.normal
  let := P.moved_reduced.elementary
  let f := ChapterD.UniqueFactor.actionHom P.H ⁅P.Z,P.K⁆ P.moved_module_normalized
  let q := f.rangeRestrict
  let ρ := ChapterD.UniqueFactor.imageRepresentation P.H ⁅P.Z,P.K⁆ P.moved_module_normalized
  let R := pResidual 2 P.H
  let e : R ≃* P.K := R.equivMapOfInjective P.H.subtype P.H.subtype_injective
  let b := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  obtain ⟨a⟩ := (P.maximal_residual_five_at structural modules hr hw hm).1
  have hsR := (Chapter3.sqtk_of_mem_H S.hypothesis.simpleQTKE P.minimal.1.1.1).subgroup R
  have hs : IsSQTK KnownSimple.IsKnownSimple (R ⧸ pCore 2 R) := by
    refine ⟨?_,hsR.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hsR.stronglyQuasithin p hp ho)
  have hker : q.ker = centralizer (U : Set P.H) := by
    rw [MonoidHom.ker_rangeRestrict,ChapterD.UniqueFactor.actionHom_ker]
    ext h
    constructor
    · intro hh w hw
      exact Subtype.ext (hh w hw)
    · intro hh w hw
      exact congrArg P.H.subtype (hh ⟨w,P.moved_le_hstar hw⟩ hw)
  have hmove : ⁅U,R⁆ ≠ ⊥ := by
    intro he
    apply P.residual_moves_moved_source_at structural
    apply le_centralizer_iff.mp
    apply commutator_eq_bot_iff_le_centralizer.mp
    have hh := congrArg (map P.H.subtype) he
    rwa [map_commutator,map_subgroupOf_eq_of_le P.moved_le_hstar,Subgroup.map_bot] at hh
  have hi := ChapterB.QuasisimpleSource.SourceCompletion.ff_reduced_five_residual_moved_irrPlus
    U P.moved_reduced (b.trans a) hs hmove
    q (MonoidHom.rangeRestrict_surjective f) hker ρ
    (ChapterD.UniqueFactor.imageRepresentation_injective _ _ _)
    (P.maximal_moved_isFF_source_at structural modules hr hw hm)
  have he : subspaceCommutator ρ ⊤ (R.map q) = ⊤ := by
    let B : Subgroup G :=
      (subspaceCommutator ρ ⊤ (R.map q)).toAddSubgroup.toSubgroup'.map (⁅P.Z,P.K⁆ : Subgroup G).subtype
    have hb : ⁅⁅P.Z,P.K⁆,P.K⁆ ≤ B := by
      rw [commutator_comm]
      apply commutator_le.mpr
      intro k hk w hw
      obtain ⟨r,hr,rfl⟩ := hk
      let v : Additive (⁅P.Z,P.K⁆ : Subgroup G) := Additive.ofMul ⟨w,hw⟩
      refine ⟨(ρ (q r) v - v).toMul,?_,?_⟩
      · change ρ (q r) v - v ∈ subspaceCommutator ρ ⊤ (R.map q)
        exact Submodule.subset_span ⟨q r,mem_map_of_mem q hr,v,Submodule.mem_top,rfl⟩
      · simp only [toMul_sub,div_eq_mul_inv]
        rfl
    rw [P.moved_commutator_eq_source_at structural modules hr hw] at hb
    apply top_unique
    intro v _
    obtain ⟨w,hw,he⟩ := hb v.toMul.property
    have hv : w = v.toMul := Subtype.ext he
    change Additive.ofMul w ∈ subspaceCommutator ρ ⊤ (R.map q) at hw
    simpa only [hv,ofMul_toMul] using hw
  change IsIrrPlus ρ (R.map q) (subspaceCommutator ρ ⊤ (R.map q)) at hi
  rwa [he] at hi

omit [Finite G] in

private theorem chosen_of_irrPlus_image_at
    {A B H : Subgroup G} (hH : B ⊔ (T : Subgroup G) = H)
    (hAH : A ≤ H) (hTK : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hn : H ≤ normalizer (A : Set G)) [IsElementaryAbelian 2 A]
    (hred : IsPReduced 2 (A.subgroupOf H))
    (hi : let f := ChapterD.UniqueFactor.actionHom H A hn
      IsIrrPlus (ChapterD.UniqueFactor.imageRepresentation H A hn)
        ((B.subgroupOf H).map f.rangeRestrict) ⊤) :
    Nonempty (ChosenModule T B A) := by
  subst H
  let H := B ⊔ (T : Subgroup G)
  let R := ReducedModule H
  let j : A →* R := {
    toFun a := ⟨⟨a,hAH a.property⟩,hred.le_reducedPSubgroup a.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  let e := j.toAdditive.toZModLinearMap 2
  have he : Function.Injective e := by
    intro x y h
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg (fun z : Additive R => (z.toMul.val.val : G)) h
  let f := ChapterD.UniqueFactor.actionHom H A hn
  let ρ := ChapterD.UniqueFactor.imageRepresentation H A hn
  let I := (⊤ : Submodule (ZMod 2) (Additive A)).map e
  have heq (h : H) (v : Additive A) :
      reducedRepresentation H h (e v) = e (ρ (f.rangeRestrict h) v) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    rfl
  have hirr : IsIrrPlus (reducedRepresentation H) (B.subgroupOf H) I :=
    hi.map_embedding (reducedRepresentation H) ρ f.rangeRestrict e he heq (B.subgroupOf H) ⊤
  have ht : (T : Subgroup G).subgroupOf H ≤ subspaceStabilizer (reducedRepresentation H) I := by
    apply le_subspaceStabilizer
    rintro t ht _ ⟨v,hv,rfl⟩
    exact ⟨ρ (f.rangeRestrict t) v,Submodule.mem_top,(heq t v).symm⟩
  have hinv : IsIrrPlusWith (reducedRepresentation H) (B.subgroupOf H)
      ((T : Subgroup G).subgroupOf H) I := by
    refine ⟨(comap_mono hTK).trans (le_normalizer_comap H.subtype),hirr.choose,hirr,?_⟩
    apply le_antisymm
    · rw [Representation.BinaryOffender.Homogeneous.orbitSpan_eq_self _ ht]
      apply iSup_le
      intro J
      apply iSup_le
      intro hJ
      exact hJ.1
    · exact Representation.BinaryOffender.Homogeneous.quotientImage_le_homogeneousPart _ hirr.choose
  refine ⟨⟨I,hinv,?_⟩⟩
  ext a
  constructor
  · rintro ⟨_,⟨_,⟨v,_,rfl⟩,rfl⟩,rfl⟩
    exact v.toMul.property
  · intro ha
    exact ⟨_,⟨_,⟨Additive.ofMul ⟨a,ha⟩,Submodule.mem_top,rfl⟩,rfl⟩,rfl⟩

theorem maximal_moved_chosen_source_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G))
    (hm : P.K ∈ Chapter1.LStar G (T : Subgroup G)) :
    Nonempty (ChosenModule T P.K ⁅P.Z,P.K⁆) := by
  let := P.moved_elementary_source
  have hi := P.maximal_moved_irrPlus_source_at structural modules hr hw hm
  have hk : P.K.subgroupOf P.H = pResidual 2 P.H :=
    comap_map_eq_self_of_injective P.H.subtype_injective _
  rw [← hk] at hi
  exact chosen_of_irrPlus_image_at P.residual_sup_sylow P.moved_le_hstar
    P.sylow_normalizes_residual P.moved_module_normalized P.moved_reduced hi

theorem maximal_moved_model_source_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G))
    (hm : P.K ∈ Chapter1.LStar G (T : Subgroup G)) :
    Chapter6.Source.IsConjugationModel P.K ⁅P.Z,P.K⁆ Chapter6.Source.a5Module := by
  obtain ⟨E⟩ := P.maximal_moved_chosen_source_at structural modules hr hw hm
  obtain ⟨⟨q⟩, hall⟩ := P.maximal_residual_five_at structural modules hr hw hm
  let := E.actionCentralizer_normal
  obtain ⟨a⟩ := hall _ E
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let b := E.coreToFaithfulEquiv q.isSimpleGroup
  apply E.a5_model_of_central_quotient (b.trans a.groupEquiv) a.linearEquiv
  intro k v
  exact a.intertwines (QuotientGroup.mk' ((centralizer ((⁅P.Z,P.K⁆ : Subgroup G) : Set G)).subgroupOf P.K) k) v

theorem componentAnalysis_of_maximal_source_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G))
    (hm : P.K ∈ Chapter1.LStar G (T : Subgroup G)) : Nonempty P.ComponentAnalysis := by
  obtain ⟨q,f,hf⟩ := P.maximal_moved_model_source_at structural modules hr hw hm
  let c := BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
  let d := f.trans c.symm.toAddEquiv.toMultiplicative
  have hnorm : P.K ≤ normalizer (⁅P.Z,P.K⁆ : Subgroup G) :=
    normalizer_commutator_ge_right _ _
  have hle : ⁅P.Z,P.K⁆ ≤ P.K := by
    obtain ⟨E⟩ := P.maximal_moved_chosen_source_at structural modules hr hw hm
    exact E.le_component
  let sec : BinaryConjugationSection P.K ⁅P.Z,P.K⁆ ⊥ (P.residualNaturalAction q) := {
    section_le := hle
    kernel_le := bot_le
    normalized := hnorm
    coordinates := d.toMonoidHom
    onto := d.surjective
    kernel_eq := by rw [d.toMonoidHom.ker_eq_bot_iff.mpr d.injective,bot_subgroupOf]
    equivariant k v := by
      apply c.injective
      change c (c.symm (f ⟨(k:G)*(v:G)*(k:G)⁻¹,_⟩).toAdd) =
        c (BinaryPermutation.alternatingCoreRepresentation (Fin 5)
          (q (QuotientGroup.mk' (pCore 2 P.K) k)) (c.symm (f v).toAdd))
      rw [c.apply_symm_apply]
      have hc := BinaryPermutation.coreEquivNatural_equivariant (Fin 5) (by decide)
        (q (QuotientGroup.mk' (pCore 2 P.K) k)).val (c.symm (f v).toAdd)
      change c (BinaryPermutation.alternatingCoreRepresentation (Fin 5)
        (q (QuotientGroup.mk' (pCore 2 P.K) k)) (c.symm (f v).toAdd)) =
        Chapter6.Source.a5Module (q (QuotientGroup.mk' (pCore 2 P.K) k))
          (c (c.symm (f v).toAdd)) at hc
      rw [hc,c.apply_symm_apply]
      change f ⟨(k:G)*(v:G)*(k:G)⁻¹,_⟩ = Multiplicative.ofAdd
        (Chapter6.Source.a5Module (q (QuotientGroup.mk' (pCore 2 P.K) k)) (f v).toAdd)
      apply f.symm.injective
      rw [f.symm_apply_apply]
      apply Subtype.ext
      exact (hf k v).symm }
  exact ⟨⟨P.pointCentralizer_normalizes_of_maximal hm,q,
    P.maximal_thompson_source_at structural modules hr hw hm,sec⟩⟩

theorem componentAnalysis_of_proper_models_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (localAnalysis_at : ∀ (Y W : Subgroup G) (SY : Setup T Y W), Nonempty SY.LocalAnalysis)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G))
    (proper : ∀ Y : Subgroup G, Y ∈ Chapter1.LStar G (T : Subgroup G) → P.K < Y →
      Nonempty ((P.K ⧸ pCore 2 P.K) ≃* alternatingGroup (Fin 5)) ∧
        Nonempty (CentralQuotient Y ≃* alternatingGroup (Fin 7))) :
    Nonempty P.ComponentAnalysis := by
  by_cases hm : P.K ∈ Chapter1.LStar G (T : Subgroup G)
  · exact P.componentAnalysis_of_maximal_source_at structural modules hr hw hm
  obtain ⟨F,hF⟩ := P.overcomponents_of_original_at structural modules hr hw
  have hKY : P.K ≤ F.Y := F.residual_le.trans F.le_maximal
  have hne : P.K ≠ F.Y := fun he => hm (he.symm ▸ F.maximal)
  obtain ⟨⟨q⟩,_⟩ := proper F.Y F.maximal (lt_of_le_of_ne hKY hne)
  obtain ⟨R⟩ := P.residualAnalysis_of_models_at structural modules hr hw q
    (fun Y hY hKY => (proper Y hY hKY).2) (fun h => (hm h).elim)
  exact P.componentAnalysis_of_residual_at structural escape localAnalysis_at R

end TerminalPoint

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

