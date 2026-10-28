module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Orbit
public import CFSG.Quasithin.ChapterE.GenerationKnownSimple

/-!
# E-generation below the source omega-center threshold

An E-member with quotient rank below s(G,V) has a residual centralizing
Ω₁(Z(T)): intersect each of its conjugates of V with its two-core and apply
E.3.6. E-generation then puts H in the join of C_H(Z) and N_H(W₀).
In the source outside-local situation, both subgroups lie in H ∩ M.
This gives E.3.20 directly, without assuming a numerical parameter bound.

Source: Aschbacher--Smith, E.3.20, printed p.235, used in 11.3.4 and
11.3.6, printed pp.771--772 (combined manuscript, 1 March 2004).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
open ChapterE
variable {G : Type*} [Group G] [Finite G]

private theorem member_residual_centralizes_omega {V R Z : Subgroup G}
    [IsElementaryAbelian 2 V] {i : ℕ} (hs : (i : ℕ∞) < globalS V)
    (hZ : IsPGroup 2 Z) (hZR : Z ≤ centralizer (R : Set G))
    {X : Type*} [Group X] [Finite X] {P A K : Subgroup X}
    (hK : IsEMemberAt i P A K) (f : X →* G) (hf : Function.Injective f)
    (g : G) (hAg : A.map f = V.map (MulAut.conj g).toMonoidHom)
    (hPR : P.map f ≤ R) :
    (pResidual 2 K).map (f.comp K.subtype) ≤ centralizer (Z : Set G) := by
  let B := A.subgroupOf K
  let e := f.comp K.subtype
  let := hK.1.1
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hK.1.2.2.1
  have he : Function.Injective e := hf.comp K.subtype_injective
  have hB : B.map e = V.map (MulAut.conj g).toMonoidHom := by
    rw [show e = f.comp K.subtype from rfl, ← map_map,
      map_subgroupOf_eq_of_le hK.1.2.2.1]
    exact hAg
  have hcore : (pCore 2 K).map e ≤ R := by
    obtain ⟨U,hU⟩ := hK.1.2.2.2.2.1
    have hcu := map_mono (f := K.subtype) (pCore_isPGroup.le_sylow_of_normal U)
    rw [hU,subgroupOf_map_subtype] at hcu
    rw [show e = f.comp K.subtype from rfl, ← map_map]
    exact (map_mono (hcu.trans inf_le_left)).trans hPR
  have hi : subgroupCorank B (B ⊓ pCore 2 K) ≤ i :=
    SourceContainment.core_corank_le B (ValuesEvenClassical.Sp4Lower.member_core_rank_le hK)
  have hconj (x : K) : B.map (e.comp (MulAut.conj x).toMonoidHom) ≤
      centralizer (Z : Set G) := by
    let e' := e.comp (MulAut.conj x).toMonoidHom
    let C := (B ⊓ pCore 2 K).map e'
    let W := V.map (MulAut.conj (e x * g)).toMonoidHom
    let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
    have hinj : Function.Injective e' := he.comp (MulAut.conj x).injective
    have hW : B.map e' = W := by
      have he' : e' = (MulAut.conj (e x)).toMonoidHom.comp e := by ext a; simp [e']
      change B.map e' = _
      rw [he',← map_map,hB,map_map]
      congr 1
      ext a
      simp [mul_assoc]
    have hCR : C ≤ R := by
      rintro c ⟨a,ha,rfl⟩
      exact hcore (mem_map_of_mem e ((inferInstance : (pCore 2 K).Normal).conj_mem a ha.2 x))
    have hc : (subgroupCorank W C : ℕ∞) < globalS W := by
      have heq : subgroupCorank W C = subgroupCorank B (B ⊓ pCore 2 K) := by
        rw [← hW]
        exact congrArg (Nat.log 2) (relIndex_map_map_of_injective _ _ hinj)
      rw [heq,show globalS W = globalS V from globalS_map_equiv _ _]
      exact lt_of_le_of_lt (by exact_mod_cast hi) hs
    have hCW : C ≤ W := hW ▸ map_mono inf_le_left
    have hcentral := centralizer_inf_eq_of_corank_lt_globalS hCW hc hZ
    apply le_centralizer_iff.mpr
    rw [hW]
    exact (le_inf le_rfl (hZR.trans (centralizer_le hCR))).trans
      (hcentral.le.trans inf_le_right)
  apply (map_mono hK.1.residual_le_normalClosure).trans
  apply map_le_iff_le_comap.mpr
  change Subgroup.closure (Group.conjugatesOfSet (B : Set K)) ≤ _
  apply (closure_le _).mpr
  intro x hx
  obtain ⟨a,ha,hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
  obtain ⟨k,rfl⟩ := isConj_iff.mp hax
  exact hconj k (mem_map_of_mem _ ha)

variable {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H : Subgroup G}

private theorem omega_centralizer_le (h : Hypothesis1131At D S U₁ H) :
    H ⊓ centralizer (sourceZ T : Set G) ≤ normalizer (L : Set G) := by
  apply Chapter3.HStar.proper_overgroup_le T h.outside
  · apply le_inf h.outside.1.1.2
    apply le_centralizer_iff.mp
    intro z hz
    exact ((mem_omegaCenterIn_iff _ _).mp hz).2.1
  · apply lt_of_le_of_ne inf_le_left
    intro he
    apply h.moves_omega_center
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mp
    have hc : H ≤ centralizer (sourceZ T : Set G) := he ▸ inf_le_right
    simpa only [sourceZ,omegaCenterIn_eq_omegaOneAmbient] using hc

private theorem weak_normalizer_le (h : Hypothesis1131At D S U₁ H)
    {W : Subgroup G} (hw : ¬ indexedWeakClosure W (T : Subgroup G) 0 ≤ H.pCoreIn 2) :
    H ⊓ normalizer (indexedWeakClosure W (T : Subgroup G) 0 : Set G) ≤
      normalizer (L : Set G) := by
  apply Chapter3.HStar.proper_overgroup_le T h.outside
  · exact le_inf h.outside.1.1.2
      ((T : Subgroup G).le_normalizer.trans (normalizer_le_weakClosure_normalizer _ _ _))
  · apply lt_of_le_of_ne inf_le_left
    intro he
    apply hw
    apply le_pCoreIn_of_normalizes
      (T.isPGroup'.to_le (indexedWeakClosure_le W (T : Subgroup G) 0))
      ((indexedWeakClosure_le _ _ _).trans h.outside.1.1.2)
    exact he ▸ inf_le_right

/-- The E.3.20 obstruction at any attained generation bound; no minimum label
is substituted for the actual E-generation hypothesis. -/
theorem globalS_le_of_generation_for (h : Hypothesis1131At D S U₁ H)
    (W : Subgroup G) [IsElementaryAbelian 2 W]
    (hw : ¬ indexedWeakClosure W (T : Subgroup G) 0 ≤ H.pCoreIn 2)
    {i : ℕ} (hgen : IsEGeneratedAt i (T.subtype h.outside.1.1.2)) :
    globalS W ≤ (i : ℕ∞) := by
  by_contra hn
  have hs : (i : ℕ∞) < globalS W := lt_of_not_ge hn
  let P := T.subtype h.outside.1.1.2
  let M := normalizer (L : Set G)
  have hTP : (P : Subgroup H).map H.subtype = (T : Subgroup G) := by
    change ((T : Subgroup G).subgroupOf H).map H.subtype = _
    exact map_subgroupOf_eq_of_le h.outside.1.1.2
  let Ω := conjugateCorankFamily W 0
  have hΩ : IsElementaryFamily Ω := by
    constructor
    · rintro A ⟨g,hAV,_⟩
      let : IsElementaryAbelian 2 (W.map (MulAut.conj g).toMonoidHom) := IsElementaryAbelian.map _
      exact IsElementaryAbelian.of_injective (inclusion hAV) (inclusion_injective _)
    · intro g A hA
      exact conjugateCorankFamily_invariant W 0 A hA g
  let ΩH := ChiefOrbit.restrictedFamily H Ω
  have hΩH : IsElementaryFamily ΩH := ChiefOrbit.restrictedFamily_elementary H hΩ
  have hW : (weakClosure (P : Subgroup H) ΩH).map H.subtype =
      indexedWeakClosure W (T : Subgroup G) 0 := by
    change (weakClosure ((T : Subgroup G).subgroupOf H) ΩH).map H.subtype = _
    exact ChiefOrbit.map_weakClosure_restrictedFamily (T : Subgroup G) H h.outside.1.1.2 Ω
  have hN : normalizer (weakClosure (P : Subgroup H) ΩH : Set H) ≤ M.subgroupOf H := by
    apply map_le_iff_le_comap.mp
    apply le_trans (le_inf (map_subtype_le _) (le_normalizer_map H.subtype))
    rw [hW]
    exact weak_normalizer_le h hw
  have hE : eFamilySubgroup i (P : Subgroup H) ΩH ≤ M.subgroupOf H := by
    apply iSup_le
    intro A
    apply sSup_le
    intro K hK
    have hAT : A.val.map H.subtype ≤ (T : Subgroup G) := hTP ▸ map_mono A.property.2
    obtain ⟨g,hAg,_⟩ := (mem_gamma_zero_iff W (T : Subgroup G) (A.val.map H.subtype)).mp
      ⟨A.property.1,hAT⟩
    have hZ : IsPGroup 2 (sourceZ T) := IsElementaryAbelian.isPGroup 2 (omegaCenterIn (T : Subgroup G))
    have hZR : sourceZ T ≤ centralizer (T : Set G) :=
      fun z hz => ((mem_omegaCenterIn_iff _ _).mp hz).2.1
    have hRC := member_residual_centralizes_omega hs hZ hZR hK H.subtype
      H.subtype_injective g hAg hTP.le
    apply hK.1.le_of_residual_le
      (map_le_iff_le_comap.mp (hTP ▸ D.sylow_normalizes_component))
    rintro x ⟨k,hk,rfl⟩
    exact omega_centralizer_le h ⟨k.val.property,
      hRC (mem_map_of_mem (H.subtype.comp K.subtype) hk)⟩
  apply h.outside.1.2
  have htop : (⊤ : Subgroup H) ≤ M.subgroupOf H := by
    rw [← hgen ΩH hΩH]
    exact sup_le hE hN
  intro x hx
  exact htop (show (⟨x,hx⟩ : H) ∈ (⊤ : Subgroup H) from mem_top _)

/-- E.3.20 for the original seed, preserving the original public interface. -/
theorem globalS_le_of_generation (h : Hypothesis1131At D S U₁ H)
    (hw : ¬ indexedWeakClosure V (T : Subgroup G) 0 ≤ H.pCoreIn 2)
    {i : ℕ} (hgen : IsEGeneratedAt i (T.subtype h.outside.1.1.2)) :
    letI := D.elementary
    globalS V ≤ (i : ℕ∞) := by
  let := D.elementary
  exact globalS_le_of_generation_for h V hw hgen

/-- The actual H is SQTK over the full known-simple catalogue. -/
theorem outside_sqtk (h : Hypothesis1131At D S U₁ H) :
    IsSQTK KnownSimple.IsKnownSimple H := by
  have hn : H ≤ normalizer (H.pCoreIn 2 : Set G) := by
    simpa only [pCoreIn,normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype]
      using (pCore 2 H).le_normalizer_map H.subtype
  have hs := S.source.simpleQTKE.twoLocal_sqtk
    (show IsTwoLocal (normalizer (H.pCoreIn 2 : Set G)) from
      ⟨H.pCoreIn 2,h.outside.1.1.1,isPGroup_pCoreIn 2 H,rfl⟩)
  exact ⟨hs.stronglyQuasithin.of_injective (inclusion hn) (inclusion_injective hn),
    hs.isKGroup.of_injective (inclusion hn) (inclusion_injective hn)⟩

/-- E.3.20 with k literally n(H), including attainment of this minimum. -/
theorem globalS_le_parameter_for (h : Hypothesis1131At D S U₁ H)
    (W : Subgroup G) [IsElementaryAbelian 2 W]
    (hw : ¬ indexedWeakClosure W (T : Subgroup G) 0 ≤ H.pCoreIn 2) :
    globalS W ≤ (generationParameter H : ℕ∞) := by
  have hq : H.pCoreIn 2 ≠ ⊥ := h.outside.1.1.1
  let : Nontrivial (H.pCoreIn 2) := (nontrivial_iff_ne_bot _).mpr hq
  obtain ⟨j,hj,hcard⟩ := (isPGroup_pCoreIn 2 H).nontrivial_iff_card.mp inferInstance
  have heven : ¬ Odd (Nat.card H) := by
    intro ho
    apply ho.not_two_dvd_nat
    apply dvd_trans _ (card_dvd_of_le (pCoreIn_le 2 H))
    rw [hcard]
    exact dvd_pow_self 2 (Nat.ne_of_gt hj)
  exact globalS_le_of_generation_for h W hw
    ((source_generation_spec_knownSimple (outside_sqtk h)
      (T.subtype h.outside.1.1.2) heven).2 _)

/-- The original seed version of the attained E.3.20 bound. -/
theorem globalS_le_parameter (h : Hypothesis1131At D S U₁ H)
    (hw : ¬ indexedWeakClosure V (T : Subgroup G) 0 ≤ H.pCoreIn 2) :
    letI := D.elementary
    globalS V ≤ (generationParameter H : ℕ∞) := by
  let := D.elementary
  exact globalS_le_parameter_for h V hw

/-- The lower bound in 11.3.4 for the actual counterexample. -/
theorem counterexample_parameter_lower (h : Hypothesis1131At D S U₁ H)
    (p : Preceding1133 D S U₁ H) (hc : ¬ Proposition1132At D S U₁ H) :
    letI := D.elementary
    globalS V ≤ (generationParameter H : ℕ∞) := by
  apply globalS_le_parameter h
  rw [← weakClosureZero_eq_indexed]
  exact weakClosure_not_le_core_of_counterexample h p hc
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
