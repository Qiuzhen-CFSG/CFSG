module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.SylowStabilization
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.Nonconstrained
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BenderSylowOvergroups

/-!
# Containing-component quotients before distinctness

The prescribed Sylow stabilizes the original pair inside H ∩ M. Hence C.2.6
and the Fitting-normalizer criterion make every constrained normal containing
component's two-core quotient quasisimple, even if the two containing components
coincide. For a strict containment this supplies the full literal C.2.7 input.
In the other Fitting case, module choice removes the odd core of H, making
the containing component quasisimple. Full-Sylow overgroup solvability also
excludes every Bender quotient of a strict containing component.

The final application selects the actual strict factor and proves this dichotomy
without odd-prime rank or distinctness assumptions. It does not discharge the
A.3.12 model exclusions. Those and final half-Sylow assembly remain with
qt-d-10-nona5-half-sylow-unique. ModuleChoiceAt is supplied independently by
qt-d-10-nona5-point-selection; qt-d-10-nona5-point-control retains its final discharge.
Source: Aschbacher--Smith, 10.2.6, pp.748--749, and C.2.6--7, pp.145--147.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {H : Subgroup G} {t : G} {K₁ K₂ : Subgroup H}

/-- Quasisimplicity of the quotient uses Sylow stabilization, not distinctness. -/
theorem ContainingPair.quotient_quasisimple_of_constrained
    (C : ContainingPair D H t K₁ K₂)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {s : G} (hs : s ∈ (T : Subgroup G)) {K : Subgroup G}
    (hK : K ∈ cComponentsIn H) (hKN : (K.subgroupOf H).Normal)
    (hBK : L.map (MulAut.conj s).toMonoidHom ≤ K)
    (hf : generalizedFitting K = pCore 2 K) :
    IsQuasisimple (K ⧸ pCore 2 K) := by
  classical
  by_contra hnq
  have hF := ChapterC.Section02Source.fittingCore_le_of_nonquasisimple_component_setup
    (pushingSetup_of_halfJoin_le D (D.simpleQTKE.twoLocal_sqtk C.maximal.1) C.half_le)
    hK hf ((normal_subgroupOf_iff_le_normalizer hK.1).mp hKN) hnq
  let B := L.map (MulAut.conj s).toMonoidHom
  let B₀ := B.subgroupOf K
  let e : L ≃* B₀ := ((MulAut.conj s).subgroupMap L).trans
    (subgroupOfEquivOfLe hBK).symm
  have htop : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using hK.2.subgroupOf_of_le le_rfl hK.1
  have hB : IsQuasisimple (B₀ ⧸ pCore 2 B₀) := by
    let := D.quasisimple
    exact IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))
  have hFn : twoFittingCore K ≤ normalizer (B₀ : Set K) := by
    rw [←subgroupOf_normalizer_eq hBK]
    intro x hx
    exact C.intersection_normalizes_conjugate_of_sylow hn hs (hF (mem_map_of_mem K.subtype hx))
  exact hnq (quasisimple_quotient_of_fitting_normalizes htop B₀ hB hFn)

/-- The complete C.2.7 input for a strict original factor, before rank bounds. -/
theorem ContainingPair.c27_input_of_strict
    (C : ContainingPair D H t K₁ K₂)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {s : G} (hs : s ∈ (T : Subgroup G)) {K : Subgroup G}
    (hK : K ∈ cComponentsIn H) (hKN : (K.subgroupOf H).Normal)
    (hBK : L.map (MulAut.conj s).toMonoidHom < K)
    (hf : generalizedFitting K = pCore 2 K) :
    RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Input
      KnownSimple.IsKnownSimple H ((localJoin T L).pCoreIn 2) (H ⊓ D.maximalLocal) K := by
  refine ⟨pushingSetup_of_halfJoin_le D (D.simpleQTKE.twoLocal_sqtk C.maximal.1) C.half_le,
    hK,C.quotient_quasisimple_of_constrained hn hs hK hKN hBK.le hf,hf,?_,?_⟩
  · exact fun h => source_strict_conjugate_component_outside D hs hK hBK (h.trans inf_le_right)
  · exact ((join_core_le_stabilizer D).trans (le_sup_right.trans C.half_le)).trans
      ((normal_subgroupOf_iff_le_normalizer hK.1).mp hKN)

/-- Restriction uses the actual prescribed Sylow, before any rank calculation. -/
theorem ContainingPair.local_sylow_in_containing
    (C : ContainingPair D H t K₁ K₂)
    {s : G} (hs : s ∈ (T : Subgroup G)) {K : Subgroup G}
    (hK : K ∈ cComponentsIn H)
    (hBK : L.map (MulAut.conj s).toMonoidHom ≤ K) :
    ∃ S : Sylow 2 K,
      (S : Subgroup K) = ((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf K ∧
      (L.map (MulAut.conj s).toMonoidHom).subgroupOf K ∈ ChapterA.Section03.localCComponents S := by
  let B := L.map (MulAut.conj s).toMonoidHom
  let R := (T : Subgroup G) ⊓ normalizer (L : Set G)
  have hB : B ∈ Chapter1.L G (T : Subgroup G) := by
    have hh := (Chapter1.mem_L_map_iff (MulAut.conj s).toMonoidHom
      (MulAut.conj s).injective).mpr D.maximal.1
    have he : (T : Subgroup G).map (MulAut.conj s).toMonoidHom = T :=
      mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup G).le_normalizer hs)
    rwa [he] at hh
  obtain ⟨S,hS⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    C.sylow hK.1 hK.2.subnormal
  have he : (S : Subgroup K) = R.subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [hS,subgroupOf_map_subtype]
  refine ⟨S,he,?_⟩
  rw [he]
  exact ChapterA.Section03.SourceEmbeddings.local_restrict
    (ChapterA.Section03.localCComponents_antitone inf_le_left hB.1) hBK

/-- No strict containing component has a Bender two-core quotient.
This exclusion is independent of distinctness and of the odd-prime rank bounds. -/
theorem ContainingPair.not_bender_quotient_of_strict
    (C : ContainingPair D H t K₁ K₂)
    {s : G} (hs : s ∈ (T : Subgroup G)) {K : Subgroup G}
    (hK : K ∈ cComponentsIn H)
    (hBK : L.map (MulAut.conj s).toMonoidHom < K) :
    ¬ ClassificationModels.IsBenderModel (K ⧸ pCore 2 K) := by
  intro hm
  obtain ⟨S,_,hl⟩ := C.local_sylow_in_containing hs hK hBK.le
  let B := (L.map (MulAut.conj s).toMonoidHom).subgroupOf K
  let P := B ⊔ (S : Subgroup K)
  have hp : P ≠ ⊤ := by
    intro ht
    have hB : B.IsCComponent := by
      change (B.subgroupOf P).IsCComponent at hl
      rw [ht] at hl
      simpa only [map_subgroupOf_eq_of_le le_top] using
        hl.map_subtype (show (⊤ : Subgroup K).IsSubnormal from .top)
    have htop : (⊤ : Subgroup K).IsCComponent := by
      simpa only [subgroupOf_self] using hK.2.subgroupOf_of_le le_rfl hK.1
    exact hBK.ne (le_antisymm hBK.le
      (subgroupOf_eq_top.mp (hB.eq_of_le htop le_top)))
  let := isSolvable_proper_sylow_overgroup_of_twoCore_quotient
    (ChapterA.Section03.SourceEmbeddings.bender_solvable_proper_sylow_overgroup hm)
    S P le_sup_right hp
  exact hl.not_isSolvable inferInstance

/-- Select the actual strict component and discharge both Fitting branches.
The C.2.7 and quasisimple outputs use the same component and original exchanger. -/
theorem ContainingPair.exists_strict_component_cases
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))) :
    ∃ (s : G) (K : Subgroup G), (s = 1 ∨ s = t) ∧ s ∈ (T : Subgroup G) ∧
      K ∈ cComponentsIn H ∧ (K.subgroupOf H).Normal ∧
      L.map (MulAut.conj s).toMonoidHom < K ∧
      ¬ ClassificationModels.IsBenderModel (K ⧸ pCore 2 K) ∧
      (RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Input
        KnownSimple.IsKnownSimple H ((localJoin T L).pCoreIn 2) (H ⊓ D.maximalLocal) K ∨
        IsQuasisimple K) := by
  have hmap (I : Subgroup H) : (I.map H.subtype).subgroupOf H = I :=
    comap_map_eq_self_of_injective H.subtype_injective I
  have branch (s : G) (hs : s ∈ (T : Subgroup G)) (K : Subgroup G)
      (hK : K ∈ cComponentsIn H) (hKN : (K.subgroupOf H).Normal)
      (hBK : L.map (MulAut.conj s).toMonoidHom < K) :
      RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Input
        KnownSimple.IsKnownSimple H ((localJoin T L).pCoreIn 2) (H ⊓ D.maximalLocal) K ∨
        IsQuasisimple K := by
    by_cases hf : generalizedFitting K = pCore 2 K
    · exact .inl (C.c27_input_of_strict hn hs hK hKN hBK hf)
    · let j := subgroupOfEquivOfLe hK.1
      rcases hK.2.component_or_generalizedFitting_eq_pCore
        (oddCore_eq_bot_of_moduleChoice hchoice hmany D hn hna C.half_le) with hq | he
      · let := hq.2
        exact .inr (IsQuasisimple.of_mulEquiv j)
      · apply (hf ?_).elim
        have hm := congrArg (Subgroup.map j.toMonoidHom) he
        simpa only [map_generalizedFitting_equiv,pCore_map_iso] using hm
  rcases C.strict with hs | hs
  · have hK : K₁.map H.subtype ∈ cComponentsIn H :=
      ⟨map_subtype_le K₁,(hmap K₁).symm ▸ C.first_component⟩
    have hKN : ((K₁.map H.subtype).subgroupOf H).Normal := (hmap K₁).symm ▸ C.first_normal
    have hstrict : L.map (MulAut.conj (1 : G)).toMonoidHom < K₁.map H.subtype := by
      have hh := (map_lt_map_iff_of_injective H.subtype_injective).mpr hs
      rw [map_subgroupOf_eq_of_le C.left_le] at hh
      have he : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
        ext x
        simp
      simpa only [he, Subgroup.map_id] using hh
    exact ⟨1,K₁.map H.subtype,Or.inl rfl,one_mem _,hK,hKN,hstrict,C.not_bender_quotient_of_strict (one_mem _) hK hstrict,
      branch 1 (one_mem _) _ hK hKN hstrict⟩
  · have hK : K₂.map H.subtype ∈ cComponentsIn H :=
      ⟨map_subtype_le K₂,(hmap K₂).symm ▸ C.second_component⟩
    have hKN : ((K₂.map H.subtype).subgroupOf H).Normal := (hmap K₂).symm ▸ C.second_normal
    have hstrict : L.map (MulAut.conj t).toMonoidHom < K₂.map H.subtype := by
      have hh := (map_lt_map_iff_of_injective H.subtype_injective).mpr hs
      rwa [map_subgroupOf_eq_of_le C.right_le] at hh
    exact ⟨t,K₂.map H.subtype,Or.inr rfl,C.t_mem,hK,hKN,hstrict,C.not_bender_quotient_of_strict C.t_mem hK hstrict,
      branch t C.t_mem _ hK hKN hstrict⟩

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
