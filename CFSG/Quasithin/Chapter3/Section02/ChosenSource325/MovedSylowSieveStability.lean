module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowOffenderExtraction
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.EndNodeRank
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.QuasisimpleContract
public import Theory.Representation.BinaryOffender.SectionOffender
public import Theory.Representation.BinaryOffender.EquivariantBest
public import Theory.Representation.BinaryOffender.MovedSpaceTransport
public import Theory.Representation.BinaryOffender.GeneratedCore
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceB513.SplitModels

/-!
# Cubic stabilization in the exceptional B.4.2 rows

If a cubic actor moves a constituent, its index-two stabilizer is an offender
on that constituent. In a ratio-one module it is a best offender. The literal
swapped-pair codimension then exceeds twice the actor rank when all best
offenders have rank less than the constituent dimension minus two. The
projective-plane triple-six row and exterior-five row satisfy this bound.

The actual chosen-seed application is `SeedAlternativesMovedSylowStability`.
Source: Aschbacher--Smith D.3.5(3--5), combined manuscript of 1 March 2004,
printed pp.195--196. The triple-six clause uses projective lines, hence
F₄-subspaces of dimension two, as required by B.4.2(8) and K.1.3.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
open ChapterB.QuasisimpleSource
variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W] (ρ : Representation (ZMod 2) H W)

/-- A ratio-one constituent with small best offenders is fixed by every
cubic actor of ratio at most two that is faithful on the constituent. -/
theorem cubic_stabilizes_of_small_best_offenders
    (I : Submodule (ZMod 2) W) (A : Subgroup H) (hA : IsElementaryTwo A)
    (hc : IsCubic ρ A) (hind : sSupIndep (subspaceOrbit ρ A I))
    (hdim : 2 < Module.finrank (ZMod 2) I)
    (hbound : fixedCodim ρ A ≤ 2 * rank A) (hk : subspaceKernel ρ I A = ⊥)
    (hq : quadraticRatio (subspaceImageRepresentation ρ I) = 1)
    (hsmall : ∀ B, IsBestOffender (subspaceImageRepresentation ρ I) B →
      rank B + 2 < Module.finrank (ZMod 2) I) :
    A ≤ subspaceStabilizer ρ I := by
  intro a ha
  by_contra hn
  have hm : I.map (ρ a) ≠ I := fun he => hn ((subspace_map_eq_iff ρ I a).mp he)
  let : IsElementaryAbelian 2 A := hA.2
  let B := A ⊓ subspaceStabilizer ρ I
  have hB := cubic_stabilizer_ne_bot ρ I A hA hc hind hdim hbound
  obtain ⟨b,hb,hb1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hB
  have hmove : ∃ v ∈ I, ρ b v ≠ v := by
    by_contra! hfix
    exact hb1 (mem_bot.mp (hk.le ⟨hb.1,hfix⟩))
  have ha2 : a*a = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha
  have htwo : ∀ c ∈ A, I.map (ρ c) = I ∨ I.map (ρ c) = I.map (ρ a) :=
    fun c hcA => cubic_orbit_eq_self_or_moving_of_noncentral_stabilizer
      ρ I A hc hind ha ha2 hm hb.1 hb.2 hmove hcA
  have hi : I ∈ subspaceOrbit ρ A I := by
    refine ⟨1,?_⟩
    simp only [Subgroup.coe_one,map_one,Module.End.one_eq_id,Submodule.map_id]
  have hd := hind.pairwiseDisjoint hi ⟨⟨a,ha⟩,rfl⟩ hm.symm
  have hkB : subspaceKernel ρ I B = ⊥ := by
    apply bot_unique
    intro g hg
    exact hk.le ⟨hg.1.1,hg.2⟩
  have hI : I ≠ ⊥ := Submodule.nontrivial_iff_ne_bot.mp
    (Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank (ZMod 2) I))
  have hoff := pair_stabilizer_isOffender ρ I hI A hA ha ha2 hd hm htwo hB hkB hbound
  obtain ⟨hbest,hcodim⟩ := hoff.best_and_codim_eq_of_quadraticRatio_eq_one _ hq
  have hs := hsmall _ hbest
  have hr := pair_stabilizer_rank ρ I A hA ha ha2 hm htwo
  have hrB := rank_subspaceKernel_add_image ρ I B inf_le_right
    ((IsElementaryAbelian.isPGroup 2 A).to_le (show B ≤ A from inf_le_left))
  rw [hkB,Representation.BinaryOffender.rank_bot,zero_add] at hrB
  have hlower := swapped_pair_codim_lower_bound ρ I A ha ha2 hd
  change rank A = rank B + 1 at hr
  change Module.finrank (ZMod 2) I + fixedCodim (subspaceImageRepresentation ρ I)
    (restrictedSubgroup ρ I B) ≤ fixedCodim ρ A at hlower
  change fixedCodim (subspaceImageRepresentation ρ I) (restrictedSubgroup ρ I B) =
    rank (restrictedSubgroup ρ I B) at hcodim
  change rank (restrictedSubgroup ρ I B) + 2 < Module.finrank (ZMod 2) I at hs
  rw [hrB] at hcodim hs
  omega

omit [Finite H] [FiniteDimensional (ZMod 2) W] in
/-- The actual ten-dimensional exterior-five offender has rank four. -/
theorem exteriorFive_best_rank_small (K : Subgroup H)
    (hg : offenderSubgroup ρ = K)
    (e : K ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
    (hd : Module.finrank (ZMod 2) W = 10)
    (hoff : ∀ B, IsBestOffender ρ B → IsEndNodeRadical ((B.subgroupOf K).map e.toMonoidHom)) :
    ∀ B, IsBestOffender ρ B → rank B + 2 < Module.finrank (ZMod 2) W := by
  intro B hB
  have hr := (hoff B hB).rank
  have hBK : B ≤ K := hg ▸ hB.le_offenderSubgroup ρ
  rw [rank_map_injective e.toMonoidHom e.injective,rank_subgroupOf hBK] at hr
  omega

/-- The F₄-plane fixed pointwise by a triple-six offender bounds its rank by two. -/
theorem tripleSix_best_rank_small (K : Subgroup H)
    (a : ChapterB.SourceInduction.ProjectiveLine.TripleSixAction ρ K)
    (hq : quadraticRatio ρ = 1) :
    ∀ B, IsBestOffender ρ B → rank B + 2 < Module.finrank (ZMod 2) W := by
  intro B hB
  obtain ⟨P,hP,hBker⟩ := a.offenders B hB
  have hfix := le_fixedSpace_subspaceKernel ρ
    ((P.restrictScalars (ZMod 2)).comap a.coordinates.toLinearMap) ⊤
  rw [←hBker] at hfix
  have hfour : Module.finrank (ZMod 2)
      ((P.restrictScalars (ZMod 2)).comap a.coordinates.toLinearMap) = 4 := by
    have he := (a.coordinates.ofSubmodule' (P.restrictScalars (ZMod 2))).finrank_eq
    have hr := ((P.restrictScalarsEquiv (ZMod 2)).restrictScalars (ZMod 2)).finrank_eq
    rw [he,hr,←Module.finrank_mul_finrank (ZMod 2) BinaryField.four.Carrier P,hP]
    have hF : Module.finrank (ZMod 2) BinaryField.four.Carrier = 2 := by
      have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := BinaryField.four.Carrier)
      rw [Nat.card_zmod,BinaryField.four.card_eq] at hc
      exact Nat.pow_right_injective (by decide : 1 < 2) hc.symm
    simp [hF]
  have hfixed := Submodule.finrank_mono hfix
  have hdim := fixedCodim_add_finrank ρ B
  have he := ((hB.isOffender ρ).best_and_codim_eq_of_quadraticRatio_eq_one _ hq).2
  have hd := a.dimension
  omega

/-- The stabilization criterion survives literal actor and vector coordinates. -/
theorem cubic_stabilizes_of_small_best_offenders_equiv
    (I : Submodule (ZMod 2) W) (A : Subgroup H) (hA : IsElementaryTwo A)
    (hc : IsCubic ρ A) (hind : sSupIndep (subspaceOrbit ρ A I))
    (hdim : 2 < Module.finrank (ZMod 2) I)
    (hbound : fixedCodim ρ A ≤ 2 * rank A) (hk : subspaceKernel ρ I A = ⊥)
    {K U : Type*} [Group K] [AddCommGroup U] [Module (ZMod 2) U]
    (σ : Representation (ZMod 2) K U)
    (e : ActionEquiv (subspaceImageRepresentation ρ I) σ)
    (hq : quadraticRatio σ = 1)
    (hsmall : ∀ B, IsBestOffender σ B → rank B + 2 < Module.finrank (ZMod 2) U) :
    A ≤ subspaceStabilizer ρ I := by
  apply cubic_stabilizes_of_small_best_offenders ρ I A hA hc hind hdim hbound hk
    (e.quadraticRatio_eq.trans hq)
  intro B hB
  have hh := hsmall _ (hB.map_equivariant _ _ e.groupEquiv e.linearEquiv e.intertwines)
  rw [rank_map_injective _ e.groupEquiv.injective,←e.linearEquiv.finrank_eq] at hh
  exact hh

/-- On two faithful disjoint ratio-one constituents a common actor with
codimension at most twice its rank is a best offender on both constituents. -/
theorem common_actor_best_on_pair
    (I J : Submodule (ZMod 2) W) {A : Subgroup H} (hA : IsElementaryTwo A)
    (hI : A ≤ subspaceStabilizer ρ I) (hJ : A ≤ subspaceStabilizer ρ J)
    (hd : Disjoint I J) (hkI : subspaceKernel ρ I A = ⊥)
    (hkJ : subspaceKernel ρ J A = ⊥) (hb : fixedCodim ρ A ≤ 2 * rank A)
    (hqI : quadraticRatio (subspaceImageRepresentation ρ I) = 1)
    (hqJ : quadraticRatio (subspaceImageRepresentation ρ J) = 1) :
    IsBestOffender (subspaceImageRepresentation ρ I) (restrictedSubgroup ρ I A) ∧
    IsBestOffender (subspaceImageRepresentation ρ J) (restrictedSubgroup ρ J A) ∧
    fixedCodim (subspaceImageRepresentation ρ I) (restrictedSubgroup ρ I A) = rank A ∧
    fixedCodim (subspaceImageRepresentation ρ J) (restrictedSubgroup ρ J A) = rank A := by
  let : IsElementaryAbelian 2 A := hA.2
  have hfaith (U : Submodule (ZMod 2) W) (hk : subspaceKernel ρ U A = ⊥) :
      ¬ U ≤ fixedSpace ρ A := by
    intro hf
    apply hA.1
    apply bot_unique
    intro a ha
    exact hk.le ⟨ha,fun v hv => hf hv ⟨a,ha⟩⟩
  have hIe := hA.restrictedSubgroup ρ I hI (hfaith I hkI)
  have hJe := hA.restrictedSubgroup ρ J hJ (hfaith J hkJ)
  have hrI := rank_subspaceKernel_add_image ρ I A hI (IsElementaryAbelian.isPGroup 2 A)
  have hrJ := rank_subspaceKernel_add_image ρ J A hJ (IsElementaryAbelian.isPGroup 2 A)
  rw [hkI,Representation.BinaryOffender.rank_bot,zero_add] at hrI
  rw [hkJ,Representation.BinaryOffender.rank_bot,zero_add] at hrJ
  have hlow (U : Submodule (ZMod 2) W)
      (he : IsElementaryTwo (restrictedSubgroup ρ U A))
      (hq : quadraticRatio (subspaceImageRepresentation ρ U) = 1) :
      rank (restrictedSubgroup ρ U A) ≤
        fixedCodim (subspaceImageRepresentation ρ U) (restrictedSubgroup ρ U A) := by
    by_contra! hh
    have hstrong : IsStrongFFModule (subspaceImageRepresentation ρ U) := ⟨_,he,hh⟩
    have hs := (isStrongFFModule_iff_quadraticRatio_lt_one _).mp hstrong
    rw [hq] at hs
    exact lt_irrefl _ hs
  have hli := hlow I hIe hqI
  have hlj := hlow J hJe hqJ
  rw [hrI] at hli
  rw [hrJ] at hlj
  have hsum := common_actor_fixedCodim_pair_le ρ I J A hI hJ hd
  have hei : fixedCodim (subspaceImageRepresentation ρ I) (restrictedSubgroup ρ I A) = rank A := by omega
  have hej : fixedCodim (subspaceImageRepresentation ρ J) (restrictedSubgroup ρ J A) = rank A := by omega
  refine ⟨?_,?_,hei,hej⟩
  · exact (IsOffender.best_and_codim_eq_of_quadraticRatio_eq_one _
      ⟨hIe,by rw [hei,hrI]⟩ hqI).1
  · exact (IsOffender.best_and_codim_eq_of_quadraticRatio_eq_one _
      ⟨hJe,by rw [hej,hrJ]⟩ hqJ).1

/-- On a nontrivial independent orbit, a common stable faithful cubic-budget
actor is best on every constituent of quadratic ratio one. -/
theorem common_actor_best_on_orbit
    (I : Submodule (ZMod 2) W) {A : Subgroup H} (hA : IsElementaryTwo A)
    (hind : sSupIndep (subspaceOrbit ρ ⊤ I))
    (hs : ∀ J ∈ subspaceOrbit ρ ⊤ I, A ≤ subspaceStabilizer ρ J)
    (hk : ∀ J ∈ subspaceOrbit ρ ⊤ I, subspaceKernel ρ J A = ⊥)
    (hq : ∀ J ∈ subspaceOrbit ρ ⊤ I, quadraticRatio (subspaceImageRepresentation ρ J) = 1)
    (hb : fixedCodim ρ A ≤ 2 * rank A)
    (hm : ∃ t : H, I.map (ρ t) ≠ I)
    (J : Submodule (ZMod 2) W) (hJ : J ∈ subspaceOrbit ρ ⊤ I) :
    IsBestOffender (subspaceImageRepresentation ρ J) (restrictedSubgroup ρ J A) ∧
      fixedCodim (subspaceImageRepresentation ρ J) (restrictedSubgroup ρ J A) = rank A := by
  obtain ⟨t,ht⟩ := hm
  have hi : I ∈ subspaceOrbit ρ ⊤ I := by
    refine ⟨1,?_⟩
    simp only [Subgroup.coe_one,map_one,Module.End.one_eq_id,Submodule.map_id]
  have htmem : I.map (ρ t) ∈ subspaceOrbit ρ ⊤ I := ⟨⟨t,mem_top _⟩,rfl⟩
  obtain ⟨K,hK,hJK⟩ : ∃ K ∈ subspaceOrbit ρ ⊤ I, J ≠ K := by
    by_cases h : J = I
    · exact ⟨I.map (ρ t),htmem,by rwa [h,ne_comm]⟩
    · exact ⟨I,hi,h⟩
  have hd := hind.pairwiseDisjoint hJ hK hJK
  have hp := common_actor_best_on_pair ρ J K hA (hs J hJ) (hs K hK)
    hd (hk J hJ) (hk K hK) hb (hq J hJ) (hq K hK)
  exact ⟨hp.1,hp.2.2.1⟩

omit [Finite H] in
/-- The same actor's fixed codimensions add exactly on an invariant direct sum. -/
theorem common_actor_fixedCodim_sup
    (I J : Submodule (ZMod 2) W) (A : Subgroup H)
    (hI : A ≤ subspaceStabilizer ρ I) (hJ : A ≤ subspaceStabilizer ρ J)
    (hd : Disjoint I J) :
    fixedCodim (subspaceImageRepresentation ρ (I ⊔ J)) (restrictedSubgroup ρ (I ⊔ J) A) =
      fixedCodim (subspaceImageRepresentation ρ I) (restrictedSubgroup ρ I A) +
      fixedCodim (subspaceImageRepresentation ρ J) (restrictedSubgroup ρ J A) := by
  have hi := fixedCodim_add_finrank (subspaceImageRepresentation ρ I) (restrictedSubgroup ρ I A)
  have hj := fixedCodim_add_finrank (subspaceImageRepresentation ρ J) (restrictedSubgroup ρ J A)
  have hs := fixedCodim_add_finrank (subspaceImageRepresentation ρ (I ⊔ J))
    (restrictedSubgroup ρ (I ⊔ J) A)
  rw [(restrictedFixedSpaceEquiv ρ I A hI).finrank_eq] at hi
  rw [(restrictedFixedSpaceEquiv ρ J A hJ).finrank_eq] at hj
  rw [(restrictedFixedSpaceEquiv ρ (I ⊔ J) A (subspaceStabilizer_sup ρ hI hJ)).finrank_eq,
    fixedSpace_inf_disjoint_sup ρ I J A hI hJ hd] at hs
  have hdim := I.finrank_sup_add_finrank_inf_eq J
  rw [hd.eq_bot,finrank_bot,add_zero] at hdim
  have hfix := (I ⊓ fixedSpace ρ A).finrank_sup_add_finrank_inf_eq (J ⊓ fixedSpace ρ A)
  rw [(hd.mono inf_le_left inf_le_left).eq_bot,finrank_bot,add_zero] at hfix
  omega

/-- Three independent faithful constituents already exceed a two-rank budget
when the common actor costs at least its rank on each constituent. -/
theorem no_three_constituents_of_common_budget
    (I J K : Submodule (ZMod 2) W) {A : Subgroup H} (hA : IsElementaryTwo A)
    (hI : A ≤ subspaceStabilizer ρ I) (hJ : A ≤ subspaceStabilizer ρ J)
    (hK : A ≤ subspaceStabilizer ρ K) (hd : Disjoint I J) (hdk : Disjoint (I ⊔ J) K)
    (hb : fixedCodim ρ A ≤ 2 * rank A)
    (hi : rank A ≤ fixedCodim (subspaceImageRepresentation ρ I) (restrictedSubgroup ρ I A))
    (hj : rank A ≤ fixedCodim (subspaceImageRepresentation ρ J) (restrictedSubgroup ρ J A))
    (hk : rank A ≤ fixedCodim (subspaceImageRepresentation ρ K) (restrictedSubgroup ρ K A)) :
    False := by
  have hs := common_actor_fixedCodim_pair_le ρ (I ⊔ J) K A
    (subspaceStabilizer_sup ρ hI hJ) hK hdk
  rw [common_actor_fixedCodim_sup ρ I J A hI hJ hd] at hs
  have hp := hA.rank_pos
  omega

/-- A stable common actor paying its rank on every independent constituent
forces any nontrivial homogeneous orbit to have exactly two actual members. -/
theorem two_conjugates_of_common_budget
    (I : Submodule (ZMod 2) W) {A : Subgroup H} (hA : IsElementaryTwo A)
    (hind : sSupIndep (subspaceOrbit ρ ⊤ I))
    (hs : ∀ J ∈ subspaceOrbit ρ ⊤ I, A ≤ subspaceStabilizer ρ J)
    (hb : fixedCodim ρ A ≤ 2 * rank A)
    (hlow : ∀ J ∈ subspaceOrbit ρ ⊤ I, rank A ≤ fixedCodim
      (subspaceImageRepresentation ρ J) (restrictedSubgroup ρ J A))
    {t : H} (ht : I.map (ρ t) ≠ I) :
    ∀ s : H, I.map (ρ s) = I ∨ I.map (ρ s) = I.map (ρ t) := by
  intro s
  by_contra! hn
  have hmem (g : H) : I.map (ρ g) ∈ subspaceOrbit ρ ⊤ I := ⟨⟨g,mem_top _⟩,rfl⟩
  have hi : I ∈ subspaceOrbit ρ ⊤ I := by
    simpa only [map_one,Module.End.one_eq_id,Submodule.map_id] using hmem 1
  have hd := hind.pairwiseDisjoint hi (hmem t) ht.symm
  have hdk : Disjoint (I ⊔ I.map (ρ t)) (I.map (ρ s)) := by
    have hpair : ({I,I.map (ρ t)} : Set (Submodule (ZMod 2) W)) ⊆ subspaceOrbit ρ ⊤ I := by
      intro J hJ
      rcases Set.mem_insert_iff.mp hJ with rfl | hJ
      · exact hi
      · rw [Set.mem_singleton_iff] at hJ
        exact hJ ▸ hmem t
    have hnmem : I.map (ρ s) ∉ ({I,I.map (ρ t)} : Set (Submodule (ZMod 2) W)) := by
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
      exact not_or.mpr hn
    have hh := hind.disjoint_sSup (hmem s) hpair hnmem
    simpa only [sSup_pair] using hh.symm
  exact no_three_constituents_of_common_budget ρ I (I.map (ρ t)) (I.map (ρ s)) hA
    (hs I hi) (hs _ (hmem t)) (hs _ (hmem s)) hd hdk hb
    (hlow I hi) (hlow _ (hmem t)) (hlow _ (hmem s))

/-- Best offending, its rank, and its generated-core containment survive the
literal marked faithful-image equivalence together. -/
theorem restricted_best_on_marked_image
    (I : Submodule (ZMod 2) W) {A : Subgroup H} (hA : IsElementaryTwo A)
    (hs : A ≤ subspaceStabilizer ρ I) (hk : subspaceKernel ρ I A = ⊥)
    (hbest : IsBestOffender (subspaceImageRepresentation ρ I) (restrictedSubgroup ρ I A))
    {K U : Type*} [Group K] [AddCommGroup U] [Module (ZMod 2) U]
    (σ : Representation (ZMod 2) K U) (e : ActionEquiv (subspaceImageRepresentation ρ I) σ)
    (L : Subgroup K) (hL : offenderSubgroup σ = L) :
    let B := (restrictedSubgroup ρ I A).map e.groupEquiv.toMonoidHom
    IsBestOffender σ B ∧ B ≤ L ∧ rank B = rank A := by
  let : IsElementaryAbelian 2 A := hA.2
  have hb := hbest.map_equivariant _ _ e.groupEquiv e.linearEquiv e.intertwines
  refine ⟨hb,hL ▸ hb.le_offenderSubgroup σ,?_⟩
  rw [rank_map_injective _ e.groupEquiv.injective]
  have hr := rank_subspaceKernel_add_image ρ I A hs (IsElementaryAbelian.isPGroup 2 A)
  simpa only [hk,Representation.BinaryOffender.rank_bot,zero_add] using hr

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
