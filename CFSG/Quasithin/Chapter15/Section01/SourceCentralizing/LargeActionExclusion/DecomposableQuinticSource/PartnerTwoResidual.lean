module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableQuinticSource.Kernel
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableQuinticSource.PartnerTwo
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableQuinticSource.Escape
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoCore
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoSectionSeed

/-!
# The literal order-two partner residual package

The order-two partner branch is kept at the level of the original groups.
The prepared module lies in the actual partner two-core; its partner residual
centralizes the original fixed subgroup, while the second Sylow-central seed
retains the support exchange and the reduced section above the central line.
The unchanged section kernel then has no normal three-complement.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- The literal order-two branch retains its core, residual centralization,
second support seed, and section-kernel obstruction in one source package. -/
theorem PreparedChosenModule.decomposable_five_partner_two_residual_obstruction
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map
          (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized)
        (T : Subgroup G) M (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      Nat.card (localModule T Mc) = 2 →
      let Uc := localModule T Mc
      let E := thompsonFixed T V
      let C := centralizer (E : Set G)
      let H := conjugateSpanBy V C
      let K := (commutatorPreimage Mc H E).subgroupOf Mc
      let E₂ := E ⊓ commutatorPreimage (T : Subgroup G) (T : Subgroup G) Uc
      let H₂ := conjugateSpanBy E₂ Mc
      V ≤ Mc.pCoreIn 2 ∧
        Mc = centralizer (Uc : Set G) ∧
        Mc = C ⊔ (T : Subgroup G) ∧
        (pResidual 2 Mc).map Mc.subtype ≤ C ∧
        normalizer (E : Set G) = Mc ∧
        H = conjugateSpanBy V (centralizer (Uc : Set G)) ∧
        Mc ≤ normalizer (H : Set G) ∧
        commutatorPreimage Mc H E ≤ M ⊓ C ∧
        ∃ hK : K.Normal, letI := hK
          ¬ HasNormalPComplement 3 ((C.subgroupOf Mc).map (QuotientGroup.mk' K)) ∧
        Uc < E₂ ∧ E₂ < E ∧
        (Nat.card E₂ = 4 ∨ Nat.card E₂ = 8) ∧
        ⁅E₂, (T : Subgroup G)⁆ ≤ Uc ∧ E₂ ≤ H₂ ∧
        H₂ ≤ conjugateSpanBy E (centralizer (Uc : Set G)) ∧
        Mc ≤ normalizer (H₂ : Set G) ∧
        IsElementaryAbelian 2 H₂ ∧
        ∃ hUc : (Uc.subgroupOf Mc).Normal, letI := hUc
          IsPReduced 2 ((H₂.subgroupOf Mc).map
            (QuotientGroup.mk' (Uc.subgroupOf Mc))) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let Uc := localModule T Mc
  let E := thompsonFixed T V
  let C := centralizer (E : Set G)
  let H := conjugateSpanBy V C
  let K := (commutatorPreimage Mc H E).subgroupOf Mc
  let E₂ := E ⊓ commutatorPreimage (T : Subgroup G) (T : Subgroup G) Uc
  let H₂ := conjugateSpanBy E₂ Mc
  have hVQ := h.decomposable_five_partner_two_core
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  have hres := h.decomposable_five_partner_two_residual_centralizes
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  obtain ⟨hMcZ, hMcEgen, hresE⟩ := hres
  obtain ⟨hUcZ, hMcZ', _, _, _⟩ := h.decomposable_five_partner_two_fixed_line
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  have hMcUc : Mc = centralizer (Uc : Set G) :=
    hMcZ'.trans (congrArg (fun W : Subgroup G => centralizer (W : Set G)) hUcZ.symm)
  have hMcUn : Mc ≤ normalizer (Uc : Set G) := by
    rw [hMcUc]
    exact Subgroup.centralizer_le_normalizer _
  let : (Uc.subgroupOf Mc).Normal :=
    normal_subgroupOf_of_le_normalizer hMcUn
  have hspan := h.decomposable_five_span_section
    hG T hempty hM hmany hJ hu hne hfull c d hd s π hp hs hdec hq hfive
  obtain ⟨hspanV, hNE, hspanEq, hNH, hspanData⟩ := hspan
  obtain ⟨hKle, hKnormal, hnoComp⟩ := h.decomposable_five_section_kernel_obstruction
    hG T hempty hM hmany hJ hu hne hfull c d hd s π hp hs hdec hq hfive
  obtain ⟨hUE₂, hE₂E, hE₂card, hdisp, hE₂H, hH₂F, hMcH₂, hH₂elem, hH₂red⟩ :=
    h.decomposable_five_partner_two_second_seed
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  exact ⟨hVQ, hMcUc, hMcEgen, hresE, hNE, hspanEq, hNH, hKle,
    ⟨hKnormal, hnoComp, hUE₂, hE₂E, hE₂card, hdisp, hE₂H, hH₂F,
      hMcH₂, hH₂elem, ⟨inferInstance, hH₂red⟩⟩⟩

/- The order-five marked residual has an actual normal intersection with the
   partner, retaining the original first support and the literal V-centralizer. -/
theorem PreparedChosenModule.decomposable_five_partner_two_marked_residual_intersection
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map
          (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized)
        (T : Subgroup G) M (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      Nat.card (localModule T Mc) = 2 →
      let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
      let G₁ := centralizer (Z₁ : Set G)
      let C := M ⊓ G₁
      letI := caseI_module_centralizer_normal (Z1 := Z₁) h.normalized
      Nat.card (pResidual 2 (C ⧸
        (M ⊓ centralizer (V : Set G)).subgroupOf C)) = 5 →
      let N := M ⊓ centralizer (V : Set G)
      let H := M ⊓ Mc ⊓ G₁
      let E₂ := thompsonFixed T V ⊓
        commutatorPreimage (T : Subgroup G) (T : Subgroup G) (localModule T Mc)
      E₂ ≤ H ∧
        ∃ hN : (N.subgroupOf C).Normal, letI := hN
          (pResidual 2 H).map H.subtype = (pResidual 2 N).map N.subtype := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU Z₁ G₁ C hcard N H E₂
  let S := (T : Subgroup G) ⊓ G₁
  have hMcC : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMcC.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hSylC : Chapter1.IsSylowIn 2 S C :=
    s.local_sylow hM.1.2 h.normalized c d π hs
  have hescape : ¬ C ≤ Mc := h.decomposable_five_marked_centralizer_not_le
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  have hNMc : N ≤ Mc := by
    change M ⊓ centralizer (V : Set G) ≤ Mc
    exact inf_le_right.trans (h.centralizer_le_partner T hu)
  have hNC : N ≤ C := inf_le_inf_left M
    (centralizer_le (show Z₁ ≤ V from inf_le_right.trans inf_le_left))
  have hNH : N ≤ H := le_inf (le_inf inf_le_left hNMc) (hNC.trans inf_le_right)
  have hHC : H ≤ C := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hSH : S ≤ H := le_inf (le_inf (inf_le_left.trans hM.1.2)
    (inf_le_left.trans hTMc)) inf_le_right
  let : (N.subgroupOf C).Normal := caseI_module_centralizer_normal h.normalized
  have hI : (pResidual 2 H).map H.subtype = (pResidual 2 N).map N.subtype := by
    obtain ⟨P,hP⟩ := hSylC
    apply embedded_pResidual_intersection_of_prime_quotient_residual C N H hNC hNH hHC P
    · intro x hx
      exact hSH (hP ▸ hx)
    · intro hh
      exact hescape (hh ▸ (show H ≤ Mc from inf_le_left.trans inf_le_right))
    · rw [show Nat.card (pResidual 2 (C ⧸ N.subgroupOf C)) = 5 from hcard]
      decide
  have hET : thompsonFixed T V ≤ (T : Subgroup G) := by
    intro e he
    exact ChapterB.thompsonJ_le _ _
      (((mem_omegaOneCenterAmbient_iff _ e).mp
        (h.thompsonFixed_le_omega T hM he)).1)
  have hE₂M : E₂ ≤ M := (inf_le_left.trans hET).trans hM.1.2
  have hE₂Mc : E₂ ≤ Mc := (inf_le_left.trans hET).trans hTMc
  have hE₂G₁ : E₂ ≤ G₁ := (inf_le_left.trans inf_le_left).trans
    (V.le_centralizer.trans (centralizer_le (show Z₁ ≤ V from inf_le_right.trans inf_le_left)))
  have hE₂H : E₂ ≤ H := le_inf (le_inf hE₂M hE₂Mc) hE₂G₁
  exact ⟨hE₂H, ⟨inferInstance, hI⟩⟩

/-- The second seed is already partner-invariant. Its partner span is itself,
its full ambient normalizer is the partner, and its displacement is exactly
the original central line. -/
theorem PreparedChosenModule.decomposable_five_partner_two_second_seed_normalizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map
          (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized)
        (T : Subgroup G) M (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      Nat.card (localModule T Mc) = 2 →
      let Uc := localModule T Mc
      let E := thompsonFixed T V
      let E₂ := E ⊓ commutatorPreimage (T : Subgroup G) (T : Subgroup G) Uc
      conjugateSpanBy E₂ Mc = E₂ ∧ normalizer (E₂ : Set G) = Mc ∧
        ⁅E₂, Mc⁆ = Uc := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU Uc E E₂
  obtain ⟨hUE₂, hE₂E, _, hdisp, _, _, _, _, _⟩ :=
    h.decomposable_five_partner_two_second_seed
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  obtain ⟨_, hMcgen, _⟩ := h.decomposable_five_partner_two_residual_centralizes
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  obtain ⟨_, _, hfixed, _, _⟩ := h.decomposable_five_partner_two_fixed_line
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  have hMcU : Mc ≤ normalizer (Uc : Set G) := le_normalizer_conjugateSpanBy _ _
  have hCMc : centralizer (E : Set G) ≤ Mc := le_sup_left.trans_eq hMcgen.symm
  have hTMc : (T : Subgroup G) ≤ Mc := le_sup_right.trans_eq hMcgen.symm
  have hMcpre : Mc ≤ commutatorPreimage Mc E₂ Uc := by
    apply hMcgen.le.trans
    refine sup_le (le_commutatorPreimage hCMc ?_)
      (le_commutatorPreimage hTMc ?_)
    · exact (commutator_eq_bot_iff_le_centralizer.mpr
        (centralizer_le hE₂E.le)).le.trans bot_le
    · rw [commutator_comm]
      exact hdisp
  have hcomm : ⁅Mc, E₂⁆ ≤ Uc := (commutator_mono hMcpre le_rfl).trans
    (commutator_commutatorPreimage_le Mc E₂ Uc hMcU)
  have hn : Mc ≤ normalizer (E₂ : Set G) :=
    le_normalizer_iff_commutator_le_right.mpr (hcomm.trans hUE₂.le)
  have hspan : conjugateSpanBy E₂ Mc = E₂ :=
    le_antisymm (conjugateSpanBy_le le_rfl hn) (le_conjugateSpanBy _ _)
  have hMcC : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  let : IsElementaryAbelian 2 E₂ := IsElementaryAbelian.of_le
    (hE₂E.le.trans (show E ≤ V from inf_le_left))
  have hne : E₂ ≠ ⊥ := ne_bot_of_gt (bot_le.trans_lt hUE₂)
  have hnEq : normalizer (E₂ : Set G) = Mc :=
    (hMcC.1.eq_of_le ⟨E₂, hne, IsElementaryAbelian.isPGroup 2 E₂, rfl⟩ hn).symm
  have hcommNe : ⁅E₂, Mc⁆ ≠ ⊥ := by
    intro hz
    have hcentral : E₂ ≤ centralizer (T : Set G) :=
      (commutator_eq_bot_iff_le_centralizer.mp hz).trans (centralizer_le hTMc)
    have hE₂F : E₂ ≤ conjugateSpanBy E (centralizer (Uc : Set G)) :=
      hE₂E.le.trans (le_conjugateSpanBy _ _)
    exact hUE₂.not_ge ((le_inf hE₂F hcentral).trans hfixed.le)
  have hc : ⁅E₂, Mc⁆ = Uc := eq_of_le_of_card_ge
    (by rwa [commutator_comm]) (by
      have hh := (one_lt_card_iff_ne_bot ⁅E₂, Mc⁆).mpr hcommNe
      change Nat.card Uc = 2 at hcU
      omega)
  exact ⟨hspan, hnEq, hc⟩

/-- The actual marked quintic actor moves the second seed onto the whole
opposite support. In particular neither that actor nor the marked two-residual
normalizes the seed. -/
theorem PreparedChosenModule.decomposable_five_partner_two_second_seed_support
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map
          (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized)
        (T : Subgroup G) M (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      Nat.card (localModule T Mc) = 2 →
      let E := thompsonFixed T V
      let E₂ := E ⊓ commutatorPreimage (T : Subgroup G) (T : Subgroup G)
        (localModule T Mc)
      let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
      let C := M ⊓ centralizer (Z₁ : Set G)
      let Y := (primeToResidual 5 C).map C.subtype
      ⁅E₂, Y⁆ = plane V (c.ambientFactor d s.second).space ∧
        ¬ Y ≤ normalizer (E₂ : Set G) ∧
        ¬ (pResidual 2 C).map C.subtype ≤ Mc := by
  subst V
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU E E₂ Z₁ C Y
  have hr := source_centralizing_full_cases_twoRank hG T hM U c d hd π hp hs
    (Or.inr (Or.inr (Or.inl hdec)))
  have ha := (h.thompson_actors T hM.1.2 hq
    (fun A hA => hA.rank_le_of_primeRank_le hr)).1
  have hm := (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
  have hJi := (chosen_thompson_images_of_source_decomposable T hM.1.2 h.normalized
    hm ha c d π hp hdec).1
  let V := localModule T M
  let Z₂ := thompsonPlane T V (c.ambientFactor d s.second).space
  let V₂ := plane V (c.ambientFactor d s.second).space
  obtain ⟨_, _, hmove, _, _, _, _, hYR⟩ :=
    s.quintic_actor_geometry hM.1.2 h.normalized c d π hp hs hJi hfive
  have hNE := h.decomposable_five_fixed_normalizer_eq_partner
    hG T hempty hM hmany hJ hu rfl c d hd s π hp hs hdec hq hfive
  obtain ⟨_, hNE₂, _⟩ := h.decomposable_five_partner_two_second_seed_normalizer
    hG T hempty hM hmany hJ hu rfl c d hd s π hp hs hdec hq hfive hcU
  have hYB : Y ≤ normalizer (V₂ : Set G) := by
    rw [show V₂ = ⁅V, Y⁆ from hmove.symm]
    exact normalizer_commutator_ge_right V Y
  have hout : ¬ Y ≤ Mc := by
    intro hYMc
    have hYE : Y ≤ normalizer (E : Set G) := hYMc.trans_eq hNE.symm
    have hYZ₂ : Y ≤ normalizer (Z₂ : Set G) :=
      (le_inf hYB hYE).trans inf_normalizer_le_normalizer_inf
    rcases s.quintic_actor_irreducible hM.1.2 h.normalized c d π hp hs hJi hfive
        Z₂ inf_le_left hYZ₂ with hz | hz
    · have hc : Nat.card Z₂ = 4 := s.thompson_card s.second
      rw [hz, card_bot] at hc
      omega
    · have hc : Nat.card Z₂ = 4 := s.thompson_card s.second
      rw [hz, s.support_card] at hc
      omega
  have hcommB : ⁅E₂, Y⁆ ≤ V₂ :=
    (commutator_mono (show E₂ ≤ V from inf_le_left.trans inf_le_left) le_rfl).trans
      hmove.le
  have hcommEq : ⁅E₂, Y⁆ = V₂ := by
    rcases s.quintic_actor_irreducible hM.1.2 h.normalized c d π hp hs hJi hfive
        ⁅E₂, Y⁆ hcommB (normalizer_commutator_ge_right E₂ Y) with hz | he
    · have hYC : Y ≤ centralizer (E₂ : Set G) :=
        le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz)
      exact (hout ((hYC.trans (Subgroup.centralizer_le_normalizer _)).trans_eq hNE₂)).elim
    · exact he
  exact ⟨hcommEq, fun hn => hout (hn.trans_eq hNE₂), fun hR => hout (hYR.trans hR)⟩

/-- The marked Sylow centralizer fixes the actual second seed. If that
seed has order eight, it generates E together with the first marked plane,
so the marked Sylow centralizer is normal in T. -/
theorem PreparedChosenModule.decomposable_five_partner_two_second_seed_marked_sylow
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map
          (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized)
        (T : Subgroup G) M (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      Nat.card (localModule T Mc) = 2 →
      let E := thompsonFixed T V
      let E₂ := E ⊓ commutatorPreimage (T : Subgroup G) (T : Subgroup G)
        (localModule T Mc)
      let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
      let S := (T : Subgroup G) ⊓ centralizer (Z₁ : Set G)
      S ≤ centralizer (E₂ : Set G) ∧
        (Nat.card E₂ = 8 → S = (T : Subgroup G) ⊓ centralizer (E : Set G) ∧
          (S.subgroupOf (T : Subgroup G)).Normal) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU E E₂ Z₁ S
  let Uc := localModule T Mc
  let Z₂ := thompsonPlane T V (c.ambientFactor d s.second).space
  obtain ⟨_, hE₂E, _, hdisp, _, _, _, _, _⟩ :=
    h.decomposable_five_partner_two_second_seed
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  obtain ⟨hUZ, hMcZ, _, _, _⟩ := h.decomposable_five_partner_two_fixed_line
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  obtain ⟨_, hNE₂, _⟩ := h.decomposable_five_partner_two_second_seed_normalizer
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  have hTMc : (T : Subgroup G) ≤ Mc := by
    rw [hMcZ]
    exact le_centralizer_iff.mp (centralInvolutions_le_centralizer_sylow T)
  have hTE₂ : (T : Subgroup G) ≤ normalizer (E₂ : Set G) := hTMc.trans_eq hNE₂.symm
  have hTE : (T : Subgroup G) ≤ normalizer (E : Set G) := hTMc.trans_eq
    (h.decomposable_five_fixed_normalizer_eq_partner
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).symm
  have hUcT : Uc ≤ centralizer (T : Set G) := by
    rw [show Uc = centralInvolutions T from hUZ]
    exact centralInvolutions_le_centralizer_sylow T
  obtain ⟨t, ht, hout⟩ : ∃ t ∈ (T : Subgroup G),
      t ∉ normalizer (plane V (c.ambientFactor d s.first).space : Set G) := by
    by_contra! hall
    have hh := relIndex_eq_one.mpr (le_inf le_rfl hall)
    rw [s.stabilizer_index] at hh
    contradiction
  have hex := s.thompson_exchanges t ht hout
  change Z₁.map (MulAut.conj t).toMonoidHom = Z₂ ∧
    Z₂.map (MulAut.conj t).toMonoidHom = Z₁ at hex
  have hdis : Uc ⊓ Z₂ = ⊥ := by
    apply bot_unique
    intro z hz
    have he : t*z*t⁻¹ = z :=
      mul_inv_eq_iff_eq_mul.mpr (hUcT hz.1 t ht)
    have hz₁ : z ∈ Z₁ := he ▸
      (hex.2 ▸ mem_map_of_mem (MulAut.conj t).toMonoidHom hz.2)
    exact s.thompson_disjoint.le ⟨hz₁, hz.2⟩
  have hSZ₂ : S ≤ normalizer (Z₂ : Set G) := fun x hx =>
    (s.thompson_normalized ⟨hx.1, s.centralizer_le_stabilizer hx⟩).2
  have hEZ₂ : E ≤ normalizer (Z₂ : Set G) :=
    ((show E ≤ V from inf_le_left).trans
      (V.le_centralizer.trans (centralizer_le
        (show Z₂ ≤ V from inf_le_right.trans inf_le_left)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hEpre : E ≤ commutatorPreimage E S Z₂ := by
    rw [show E = Z₁ ⊔ Z₂ from s.thompson_split]
    refine sup_le (le_commutatorPreimage le_sup_left ?_)
      (le_commutatorPreimage le_sup_right ?_)
    · exact (commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp (show S ≤ centralizer (Z₁ : Set G) from inf_le_right))).le.trans bot_le
    · exact le_normalizer_iff_commutator_le_left.mp hSZ₂
  have hE₂S : ⁅E₂, S⁆ = ⊥ := by
    apply bot_unique
    rw [← hdis]
    exact le_inf ((commutator_mono le_rfl inf_le_left).trans hdisp)
      ((commutator_mono (hE₂E.le.trans hEpre) le_rfl).trans
        (commutator_commutatorPreimage_le E S Z₂ hEZ₂))
  have hSE₂ : S ≤ centralizer (E₂ : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hE₂S)
  refine ⟨hSE₂, ?_⟩
  intro hcard
  have hnot : ¬ Z₁ ≤ E₂ := by
    intro hZ₁
    have hZ₂ : Z₂ ≤ E₂ := by
      have hh := (map_mono (f := (MulAut.conj t).toMonoidHom) hZ₁).trans_eq
        (mem_normalizer_iff_map_conj_eq.mp (hTE₂ ht))
      rwa [hex.1] at hh
    exact hE₂E.not_ge (s.thompson_split.le.trans (sup_le hZ₁ hZ₂))
  have hlt : E₂ < E₂ ⊔ Z₁ := lt_of_le_of_ne le_sup_left (by
    intro he
    exact hnot (he ▸ (show Z₁ ≤ E₂ ⊔ Z₁ from le_sup_right)))
  have hjoinLe : E₂ ⊔ Z₁ ≤ E := sup_le hE₂E.le inf_le_right
  have hjoin : E₂ ⊔ Z₁ = E := eq_of_le_of_card_ge hjoinLe (by
    have hh : Nat.card E₂ < Nat.card (E₂ ⊔ Z₁ : Subgroup G) :=
      Nat.lt_of_not_ge (fun hh => hlt.ne (eq_of_le_of_card_ge hlt.le hh))
    have hdvd : Nat.card (E₂ ⊔ Z₁ : Subgroup G) ∣ 16 :=
      s.fixed_card ▸ card_dvd_of_le hjoinLe
    have hmem := Nat.mem_divisors.mpr ⟨hdvd, by decide⟩
    rw [show Nat.divisors 16 = {1, 2, 4, 8, 16} by decide] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rw [show Nat.card E = 16 from s.fixed_card]
    omega)
  have hSE : S ≤ centralizer (E : Set G) := le_centralizer_iff.mp (by
    rw [← hjoin]
    exact sup_le (le_centralizer_iff.mp hSE₂)
      (le_centralizer_iff.mp (show S ≤ centralizer (Z₁ : Set G) from inf_le_right)))
  have he : S = (T : Subgroup G) ⊓ centralizer (E : Set G) :=
    le_antisymm (le_inf inf_le_left hSE)
      (inf_le_inf_left _ (centralizer_le (show Z₁ ≤ E from inf_le_right)))
  refine ⟨he, ?_⟩
  rw [he]
  exact normal_subgroupOf_of_le_normalizer
    ((le_inf (T : Subgroup G).le_normalizer
      (hTE.trans (normalizer_le_normalizer_centralizer _))).trans
        inf_normalizer_le_normalizer_inf)

end CFSG.Quasithin.Chapter15.Section01
