module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoSupportActors
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSectionComponentNatural
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSectionComponentNormalizerFull
public import Theory.Representation.BinaryOffender.PerfectCentralizer
public import Theory.Representation.BinaryOffender.SemisimpleIrrPlus
public import Theory.Representation.CliffordSubquotient

/-!
# An original support plane determines a whole normal component

A support plane lies in the Sylow-stable image of E, of dimension at most
three. Its Sylow conjugates therefore overlap. Distinct components have
separated moved spaces here: perfect centralizer control gives crossed
fixed spaces, and Clifford semisimplicity removes their intersection.
The component is consequently Sylow normalized, then normal by the
classification of the actual offender normal closure. Irreducibility
makes its moved space the whole original section.

The two narrow private component-selection proofs below reproduce the
existing SectionOriginalComponent argument so its private declarations do
not become an import contract.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.DecomposableQuinticControl
open ChapterB.QuasisimpleSource ChapterB.SourceInduction
variable {G W : Type*} [Group G] [Finite G]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

private theorem strong_minimal_centralizes_fitting
    (ρ : Representation (ZMod 2) G W) (hf : Function.Injective ρ)
    (hcore : pCore 2 G = ⊥) {B : Subgroup G}
    (hB : IsMinimalBestOffender ρ B) (hstrong : IsStrongOffender ρ B) :
    B ≤ centralizer (fittingSubgroup G : Set G) := by
  by_contra hn
  have hmove : ⁅fittingSubgroup G,B⁆ ≠ ⊥ := by
    intro hz
    exact hn (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz))
  obtain ⟨b⟩ := ChapterB.FittingStructure.localPlaneLaw ρ hf hcore B hB hmove
  have hr : rank B = 1 := by
    rw [rank,b.actor_card]
    decide
  have hpos := fixedCodim_pos_of_faithful ρ hf hB.1.1.1
  have hlt := hstrong.2
  rw [hr] at hlt
  omega

private theorem component_of_minimal_strong_plane
    (ρ : Representation (ZMod 2) G W) (hf : Function.Injective ρ)
    (hcore : pCore 2 G = ⊥)
    (cover : SQTKQuotient KnownSimple.IsKnownSimple G)
    {A : Subgroup G} (hA : IsMinimalBestOffender ρ A)
    (hstrong : IsStrongOffender ρ A)
    (hd : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) ≤ 2) :
    A ≤ centralizer (fittingSubgroup G : Set G) ∧
      ∃ K, IsComponent G K ∧ ⁅K,A⁆ = K ∧
        K ≤ normalClosure (A : Set G) ∧
        (K.subgroupOf (normalClosure (A : Set G))).Normal ∧
        IsIrrPlus ρ K (moved ρ K) ∧ SmallMoved.ActorList K := by
  have hfit := strong_minimal_centralizes_fitting ρ hf hcore hA hstrong
  obtain ⟨K,hK,hmove⟩ := ComponentReduction.exists_component_moved ρ hcore hA.1 hfit
  have hn : A ≤ normalizer (K : Set G) := ChapterB.source_lemma_B_1_5_4 ρ hf hA.1 hK
  have hKA : ⁅K,A⁆ = K := by
    rcases hK.commutator_dichotomy A with hz | he
    · exact (hmove hz).elim
    · exact le_antisymm (le_normalizer_iff_commutator_le_left.mp hn)
        (he ▸ le_iSup_conjugates K A)
  obtain ⟨hKN,hnK,_⟩ := moved_component_in_normalClosure ρ hf hK hA.1 hKA
  obtain ⟨hirr,hlist⟩ := component_irrPlus_and_actor_of_minimal_plane ρ hf hcore cover
    hK hA hKA hd
  exact ⟨hfit,K,hK,hKA,hKN,hnK,hirr,hlist⟩


omit [Finite G] in
private theorem component_normalized_of_small_invariant_span
    (ρ : Representation (ZMod 2) G W) [IsIrreducible ρ]
    {K S : Subgroup G} (hK : IsComponent G K)
    (hI : IsIrrPlus ρ K (moved ρ K))
    (P X : Submodule (ZMod 2) W) (hPK : P ≤ moved ρ K)
    (hPX : P ≤ X) (hP : Module.finrank (ZMod 2) P = 2)
    (hX : Module.finrank (ZMod 2) X ≤ 3)
    (hSX : S ≤ subspaceStabilizer ρ X) : S ≤ normalizer (K : Set G) := by
  let : IsSemisimpleRepresentation (ρ.comp K.subtype) :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mpr
      (subnormal_restriction_semisimple ρ K hK.1)
  have hzero := hI.inf_fixedSpace_eq_bot_of_semisimple ρ
  intro t ht
  apply mem_normalizer_iff_map_conj_eq.mpr
  by_contra hne
  let J := K.map (MulAut.conj t).toMonoidHom
  have hJ : IsComponent G J := hK.map_conj t
  let : IsQuasisimple J := hJ.2
  have hJK : J ≤ centralizer (K : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (hJ.commutator_eq_bot_of_ne hK hne)
  have hJS : J ≤ subspaceStabilizer ρ (moved ρ K) :=
    subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial))
      (hJK.trans (Subgroup.centralizer_le_normalizer _))
  have hfix : moved ρ K ≤ fixedSpace ρ J :=
    hI.le_fixedSpace_of_perfect_centralizes ρ hJK hJS
  have hdis : P ⊓ P.map (ρ t) = ⊥ := by
    apply bot_unique
    rintro v ⟨hv, w, hw, rfl⟩
    have hwfix : w ∈ fixedSpace ρ K := by
      intro k
      change ρ k.val w = w
      have he := hfix (hPK hv)
        ⟨t*k.val*t⁻¹, mem_map_of_mem (MulAut.conj t).toMonoidHom k.property⟩
      change ρ (t*k.val*t⁻¹) (ρ t w) = ρ t w at he
      have hh := congrArg (ρ t⁻¹) he
      simpa only [← Module.End.mul_apply, ← map_mul, mul_assoc,
        inv_mul_cancel_left, inv_mul_cancel, mul_one, map_one,
        Module.End.one_apply] using hh
    have hwzero : w = 0 := by
      have hh : w ∈ moved ρ K ⊓ fixedSpace ρ K := ⟨hPK hw,hwfix⟩
      rwa [hzero] at hh
    simp only [hwzero,map_zero,Submodule.zero_mem]
  have htPX : P.map (ρ t) ≤ X := by
    rintro _ ⟨v,hv,rfl⟩
    exact (hSX ht v).2 (hPX hv)
  have hdim := P.finrank_sup_add_finrank_inf_eq (P.map (ρ t))
  have hbound := Submodule.finrank_mono (sup_le hPX htPX)
  rw [hdis,finrank_bot,finrank_map_action ρ,hP] at hdim
  omega

/-- A minimal strong plane offender whose displacement lies in a
Sylow-invariant three-space moves a normal component on the whole module. -/
theorem whole_component_of_small_sylow_moved_span
    (ρ : Representation (ZMod 2) G W) [IsIrreducible ρ]
    (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    (cover : SQTKQuotient KnownSimple.IsKnownSimple G)
    {A : Subgroup G} (hA : IsMinimalBestOffender ρ A)
    (hstrong : IsStrongOffender ρ A)
    (hd : Module.finrank (ZMod 2) (moved ρ A) = 2)
    (S : Sylow 2 G) (X : Submodule (ZMod 2) W)
    (hAX : moved ρ A ≤ X) (hX : Module.finrank (ZMod 2) X ≤ 3)
    (hSX : (S : Subgroup G) ≤ subspaceStabilizer ρ X) :
    A ≤ centralizer (fittingSubgroup G : Set G) ∧
      ∃ K, IsComponent G K ∧ ⁅K,A⁆ = K ∧
        K ≤ normalClosure (A : Set G) ∧ K.Normal ∧
        moved ρ K = ⊤ ∧ IsIrrPlus ρ K ⊤ ∧ SmallMoved.ActorList K := by
  obtain ⟨hfit,K,hK,hKA,hKN,_,hI,hlist⟩ :=
    component_of_minimal_strong_plane ρ hf hcore cover hA hstrong hd.le
  let : IsQuasisimple K := hK.2
  have hAK : moved ρ A ≤ moved ρ K := hA.moved_le_moved_perfect ρ hf
    hK.isCComponent.ne_bot hd.le hKA
  have hSK := component_normalized_of_small_invariant_span ρ hK hI
    (moved ρ A) X hAK hAX hd hX hSX
  have hn := component_normal_of_sylow_normalizes_of_normalClosure_best
    ρ hf hcore cover hA.1 hK hKA S hSK
  let : K.Normal := hn
  have hs : (⊤ : Subgroup G) ≤ subspaceStabilizer ρ (moved ρ K) :=
    subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial))
      (by rw [normalizer_eq_top K])
  let I : Subrepresentation ρ := ⟨moved ρ K,fun g v hv => (hs (mem_top g) v).2 hv⟩
  have hItop : I = ⊤ := (inferInstance : IsIrreducible ρ).eq_bot_or_eq_top I
    |>.resolve_left (fun he => hI.ne_bot ρ (congrArg Subrepresentation.toSubmodule he))
  have hm : moved ρ K = ⊤ := congrArg Subrepresentation.toSubmodule hItop
  exact ⟨hfit,K,hK,hKA,hKN,hn,hm,hm ▸ hI,hlist⟩

end CFSG.Quasithin.Chapter15.DecomposableQuinticControl

namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The unchanged original support actor yields a normal component acting
naturally on the whole supplied canonical section. The denominator and
coordinates remain the original ones. -/
theorem PreparedChosenModule.decomposable_five_partner_two_support_component
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      Nat.card (localModule T Mc) = 2 →
      let E := thompsonFixed T V
      let C := centralizer (localModule T Mc : Set G)
      let F := conjugateSpanBy E C
      let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
      let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
      V ≤ Mc.pCoreIn 2 ∨
        ∀ {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
          (ρ : Representation (ZMod 2) Mc W) (dF : BinaryConjugationSection Mc F D ρ),
          D ⊓ Z₁ = ⊥ →
          let A₁ := actionSubgroup ρ
            ((plane V (c.ambientFactor d s.first).space).subgroupOf Mc)
          let σ := Representation.BinaryOffender.imageRepresentation ρ
          rank A₁ = 2 ∧ fixedCodim σ A₁ = 1 ∧
            IsMinimalBestOffender σ A₁ ∧ IsStrongOffender σ A₁ ∧
            subspaceCommutator σ ⊤ A₁ = dF.imageSpace Z₁ ∧
            A₁ ≤ centralizer (fittingSubgroup (Representation.BinaryOffender.actionImage ρ) :
              Set (Representation.BinaryOffender.actionImage ρ)) ∧
            ∃ K, IsComponent (Representation.BinaryOffender.actionImage ρ) K ∧
              ⁅K,A₁⁆ = K ∧
              K ≤ normalClosure (A₁ : Set (Representation.BinaryOffender.actionImage ρ)) ∧
              K.Normal ∧ ChapterB.QuasisimpleSource.moved σ K = ⊤ ∧
              IsIrrPlus σ K ⊤ ∧ ChapterB.QuasisimpleSource.SmallMoved.ActorList K ∧
              ∃ n : ℕ, (n = 3 ∨ n = 4 ∨ n = 5) ∧
                Nonempty (ActionEquiv (σ.comp K.subtype)
                  (linearNatural BinaryField.two n)) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let E := thompsonFixed T V
  let Uc := localModule T Mc
  let C := centralizer (Uc : Set G)
  let F := conjugateSpanBy E C
  let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
  let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
  by_cases hVQ : V ≤ Mc.pCoreIn 2
  · exact Or.inl hVQ
  right
  intro W _ _ ρ dF hDZ
  let : Finite W := Finite.of_surjective (fun x : F => (dF.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp dF.onto)
  let σ := Representation.BinaryOffender.imageRepresentation ρ
  let A₁ := actionSubgroup ρ
    ((plane V (c.ambientFactor d s.first).space).subgroupOf Mc)
  have hsupport := ((h.decomposable_five_partner_two_support_actors
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ)
      ρ dF hDZ s.first
  obtain ⟨hr,hcost,hmin,hstrong,hmove⟩ := hsupport
  change subspaceCommutator σ ⊤ A₁ = dF.imageSpace Z₁ at hmove
  have hEF : E ≤ F := le_conjugateSpanBy E C
  have hZ₁F : Z₁ ≤ F := (show Z₁ ≤ E from inf_le_right).trans hEF
  have hdimP : Module.finrank (ZMod 2) (dF.imageSpace Z₁) = 2 := by
    apply dF.imageSpace_finrank_of_index Z₁ hZ₁F 2
    have hh := relIndex_mul_card_of_le (show D ⊓ Z₁ ≤ Z₁ from inf_le_right)
    rw [inf_relIndex_right,hDZ,card_bot,s.thompson_card s.first,mul_one] at hh
    exact hh
  have hdimA : Module.finrank (ZMod 2) (ChapterB.QuasisimpleSource.moved σ A₁) = 2 := by
    change Module.finrank (ZMod 2) (subspaceCommutator σ ⊤ A₁) = 2
    rw [hmove]
    exact hdimP
  have hdimW : 0 < Module.finrank (ZMod 2) W := by
    have hh := Submodule.finrank_le (dF.imageSpace Z₁)
    omega
  let : Nontrivial W := (Module.finrank_pos_iff (R := ZMod 2) (M := W)).mp hdimW
  have hirr : IsIrreducible ρ := (h.decomposable_five_canonical_section_irreducible
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).2 ρ dF
  let : IsIrreducible σ := imageRepresentation_isIrreducible ρ hirr
  have hcore : pCore 2 (Representation.BinaryOffender.actionImage ρ) = ⊥ :=
    actionImage_twoCore_eq_bot ρ hirr
  obtain ⟨_,hUD,_,_,_⟩ := (h.decomposable_five_partner_two_core_or_canonical_action
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ
  obtain ⟨_,hMN,hUE⟩ := h.decomposable_five_partner_control
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  have hindex : Uc.relIndex E = 8 := by
    have hh := (Uc.subgroupOf E).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hUE).toEquiv] at hh
    change Uc.relIndex E * Nat.card Uc = Nat.card E at hh
    rw [hcU,s.fixed_card] at hh
    omega
  have hbound : Nat.card (dF.imageSpace E) ≤ 8 := by
    rw [dF.imageSpace_card_eq_relIndex E hEF]
    exact (relIndex_le_of_le_left hUD index_ne_zero_of_finite).trans_eq hindex
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hbound
  have hdimX : Module.finrank (ZMod 2) (dF.imageSpace E) ≤ 3 :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hbound
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hTN : (T : Subgroup G) ≤ normalizer (E : Set G) :=
    (le_inf hM.1.2 hTMc).trans hMN
  let cover : ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple
      (Representation.BinaryOffender.actionImage ρ) :=
    ⟨Mc,(Representation.BinaryOffender.actionHom ρ).ker,hG.twoLocal_sqtk hMc.1.1,
      QuotientGroup.quotientKerEquivOfSurjective
        (Representation.BinaryOffender.actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective⟩
  let S : Sylow 2 (Representation.BinaryOffender.actionImage ρ) :=
    (T.subtype hTMc).mapSurjective ρ.asGroupHom.rangeRestrict_surjective
  have hSX : (S : Subgroup (Representation.BinaryOffender.actionImage ρ)) ≤
      subspaceStabilizer σ (dF.imageSpace E) := by
    apply le_subspaceStabilizer
    rintro a ⟨t,ht,rfl⟩ v hv
    change ρ t v ∈ dF.imageSpace E
    have hc : E.conjBy (t : G) = E := mem_normalizer_iff_map_conj_eq.mp (hTN ht)
    have hm := dF.imageSpace_conjBy E hEF t
    rw [hc] at hm
    rw [hm]
    exact Submodule.mem_map_of_mem (f := ρ t) hv
  have hAX : ChapterB.QuasisimpleSource.moved σ A₁ ≤ dF.imageSpace E := by
    change subspaceCommutator σ ⊤ A₁ ≤ dF.imageSpace E
    rw [hmove]
    exact dF.imageSpace_mono inf_le_right
  obtain ⟨hfit,K,hK,hKA,hKN,hnK,hm,hI,hlist⟩ :=
    DecomposableQuinticControl.whole_component_of_small_sylow_moved_span
      σ (imageRepresentation_injective ρ) hcore cover hmin hstrong hdimA
      S (dF.imageSpace E) hAX hdimX hSX
  obtain ⟨n,hn,he⟩ := DecomposableQuinticControl.whole_component_natural_of_half_cost
    σ (imageRepresentation_injective ρ) hcore cover hK hmin hKA
    (Or.inl ⟨hr,hcost⟩) hdimA.le hm
  exact ⟨hr,hcost,hmin,hstrong,hmove,hfit,K,hK,hKA,hKN,hnK,hm,hI,hlist,n,hn,he⟩

end CFSG.Quasithin.Chapter15.Section01
