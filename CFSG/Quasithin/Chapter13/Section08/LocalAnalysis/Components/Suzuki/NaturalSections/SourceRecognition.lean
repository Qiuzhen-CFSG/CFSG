module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.SectionRecognition
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.ActionImage.Structure
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.SuzukiRecognition.Source
public import Theory.Representation.BinaryOffender.CentralImageMoved
public import Theory.Representation.BinaryOffender.SectionSaturation
public import Theory.Representation.BinaryOffender.QuadraticComponentSection
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalModule.Normal.Restriction

/-!
# The full moved central section of a normal Suzuki component

Chapter K recognizes the faithful irreducible Suzuki action and bounds every
nontrivial elementary actor's fixed codimension below by twice its rank.
Choose a literal component-irreducible section retaining the quadratic actor.
The original upper bound forces equality. The actor, and then the simple
component, fix the denominator and the quotient above that section.
Central-surjective transport therefore makes the entire moved space Irr⁺;
recognizing its literal central quotient gives the natural Suzuki module.

Restriction to K A and transport along the actual component inclusion extend
the result to every normal component with the prescribed quadratic actor.
There is no assumption that the moved space is the ambient module or that
O₂(K A) vanishes. `NormalSource` supplies the original F.9.18 actor and applies
this recognition to the 13.8.16 contradiction.

Source: Aschbacher--Smith, K.3.6, p.457; F.9.18(4,7), pp.325--326;
and 13.8.16(2), p.953 (combined manuscript of 1 March 2004).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
open BenderSuzuki.MatrixGroups
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.SourceRecognition
open ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.ActionImage.Structure
open Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions
universe u
variable {D V : Type u} [Group D] [Finite D]
  [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

/-- Recognition at the literal generalized Fitting subgroup, with no B.4 callback. -/
theorem natural_of_small_quadratic
    (ρ : Representation (ZMod 2) D V)
    (hs : IsSQTK KnownSimple.IsKnownSimple D) (hf : Function.Injective ρ)
    (hqs : IsQuasisimple (generalizedFitting D))
    (hi : IsIrreducible (ρ.comp (generalizedFitting D).subtype))
    (hq : quadraticRatio ρ ≤ 2) {m : ℕ} (hm : 0 < m)
    (e : generalizedFitting D ≃* SuzukiMatrixGroup m) :
    Nonempty (ActionEquiv (ρ.comp (generalizedFitting D).subtype) (natural m)) := by
  let : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  let := hqs
  have hz := SectionRecognition.center_eq_bot_of_equiv_suzuki e
  let eq : (generalizedFitting D ⧸ center (generalizedFitting D)) ≃* SuzukiMatrixGroup m :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans (QuotientGroup.quotientBot.trans e)
  have hsource : ChapterK.RankOne.SourceHypotheses ρ (generalizedFitting D) :=
    ⟨hs,rfl,hqs,hf,hi,(cubicRatio_le_quadraticRatio ρ).trans hq⟩
  let M := hsource.suzukiModel (by omega) eq
  exact ⟨⟨M.groupEquiv,M.coordinates,M.intertwines⟩⟩

/-- The recognized Suzuki action uses at least twice the rank of every elementary actor. -/
theorem small_quadratic_codim_lower
    (ρ : Representation (ZMod 2) D V)
    (hs : IsSQTK KnownSimple.IsKnownSimple D) (hf : Function.Injective ρ)
    (hqs : IsQuasisimple (generalizedFitting D))
    (hi : IsIrreducible (ρ.comp (generalizedFitting D).subtype))
    (hq : quadraticRatio ρ ≤ 2) {m : ℕ} (hm : 0 < m)
    (e : generalizedFitting D ≃* SuzukiMatrixGroup m)
    (A : Subgroup D) (hA : IsElementaryTwo A) : 2 * rank A ≤ fixedCodim ρ A := by
  let : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  let := hqs
  have hz := SectionRecognition.center_eq_bot_of_equiv_suzuki e
  let eq : (generalizedFitting D ⧸ center (generalizedFitting D)) ≃* SuzukiMatrixGroup m :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans (QuotientGroup.quotientBot.trans e)
  have hsource : ChapterK.RankOne.SourceHypotheses ρ (generalizedFitting D) :=
    ⟨hs,rfl,hqs,hf,hi,(cubicRatio_le_quadraticRatio ρ).trans hq⟩
  let M := hsource.suzukiModel (by omega) eq
  have hr := hsource.suzuki_elementary_rank_le M (by omega) hA
  rw [hsource.suzuki_elementary_fixedCodim M (by omega) hA]
  omega

/-- A surviving component-irreducible Suzuki section attains the entire quadratic bound.
Only the action image is made faithful; no ambient two-core hypothesis is needed. -/
theorem component_irreducible_codim
    (ρ : Representation (ZMod 2) D V) (K A : Subgroup D)
    [K.Normal] [IsQuasisimple K] {m : ℕ} (hm : 0 < m)
    (eK : K ≃* SuzukiMatrixGroup m)
    (hs : IsSQTK KnownSimple.IsKnownSimple D) (hquot : IsPGroup 2 (D ⧸ K))
    (hi : IsIrreducible (ρ.comp K.subtype)) (hn : ¬ K ≤ (actionHom ρ).ker)
    (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hc : fixedCodim ρ A ≤ 2 * rank A)
    (hAC : A ⊓ centralizer (K : Set D) = ⊥) : fixedCodim ρ A = 2 * rank A := by
  let : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hcomp : IsComponent D K := ⟨(inferInstance : K.Normal).isSubnormal,inferInstance⟩
  have hker : (actionHom ρ).ker ≤ centralizer (K : Set D) :=
    commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm _ _).trans
      ((hcomp.normal_dichotomy (actionHom ρ).ker).resolve_left hn))
  have hfaith : ∀ a ∈ A, (∀ v, ρ a v = v) → a = 1 := by
    intro a ha hh
    have haC := hker ((actionHom_eq_one_iff ρ a).mpr hh)
    have hb : a ∈ (⊥ : Subgroup D) :=
      hAC ▸ (show a ∈ A ⊓ centralizer (K : Set D) from ⟨ha,haC⟩)
    exact hb
  have hsmall : quadraticRatio (imageRepresentation ρ) ≤ 2 := by
    apply (quadraticRatio_le_two_iff _).mpr
    refine ⟨actionSubgroup ρ A,hA.actionSubgroup ρ hfaith,?_,?_⟩
    · rintro a ⟨x,hx,rfl⟩ b ⟨y,hy,rfl⟩ v
      exact hq x hx y hy v
    · rw [fixedCodim_actionSubgroup,actionSubgroup_rank ρ A hfaith]
      exact hc
  have hz := SectionRecognition.center_eq_bot_of_equiv_suzuki eK
  obtain ⟨hqs,hirr,hfit⟩ := image_structure ρ K hn hquot hi
  let e := componentEquiv ρ K hn hz
  let f : generalizedFitting (actionImage ρ) ≃* actionSubgroup ρ K := MulEquiv.subgroupCongr hfit
  let : IsQuasisimple (actionSubgroup ρ K) := hqs
  have hquasi := IsQuasisimple.of_mulEquiv f.symm
  have hirrF : IsIrreducible ((imageRepresentation ρ).comp
      (generalizedFitting (actionImage ρ)).subtype) := by rw [hfit]; exact hirr
  have hl := small_quadratic_codim_lower (imageRepresentation ρ)
    (image_sqtk ρ K hn hs hquot hz) (imageRepresentation_injective ρ)
    hquasi hirrF hsmall hm (f.trans (e.symm.trans eK))
    (actionSubgroup ρ A) (hA.actionSubgroup ρ hfaith)
  rw [fixedCodim_actionSubgroup,actionSubgroup_rank ρ A hfaith] at hl
  exact le_antisymm hc hl

private def factorFixed (ρ : Representation (ZMod 2) D V) (K : Subgroup D) [K.Normal]
    (I : Subrepresentation ρ) : Subrepresentation I.toRepresentation where
  toSubmodule := (fixedSpace ρ K).comap I.toSubmodule.subtype
  apply_mem_toSubmodule g v hv := (fixedSpace_stable_of_normal ρ K (mem_top g) v).2 hv

private def factor (ρ : Representation (ZMod 2) D V) (K : Subgroup D) [K.Normal]
    (I : Subrepresentation ρ) : Representation (ZMod 2) D (centralQuotient ρ K I.toSubmodule) :=
  (factorFixed ρ K I).quotientRepresentation

/-- The actual central quotient of an invariant Irr+ member is natural. -/
theorem invariant_natural_section
    (ρ : Representation (ZMod 2) D V) (K : Subgroup D) [K.Normal] [IsQuasisimple K]
    {m : ℕ} (hm : 0 < m) (eK : K ≃* SuzukiMatrixGroup m)
    (hD : IsSQTK KnownSimple.IsKnownSimple D) (hquot : IsPGroup 2 (D ⧸ K))
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ K I)
    (hs : (⊤ : Subgroup D) ≤ subspaceStabilizer ρ I)
    (A : Subgroup D) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hc : fixedCodim ρ A ≤ 2 * rank A)
    (hAC : Disjoint A (centralizer (K : Set D))) :
    Nonempty (ActionEquiv (centralQuotientRepresentation ρ K I hI.choose) (natural m)) := by
  let : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  let S : Subrepresentation ρ := ⟨I,fun g _ hv => (hs (mem_top g) _).2 hv⟩
  let σ := factor ρ K S
  let : Finite (centralQuotient ρ K S.toSubmodule) := Module.finite_of_finite (ZMod 2)
  have hsurvive : ¬ K ≤ (actionHom σ).ker := by
    intro hh
    apply hI.not_le_fixedSpace ρ
    rw [← hI.choose_spec.1]
    apply Submodule.span_le.mpr
    rintro _ ⟨k,hk,v,hv,rfl⟩
    have hfix := (actionHom_eq_one_iff σ k).mp (hh hk)
      (Submodule.Quotient.mk (⟨v,hv⟩ : I))
    exact (Submodule.Quotient.eq ((fixedSpace ρ K).comap I.subtype)).mp hfix
  have hi : IsIrreducible (σ.comp K.subtype) := hI.choose_spec.2
  obtain ⟨hqs,hirr,hfit⟩ := image_structure σ K hsurvive hquot hi
  have hcomp : IsComponent D K := ⟨(inferInstance : K.Normal).isSubnormal,inferInstance⟩
  have hker : (actionHom σ).ker ≤ centralizer (K : Set D) :=
    commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm _ _).trans
      ((hcomp.normal_dichotomy (actionHom σ).ker).resolve_left hsurvive))
  have hfaith : ∀ a ∈ A, (∀ v, σ a v = v) → a = 1 := by
    intro a ha hh
    exact (disjoint_iff_inf_le.mp hAC) ⟨ha,hker ((actionHom_eq_one_iff σ a).mpr hh)⟩
  have hqσ : IsQuadratic σ A :=
    quadratic_of_equivariant_surjection S.toRepresentation σ
      (factorFixed ρ K S).toSubmodule.mkQ
      (factorFixed ρ K S).toSubmodule.mkQ_surjective (fun _ _ => rfl) A
      (quadratic_subrepresentation ρ S hq)
  have hsmall : quadraticRatio (imageRepresentation σ) ≤ 2 := by
    apply (quadraticRatio_le_two_iff _).mpr
    refine ⟨actionSubgroup σ A,hA.actionSubgroup σ hfaith,?_,?_⟩
    · rintro a ⟨x,hx,rfl⟩ b ⟨y,hy,rfl⟩ v
      exact hqσ x hx y hy v
    · rw [fixedCodim_actionSubgroup,actionSubgroup_rank σ A hfaith]
      exact (fixedCodim_le_of_equivariant_surjection S.toRepresentation σ
        (factorFixed ρ K S).toSubmodule.mkQ
        (factorFixed ρ K S).toSubmodule.mkQ_surjective (fun _ _ => rfl) A).trans
          ((fixedCodim_subrepresentation_le ρ S A).trans hc)
  have hz := SectionRecognition.center_eq_bot_of_equiv_suzuki eK
  let e := componentEquiv σ K hsurvive hz
  let f : generalizedFitting (actionImage σ) ≃* actionSubgroup σ K := MulEquiv.subgroupCongr hfit
  let : IsQuasisimple (actionSubgroup σ K) := hqs
  have hquasi := IsQuasisimple.of_mulEquiv f.symm
  have hirrF : IsIrreducible ((imageRepresentation σ).comp
      (generalizedFitting (actionImage σ)).subtype) := by rw [hfit]; exact hirr
  obtain ⟨a⟩ := natural_of_small_quadratic (imageRepresentation σ)
    (image_sqtk σ K hsurvive hD hquot hz) (imageRepresentation_injective σ)
    hquasi hirrF hsmall hm (f.trans (e.symm.trans eK))
  refine ⟨⟨(e.trans f.symm).trans a.groupEquiv,a.linearEquiv,?_⟩⟩
  intro k v
  exact a.intertwines (f.symm (e k)) v

/-- A quadratic supplement recognizes the whole moved Suzuki central section.
The denominator and the upper quotient are proved component-central by saturation. -/
theorem natural_moved_of_quadratic_supplement
    (ρ : Representation (ZMod 2) D V) (K A : Subgroup D)
    [K.Normal] [IsQuasisimple K] (hgen : K ⊔ A = ⊤)
    {m : ℕ} (hm : 0 < m) (eK : K ≃* SuzukiMatrixGroup m)
    (hs : IsSQTK KnownSimple.IsKnownSimple D)
    (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hc : fixedCodim ρ A ≤ 2 * rank A)
    (hAC : A ⊓ centralizer (K : Set D) = ⊥) (hn : ¬ K ≤ ρ.ker) :
    Nonempty (ActionEquiv (centralQuotientRepresentation ρ K
      (subspaceCommutator ρ ⊤ K) (subspaceCommutator_invariant ρ ⊤ K)) (natural m)) := by
  let : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hZ := SectionRecognition.center_eq_bot_of_equiv_suzuki eK
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  let : IsSimpleGroup K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  let := hA.2
  have hquot : IsPGroup 2 (D ⧸ K) :=
    isPGroup_quotient_of_sup_eq_top K A (IsElementaryAbelian.isPGroup 2 A) hgen
  obtain ⟨U,N,hi,hnσ,hqσ,hcσ⟩ := exists_component_irreducible_quadratic_section
    ρ K A hZ hgen hA hq hc hAC hn
  let σ := N.quotientRepresentation
  let : Finite (U ⧸ N.toSubmodule) := Module.finite_of_finite (ZMod 2)
  have hsurvive : ¬ K ≤ (actionHom σ).ker := fun hh => hnσ
    (fun k hk => LinearMap.ext ((actionHom_eq_one_iff σ k).mp (hh hk)))
  have hsaturated : fixedCodim N.quotientRepresentation A = 2 * rank A :=
    component_irreducible_codim σ K A hm eK hs hquot hi hsurvive hA hqσ hcσ hAC
  have hU := fixedCodim_subrepresentation_le ρ U A
  have hN := fixedCodim_quotient_add_subrepresentation_le U.toRepresentation N A
  rw [hsaturated] at hN
  have hNzero : fixedCodim N.toRepresentation A = 0 := by omega
  have hUeq : fixedCodim U.toRepresentation A = fixedCodim ρ A := by omega
  have hNA : A ≤ N.toRepresentation.ker := by
    intro a ha
    apply LinearMap.ext
    intro v
    exact ((fixedCodim_eq_zero_iff N.toRepresentation A).mp hNzero).ge
      (Submodule.mem_top (x := v)) ⟨a,ha⟩
  have hNK := simple_normal_le_ker_of_actor_le_ker N.toRepresentation K A hAC hA.1 hNA
  have hUA := quotient_trivial_of_sup_fixedSpace ρ U A
    ((fixedCodim_subrepresentation_eq_iff ρ U A).mp hUeq)
  have hUK := simple_normal_le_ker_of_actor_le_ker U.quotientRepresentation K A hAC hA.1
    (fun a ha => LinearMap.ext (hUA a ha))
  have hmove : subspaceCommutator ρ ⊤ K ≤ U.toSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k,hk,v,_,rfl⟩
    exact (Submodule.Quotient.eq U.toSubmodule).mp
      (LinearMap.congr_fun (hUK hk) (U.toSubmodule.mkQ v))
  have hfaith : Function.Injective (σ.comp K.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rcases (σ.comp K.subtype).normal_ker.eq_bot_or_eq_top with he | he
    · exact he
    · exact (hnσ (fun k hk =>
        (show (⟨k,hk⟩ : K) ∈ (σ.comp K.subtype).ker from he.symm ▸ mem_top _))).elim
  have hI : IsIrrPlus ρ K (subspaceCommutator ρ ⊤ K) := by
    apply moved_irrPlus_of_central_image ρ σ K U hmove N.toSubmodule.mkQ
      N.toSubmodule.mkQ_surjective (fun _ _ => rfl) _ hi hfaith
    intro v hv k
    have hvN : v ∈ N.toSubmodule := (Submodule.Quotient.mk_eq_zero _).mp hv
    exact congrArg Subtype.val (LinearMap.congr_fun (hNK k.property) ⟨v,hvN⟩)
  have hstable : (⊤ : Subgroup D) ≤ subspaceStabilizer ρ (subspaceCommutator ρ ⊤ K) :=
    subspaceCommutator_invariant_normalizer ρ (le_subspaceStabilizer ρ ⊤ (by simp))
      le_normalizer_of_normal
  exact invariant_natural_section ρ K hm eK hs hquot _ hI hstable A hA hq hc
    (disjoint_iff.mpr hAC)

/-- Recognition for a normal Suzuki component and any faithful quadratic actor. -/
theorem natural_moved_of_quadratic_actor
    (ρ : Representation (ZMod 2) D V) (K A : Subgroup D)
    [K.Normal] [IsQuasisimple K]
    {m : ℕ} (hm : 0 < m) (eK : K ≃* SuzukiMatrixGroup m)
    (hs : IsSQTK KnownSimple.IsKnownSimple D)
    (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hc : fixedCodim ρ A ≤ 2 * rank A)
    (hAC : A ⊓ centralizer (K : Set D) = ⊥) (hn : ¬ K ≤ ρ.ker) :
    Nonempty (ActionEquiv (centralQuotientRepresentation ρ K
      (subspaceCommutator ρ ⊤ K) (subspaceCommutator_invariant ρ ⊤ K)) (natural m)) := by
  let E := K ⊔ A
  let L := K.subgroupOf E
  let f : L ≃* K := subgroupOfEquivOfLe (show K ≤ E from le_sup_left)
  let : IsQuasisimple L :=
    Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Normal.componentInSup_quasisimple K A
  have hn' : ¬ L ≤ (ρ.comp E.subtype).ker := by
    intro hh
    apply hn
    intro k hk
    exact hh (show (⟨k,(le_sup_left : K ≤ E) hk⟩ : E) ∈ L from hk)
  have hmove : subspaceCommutator (ρ.comp E.subtype) ⊤ L = subspaceCommutator ρ ⊤ K := by
    unfold subspaceCommutator
    congr 1
    ext v
    constructor
    · rintro ⟨k,hk,w,hw,rfl⟩
      exact ⟨k,hk,w,hw,rfl⟩
    · rintro ⟨k,hk,w,hw,rfl⟩
      exact ⟨⟨k,(le_sup_left : K ≤ E) hk⟩,hk,w,hw,rfl⟩
  obtain ⟨a⟩ := natural_moved_of_quadratic_supplement (ρ.comp E.subtype) L (A.subgroupOf E)
    (Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Normal.componentInSup_generated K A)
    hm (f.trans eK) (hs.subgroup E)
    (Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Normal.actorInSup_elementary K A hA)
    (Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Normal.actorInSup_quadratic ρ K A hq)
    (Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Normal.actorInSup_bound ρ K A hc)
    (Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Normal.actorInSup_faithful K A hAC) hn'
  have changeSpace (W I : Submodule (ZMod 2) V)
      (hW : L ≤ subspaceStabilizer (ρ.comp E.subtype) W)
      (hI : L ≤ subspaceStabilizer (ρ.comp E.subtype) I) (he : W = I) :
      Nonempty (ActionEquiv (centralQuotientRepresentation (ρ.comp E.subtype) L W hW) (natural m)) →
      Nonempty (ActionEquiv (centralQuotientRepresentation (ρ.comp E.subtype) L I hI) (natural m)) := by
    subst I
    exact id
  obtain ⟨a⟩ := changeSpace _ _ _
    (hmove ▸ subspaceCommutator_invariant (ρ.comp E.subtype) ⊤ L) hmove ⟨a⟩
  let q := subgroupCentralQuotientEquiv ρ K E (show K ≤ E from le_sup_left)
    (subspaceCommutator ρ ⊤ K)
  have hqact (k : K) (v : centralQuotient (ρ.comp E.subtype) L (subspaceCommutator ρ ⊤ K)) :
      q (centralQuotientRepresentation (ρ.comp E.subtype) L _
        (hmove ▸ subspaceCommutator_invariant (ρ.comp E.subtype) ⊤ L) (f.symm k) v) =
      centralQuotientRepresentation ρ K _ (subspaceCommutator_invariant ρ ⊤ K) k (q v) := by
    induction v using Submodule.Quotient.induction_on with | _ v => rfl
  refine ⟨⟨f.symm.trans a.groupEquiv,q.symm.trans a.linearEquiv,?_⟩⟩
  intro k v
  obtain ⟨v,rfl⟩ := q.surjective v
  change a.linearEquiv (q.symm (centralQuotientRepresentation ρ K _
    (subspaceCommutator_invariant ρ ⊤ K) k (q v))) =
    natural m (a.groupEquiv (f.symm k)) (a.linearEquiv (q.symm (q v)))
  rw [← hqact,q.symm_apply_apply,q.symm_apply_apply]
  exact a.intertwines (f.symm k) v

end CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.SourceRecognition

end
