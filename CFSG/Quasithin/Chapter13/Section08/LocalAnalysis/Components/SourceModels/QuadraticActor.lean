module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.SourceModels.SmallRatio
public import Theory.Representation.BinaryOffender.QuadraticComponentSection
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.ActionImage.Structure
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalModule.Normal.Restriction

public import Theory.Representation.BinaryOffender.CubicCenterChief
public import Theory.Representation.NormalInvariants

/-!
# Normal components with a small quadratic actor

For a centerless quasisimple normal component, pass to a component-irreducible
section on which the quadratic actor remains faithful. For a component with
center of order three, first choose a chief factor faithful on the component;
quadratic orbit independence forces its restriction to the component to be
irreducible. In both cases the actual faithful image has generalized Fitting
subgroup isomorphic to the original component. The completed B.4 small-ratio
classification therefore supplies the central-quotient models, the Mathieu
alternatives, and the exclusion of the triple cover of A7.

Source: Aschbacher--Smith, F.9.18(4), printed pp.325--326, using B.4.2--5
and the component-preserving reduction of D.3.6--10, pp.196--201.
The literal Chapter 13 application is in `SourceModels.Normal`.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.Components.SourceModels
open Models
open Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions
open Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
open Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Normal
open ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.ActionImage.Structure
universe u
variable {D V : Type u} [Group D] [Finite D]
  [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem f918Models_of_centerless_quadratic_supplement
    (ρ : Representation (ZMod 2) D V) (K A : Subgroup D)
    [K.Normal] [IsQuasisimple K] (hZ : center K = ⊥) (hgen : K ⊔ A = ⊤)
    (hs : IsSQTK KnownSimple.IsKnownSimple D)
    (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hc : fixedCodim ρ A ≤ 2 * rank A)
    (hAC : A ⊓ centralizer (K : Set D) = ⊥) (hn : ¬ K ≤ ρ.ker) :
    F918Models K := by
  let : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  obtain ⟨U,N,hi,hn,hq,hc⟩ := exists_component_irreducible_quadratic_section
    ρ K A hZ hgen hA hq hc hAC hn
  let : Finite (U ⧸ N.toSubmodule) := Module.finite_of_finite (ZMod 2)
  let σ := N.quotientRepresentation
  have hsurvive : ¬ K ≤ (actionHom σ).ker := by
    intro h
    apply hn
    intro k hk
    rw [MonoidHom.mem_ker]
    apply LinearMap.ext
    intro v
    exact (actionHom_eq_one_iff σ k).mp (h hk) v
  have hfaith := faithful_on_section_of_central_kernel σ K A hAC
    (central_kernel_of_quasisimple σ K (by
      intro h
      apply hn
      intro k hk
      rw [MonoidHom.mem_ker]
      apply LinearMap.ext
      intro v
      exact h k hk v))
  have hbound : quadraticRatio (imageRepresentation σ) ≤ 2 := by
    apply (quadraticRatio_le_two_iff _).mpr
    refine ⟨actionSubgroup σ A,hA.actionSubgroup σ hfaith,
      quadratic_actionSubgroup σ hq,?_⟩
    rw [fixedCodim_actionSubgroup,actionSubgroup_rank σ A hfaith]
    exact hc
  let := hA.2
  have hquot : IsPGroup 2 (D ⧸ K) :=
    isPGroup_quotient_of_sup_eq_top K A (IsElementaryAbelian.isPGroup 2 A) hgen
  obtain ⟨hqs,hirr,hfit⟩ := image_structure σ K hsurvive hquot hi
  have hyp : B4Hypotheses KnownSimple.IsKnownSimple (imageRepresentation σ) := by
    refine ⟨image_sqtk σ K hsurvive hs hquot hZ,imageRepresentation_injective σ,?_,?_⟩
    · rw [hfit]
      exact hqs
    · rw [hfit]
      exact hirr
  let e : K ≃* generalizedFitting (actionImage σ) :=
    (componentEquiv σ K hsurvive hZ).trans (MulEquiv.subgroupCongr hfit.symm)
  exact f918Models_transport e (f918Models_of_small_quadratic (imageRepresentation σ) hyp hbound)

theorem f918Models_of_centerless_quadratic_actor
    (ρ : Representation (ZMod 2) D V) (K A : Subgroup D)
    [K.Normal] [IsQuasisimple K] (hZ : center K = ⊥)
    (hs : IsSQTK KnownSimple.IsKnownSimple D)
    (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hc : fixedCodim ρ A ≤ 2 * rank A)
    (hAC : A ⊓ centralizer (K : Set D) = ⊥) (hn : ¬ K ≤ ρ.ker) :
    F918Models K := by
  let : IsQuasisimple (K.subgroupOf (K ⊔ A)) := componentInSup_quasisimple K A
  apply f918Models_transport (componentInSupEquiv K A).symm
  apply f918Models_of_centerless_quadratic_supplement
    (ρ.comp (K ⊔ A).subtype) (K.subgroupOf (K ⊔ A)) (A.subgroupOf (K ⊔ A))
    (componentInSup_center K A hZ) (componentInSup_generated K A)
    (hs.subgroup (K ⊔ A)) (actorInSup_elementary K A hA)
    (actorInSup_quadratic ρ K A hq) (actorInSup_bound ρ K A hc)
    (actorInSup_faithful K A hAC)
  intro h
  apply hn
  intro k hk
  exact h (show (⟨k,(le_sup_left : K ≤ K ⊔ A) hk⟩ : ↥(K ⊔ A)) ∈
    K.subgroupOf (K ⊔ A) from hk)

omit [Finite V] in
private theorem constituent_faithful_of_restriction
    (ρ : Representation (ZMod 2) D V) (K : Subgroup D)
    [K.Normal] [IsQuasisimple K] (hi : IsIrreducible ρ)
    (hf : Function.Injective (ρ.comp K.subtype)) (hc : Nat.card (center K) = 3)
    (W : Subrepresentation (ρ.comp K.subtype)) (hW : W ≠ ⊥) :
    Function.Injective W.toRepresentation := by
  let := hi
  have hWsub : W.toSubmodule ≠ ⊥ := fun he => hW (Subrepresentation.toSubmodule_injective he)
  have hnormal (N : Subgroup D) [N.Normal] (hNK : N ≤ K)
      (hfix : W.toSubmodule ≤ fixedSpace ρ N) : N = ⊥ := by
    have hn : Representation.invariants (ρ.comp N.subtype) ≠ ⊥ := by
      intro hz
      exact hWsub (bot_unique (hfix.trans_eq hz))
    have hnker := le_ker_of_normal_invariants_ne_bot ρ N hn
    apply bot_unique
    intro n hn
    apply mem_bot.mpr
    exact congrArg Subtype.val (hf (show (ρ.comp K.subtype) ⟨n,hNK hn⟩ =
      (ρ.comp K.subtype) 1 from (hnker hn).trans (map_one _).symm))
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rcases IsQuasisimple.normal_le_center_or_eq_top W.toRepresentation.ker with hk | hk
  · have hd : Nat.card W.toRepresentation.ker ∣ 3 := hc ▸ card_dvd_of_le hk
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · exact Subgroup.card_eq_one.mp h1
    have hker : W.toRepresentation.ker = center K := eq_of_le_of_card_ge hk (by omega)
    let Z := (center K).map K.subtype
    let : Z.Normal := ConjAct.normal_of_characteristic_of_normal
    have hZ : Z = ⊥ := hnormal Z (map_subtype_le _) (by
      intro v hv
      rintro ⟨_,z,hz,rfl⟩
      have hm : z ∈ W.toRepresentation.ker := hker.symm ▸ hz
      exact congrArg Subtype.val (LinearMap.congr_fun hm (⟨v,hv⟩ : W)))
    have hz : center K = ⊥ := (map_eq_bot_iff_of_injective _ K.subtype_injective).mp hZ
    rw [hz,card_bot] at hc
    omega
  · have hK : K = ⊥ := hnormal K le_rfl (by
      intro v hv k
      have hm : k ∈ W.toRepresentation.ker := hk.symm ▸ mem_top k
      exact congrArg Subtype.val (LinearMap.congr_fun hm (⟨v,hv⟩ : W)))
    let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
    let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
    exact ((nontrivial_iff_ne_bot K).mp inferInstance hK).elim

private theorem component_irreducible_of_cubic_center
    (ρ : Representation (ZMod 2) D V) (K A : Subgroup D)
    [K.Normal] [IsQuasisimple K] (hcenter : Nat.card (center K) = 3)
    (hf : Function.Injective (ρ.comp K.subtype)) (hi : IsIrreducible ρ)
    (hgen : K ⊔ A = ⊤) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hc : fixedCodim ρ A ≤ 2 * rank A)
    (hAC : A ⊓ centralizer (K : Set D) = ⊥) : IsIrreducible (ρ.comp K.subtype) := by
  let : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  have hn : ¬ (⊤ : Submodule (ZMod 2) V) ≤ fixedSpace ρ K := by
    intro hh
    obtain ⟨k,hk⟩ := exists_ne (1 : K)
    apply hk
    apply hf
    apply LinearMap.ext
    intro v
    simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, Subgroup.coe_one, map_one, Module.End.one_apply]
      using hh (show v ∈ (⊤ : Submodule (ZMod 2) V) from Submodule.mem_top) k
  let C : Subrepresentation ρ :=
    ⟨fixedSpace ρ K, fun g v hv => (fixedSpace_stable_of_normal ρ K (mem_top g) v).2 hv⟩
  have hfix : fixedSpace ρ K = ⊥ := by
    rcases hi.eq_bot_or_eq_top C with hb | ht
    · exact congrArg Subrepresentation.toSubmodule hb
    · exact (hn (congrArg Subrepresentation.toSubmodule ht).ge).elim
  obtain ⟨J,hJ⟩ := exists_isIrrPlus_of_not_fixed ρ K hn
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨I,_,hI⟩ := Homogeneous.exists_isIrrPlusWith_le_orbitSpan ρ
    (show A ≤ normalizer (K : Set D) from le_normalizer_of_normal)
    (IsElementaryAbelian.isPGroup 2 A) hJ
  have hfaith := constituent_faithful_of_restriction ρ K hi hf hcenter
    (invariantSubspace ρ K I hI.invariant) (by
      intro he
      exact hI.isIrrPlus.ne_bot ρ (congrArg Subrepresentation.toSubmodule he))
  have hfaithI : ∀ k ∈ K, (∀ v ∈ I, ρ k v = v) → k = 1 := by
    intro k hk hh
    exact congrArg Subtype.val (hfaith (show
      (invariantSubspace ρ K I hI.invariant).toRepresentation ⟨k,hk⟩ =
        (invariantSubspace ρ K I hI.invariant).toRepresentation 1 from by
      apply LinearMap.ext
      intro v
      simpa only [map_one, Module.End.one_apply] using (Subtype.ext (hh v v.property) :
        (invariantSubspace ρ K I hI.invariant).toRepresentation ⟨k,hk⟩ v = v)))
  have hfa := actor_faithful_on_section ρ K A I hI.invariant hfaithI hI.normalizes hAC
  have hs := hI.quadratic_stabilizes ρ hfix hA hq hfa
    (hI.isIrrPlus.finrank_gt_two ρ K) hc
  let S : Subrepresentation ρ := ⟨I, by
    intro g v hv
    have hg : g ∈ K ⊔ A := hgen ▸ mem_top g
    exact ((sup_le hI.invariant hs) hg v).2 hv⟩
  have hItop : I = ⊤ := by
    rcases hi.eq_bot_or_eq_top S with hb | ht
    · exact (hI.isIrrPlus.ne_bot ρ (congrArg Subrepresentation.toSubmodule hb)).elim
    · exact congrArg Subrepresentation.toSubmodule ht
  exact component_irreducible_of_top_isIrrPlus ρ K (hItop ▸ hI.isIrrPlus) hfix

private theorem models_of_faithful_component_image
    (ρ : Representation (ZMod 2) D V) (K A : Subgroup D)
    [K.Normal] [IsQuasisimple K]
    (hf : Function.Injective (ρ.comp K.subtype))
    (hi : IsIrreducible (ρ.comp K.subtype))
    (hs : IsSQTK KnownSimple.IsKnownSimple D) (hquot : IsPGroup 2 (D ⧸ K))
    (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hc : fixedCodim ρ A ≤ 2 * rank A)
    (hAC : A ⊓ centralizer (K : Set D) = ⊥) : F918Models K := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  have hn : ¬ K ≤ (actionHom ρ).ker := by
    intro hh
    obtain ⟨k,hk⟩ := exists_ne (1 : K)
    apply hk
    apply hf
    apply LinearMap.ext
    intro v
    simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, Subgroup.coe_one, map_one, Module.End.one_apply]
      using (actionHom_eq_one_iff ρ k).mp (hh k.property) v
  have hinj : Function.Injective (componentMap ρ K) := by
    intro x y he
    apply hf
    exact congrArg (imageRepresentation ρ) (congrArg Subtype.val he)
  let e₀ : K ≃* actionSubgroup ρ K :=
    MulEquiv.ofBijective _ ⟨hinj,componentMap_surjective ρ K⟩
  have hk2 : IsPGroup 2 (actionHom ρ).ker := by
    apply hquot.of_injective ((QuotientGroup.mk' K).comp (actionHom ρ).ker.subtype)
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    apply mem_bot.mpr
    apply Subtype.ext
    have hxK : (x : D) ∈ K := (QuotientGroup.eq_one_iff _).mp hx
    change (x : D) = 1
    exact congrArg (fun k : K => (k : D)) (hinj (show componentMap ρ K ⟨x,hxK⟩ =
      componentMap ρ K 1 from Subtype.ext (x.property.trans (map_one _).symm)))
  have hsq : IsSQTK KnownSimple.IsKnownSimple (actionImage ρ) := by
    apply (IsSQTK.equiv (QuotientGroup.quotientKerEquivOfSurjective (actionHom ρ)
      ρ.asGroupHom.rangeRestrict_surjective)).mp
    refine ⟨?_,hs.isKGroup.quotient (actionHom ρ).ker⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (actionHom ρ).ker hk2).trans
      (hs.stronglyQuasithin p hp ho)
  have hfaith := faithful_on_section_of_central_kernel ρ K A hAC
    (central_kernel_of_quasisimple ρ K (by
      intro hh
      apply hn
      intro k hk
      exact (actionHom_eq_one_iff ρ k).mpr (hh k hk)))
  have hbound : quadraticRatio (imageRepresentation ρ) ≤ 2 := by
    apply (quadraticRatio_le_two_iff _).mpr
    refine ⟨actionSubgroup ρ A,hA.actionSubgroup ρ hfaith,
      quadratic_actionSubgroup ρ hq,?_⟩
    rw [fixedCodim_actionSubgroup,actionSubgroup_rank ρ A hfaith]
    exact hc
  obtain ⟨hqs,hirr,hfit⟩ := image_structure ρ K hn hquot hi
  have hyp : B4Hypotheses KnownSimple.IsKnownSimple (imageRepresentation ρ) := by
    refine ⟨hsq,imageRepresentation_injective ρ,?_,?_⟩
    · rw [hfit]
      exact hqs
    · rw [hfit]
      exact hirr
  exact f918Models_transport (e₀.trans (MulEquiv.subgroupCongr hfit.symm))
    (f918Models_of_small_quadratic (imageRepresentation ρ) hyp hbound)

theorem f918Models_of_cubic_center_quadratic_supplement
    (ρ : Representation (ZMod 2) D V) (K A : Subgroup D)
    [K.Normal] [IsQuasisimple K] (hcenter : Nat.card (center K) = 3)
    (hf : Function.Injective ρ) (hgen : K ⊔ A = ⊤)
    (hs : IsSQTK KnownSimple.IsKnownSimple D)
    (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hc : fixedCodim ρ A ≤ 2 * rank A)
    (hAC : A ⊓ centralizer (K : Set D) = ⊥) : F918Models K := by
  let : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  obtain ⟨U,N,hi,hfK⟩ := exists_faithful_chief_of_cubic_center ρ K hf hcenter
  let σ := sectionRepresentation ρ U N
  let : Finite (N ⧸ (sectionLower ρ U N).toSubmodule) := Module.finite_of_finite (ZMod 2)
  have hq' := quadratic_section ρ U N hq
  have hc' := (fixedCodim_section_le ρ U N A).trans hc
  have hiK := component_irreducible_of_cubic_center σ K A hcenter hfK hi hgen hA hq' hc' hAC
  let := hA.2
  exact models_of_faithful_component_image σ K A hfK hiK hs
    (isPGroup_quotient_of_sup_eq_top K A (IsElementaryAbelian.isPGroup 2 A) hgen)
    hA hq' hc' hAC

theorem f918Models_of_quadratic_actor
    (ρ : Representation (ZMod 2) D V) (K A : Subgroup D)
    [K.Normal] [IsQuasisimple K] (hf : Function.Injective ρ)
    (hcenter : Nat.card (center K) = 1 ∨ Nat.card (center K) = 3)
    (hs : IsSQTK KnownSimple.IsKnownSimple D)
    (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hc : fixedCodim ρ A ≤ 2 * rank A)
    (hAC : A ⊓ centralizer (K : Set D) = ⊥) : F918Models K := by
  rcases hcenter with hz | hz
  · apply f918Models_of_centerless_quadratic_actor ρ K A (Subgroup.card_eq_one.mp hz)
      hs hA hq hc hAC
    intro hh
    let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
    let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
    apply (nontrivial_iff_ne_bot K).mp inferInstance
    exact bot_unique (hh.trans ((MonoidHom.ker_eq_bot_iff _).mpr hf).le)
  · let : IsQuasisimple (K.subgroupOf (K ⊔ A)) := componentInSup_quasisimple K A
    apply f918Models_transport (componentInSupEquiv K A).symm
    have hz' : Nat.card (center (K.subgroupOf (K ⊔ A))) = 3 :=
      (Nat.card_congr (centerCongr (componentInSupEquiv K A)).toEquiv).trans hz
    exact f918Models_of_cubic_center_quadratic_supplement
      (ρ.comp (K ⊔ A).subtype) (K.subgroupOf (K ⊔ A)) (A.subgroupOf (K ⊔ A))
      hz' (hf.comp (K ⊔ A).subtype_injective) (componentInSup_generated K A)
      (hs.subgroup (K ⊔ A)) (actorInSup_elementary K A hA)
      (actorInSup_quadratic ρ K A hq) (actorInSup_bound ρ K A hc)
      (actorInSup_faithful K A hAC)


end CFSG.Quasithin.Chapter13.Section08.Components.SourceModels
