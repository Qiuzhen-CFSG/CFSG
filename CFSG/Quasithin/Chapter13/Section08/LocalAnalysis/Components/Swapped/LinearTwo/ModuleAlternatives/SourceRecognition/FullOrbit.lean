module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition.Constituents
public import CFSG.Quasithin.Chapter10.SourceA5MovedSeedModels
public import Theory.Representation.BinaryOffender.Homogeneous.QuotientOrbitModels
public import Theory.Representation.BinaryOffender.CubicRatio.MarkedNormalizer
public import Theory.Representation.AlternatingFiveMovedPair.NaturalEstimate
public import Theory.Representation.AlternatingFiveMovedPair.Mixed.NormalizerEstimate

/-!
# Whole Sylow orbits of the faithful field-four constituent

Choose a constituent homogeneous under the full Sylow supplement. Ambient
irreducibility makes its Sylow orbit span the whole module. Since both
component fixed spaces vanish, the constituent is faithful and its central
image is the same module. The intrinsic A₅-product classification leaves
natural tensors, mixed tensors, and the deleted square.

For a proper constituent, the two-type orbit theorem identifies the entire
module with the natural pair or mixed pair, whose full normalizers violate
the cubic bound of two. The deleted square is preserved by every product
automorphism and hence cannot have a proper homogeneous orbit. Thus the
constituent is already the whole module. All comparisons retain the actual
normal subgroup and the original vector space.

Source: Aschbacher–Smith, A.1.40–42, printed pp.31–32; D.3.5, pp.195–196;
the exchanged field-four branch of 13.8.16(1), pp.952–953.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.BinaryOffender.Homogeneous
open Representation.AlternatingFiveMovedPair
open scoped IsMulCommutative MonoidAlgebra
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition
open F918Sections.NoStrong
variable {D F U : Type*} [Group D] [Finite D] [Field F] [Finite F] [CharP F 2]
    (a : ExchangedActor KnownSimple.IsKnownSimple D F 2)
    [AddCommGroup U] [Module (ZMod 2) U]
    (σ : Representation (ZMod 2) D U)

/-- A faithful constituent homogeneous under the full Sylow supplement spans
the ambient irreducible module under that Sylow action. -/
theorem exists_full_sylow_constituent [FiniteDimensional (ZMod 2) U] [σ.IsIrreducible]
    (ha : fixedSpace σ a.component = ⊥) (hb : fixedSpace σ a.second = ⊥) :
    ∃ I : Submodule (ZMod 2) U, ∃ hI : IsIrrPlusWith σ a.orbit a.sylow I,
      orbitSpan σ a.sylow I = ⊤ ∧
      IsIrreducible (invariantSubspace σ a.orbit I hI.invariant).toRepresentation ∧
      Function.Injective (invariantSubspace σ a.orbit I hI.invariant).toRepresentation := by
  let : a.orbit.Normal := a.orbit_normal
  let : Nontrivial U := Subrepresentation.irreducible_module_nontrivial σ
  have hz : fixedSpace σ a.orbit = ⊥ := by
    apply bot_unique
    apply le_trans _ ha.le
    intro u hu c
    exact hu ⟨c,a.component_le c.property⟩
  have hn : ¬ (⊤ : Submodule (ZMod 2) U) ≤ fixedSpace σ a.orbit := by
    rw [hz]
    exact fun ht => top_ne_bot (le_antisymm ht bot_le)
  let : Group.IsPerfect a.orbit := by
    let : IsQuasisimple a.component := a.component_isComponent.2
    rw [a.orbit_eq]
    exact conjugateSpanBy_isPerfect _ _
  obtain ⟨J,hJ⟩ := exists_isIrrPlus_of_not_fixed σ a.orbit hn
  obtain ⟨I,_,hI⟩ := exists_isIrrPlusWith_le_orbitSpan σ
    (show (a.sylow : Subgroup D) ≤ normalizer (a.orbit : Set D) from le_normalizer_of_normal)
    a.sylow.isPGroup' hJ
  let R := orbitSubrepresentation σ hI.normalizes hI.isIrrPlus a.generated
  have hR : R = ⊤ := (eq_bot_or_eq_top R).resolve_left (fun he =>
    orbitSpan_ne_bot σ hI.isIrrPlus (congrArg Subrepresentation.toSubmodule he))
  have hsem : IsSemisimpleModule (ZMod 2)[a.orbit] (Representation.asModule (σ.comp a.orbit.subtype)) :=
    NormalConstituentDisplacement.restriction_semisimple σ inferInstance a.orbit
  let : IsSemisimpleRepresentation (σ.comp a.orbit.subtype) :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mpr hsem
  exact ⟨I,hI,congrArg Subrepresentation.toSubmodule hR,
    hI.isIrrPlus.irreducible_of_semisimple σ,
    faithful_on_component_invariant a σ ha hb I (hI.isIrrPlus.ne_bot σ) hI.invariant⟩

variable {P W : Type*} [Group P] [AddCommGroup W] [Module (ZMod 2) W]

/-- The zero central quotient identifies the actual constituent with its image. -/
def constituentCentralEquiv (N : Subgroup D) (hz : fixedSpace σ N = ⊥)
    (I : Submodule (ZMod 2) U) (hi : N ≤ subspaceStabilizer σ I) :
    (invariantSubspace σ N I hi).toRepresentation.Equiv
      (quotientImage σ N I hi).toRepresentation := by
  have hinj : Function.Injective (fixedSpace σ N).mkQ := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.ker_mkQ,hz]
  exact Representation.Equiv.mk (Submodule.equivMapOfInjective _ hinj I) (fun _ => rfl)

/-- A model of the central orbit identifies the entire module when its fixed
space vanishes and the original orbit spans. -/
def wholeCentralOrbitEquiv {N T : Subgroup D} {I : Submodule (ZMod 2) U}
    (hI : IsIrrPlusWith σ N T I) (hz : fixedSpace σ N = ⊥)
    (hspan : orbitSpan σ T I = ⊤) :
    Representation.Equiv (σ.comp N.subtype)
      (((centralTypeAction σ N T hI.normalizes).span
        (quotientImage σ N I hI.invariant)).toRepresentation) := by
  let S := (centralTypeAction σ N T hI.normalizes).span (quotientImage σ N I hI.invariant)
  have htop : S = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    rw [centralTypeAction_span]
    change centralOrbitSpan σ N T hI.normalizes (I.map (fixedSpace σ N).mkQ) = ⊤
    rw [←orbitSpan_quotientImage,hspan,Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _)
  let f : U →ₗ[ZMod 2] S.toSubmodule := (fixedSpace σ N).mkQ.codRestrict _ (by
    intro u
    rw [htop]
    trivial)
  have hf : Function.Bijective f := by
    constructor
    · intro u v he
      have hinj : Function.Injective (fixedSpace σ N).mkQ := by
        apply LinearMap.ker_eq_bot.mp
        rw [Submodule.ker_mkQ,hz]
      exact hinj (congrArg Subtype.val he)
    · intro v
      obtain ⟨u,hu⟩ := (fixedSpace σ N).mkQ_surjective v.val
      exact ⟨u,Subtype.ext hu⟩
  exact Representation.Equiv.mk (LinearEquiv.ofBijective f hf) (fun _ => rfl)

/-- Inflate a marked constituent model along the trivial group quotient. -/
def constituentModelInflation {N : Subgroup D} {I : Submodule (ZMod 2) U}
    (hi : N ≤ subspaceStabilizer σ I) (hz : fixedSpace σ N = ⊥)
    (e : N ≃* P) (μ : Representation (ZMod 2) P W)
    (b : Representation.Equiv (((invariantSubspace σ N I hi).toRepresentation).comp e.symm.toMonoidHom) μ) :
    (quotientImage σ N I hi).toRepresentation.Equiv
      (μ.comp ((QuotientGroup.quotientBot.trans e).toMonoidHom.comp (QuotientGroup.mk' ⊥))) := by
  let c := (constituentCentralEquiv σ N hz I hi).symm
  refine c.trans (Representation.Equiv.mk b.toLinearEquiv ?_)
  intro x
  apply LinearMap.ext
  intro v
  have h := Representation.IntertwiningMap.isIntertwining _ _ b.toIntertwiningMap (e x) v
  change b ((invariantSubspace σ N I hi).toRepresentation (e.symm (e x)) v) = μ (e x) (b v) at h
  change b ((invariantSubspace σ N I hi).toRepresentation x v) =
    μ (e (QuotientGroup.quotientBot (QuotientGroup.mk' ⊥ x))) (b v)
  have hq : QuotientGroup.quotientBot (QuotientGroup.mk' (⊥ : Subgroup N) x) = x :=
    QuotientGroup.kerLift_mk (MonoidHom.id N) x
  rw [hq]
  simpa only [e.symm_apply_apply] using h


local notation "Alt" => alternatingGroup (Fin 5)

omit [Finite D] in
/-- Automorphism invariance of the deleted square precludes a proper orbit. -/
theorem proper_constituent_not_deleted
    {N T : Subgroup D} {I : Submodule (ZMod 2) U}
    (hI : IsIrrPlusWith σ N T I) (hz : fixedSpace σ N = ⊥)
    (hspan : orbitSpan σ T I = ⊤) (hproper : I ≠ ⊤)
    (e : N ≃* (Alt × Alt)) :
    ¬ Nonempty (Representation.Equiv (((invariantSubspace σ N I hI.invariant).toRepresentation).comp
      e.symm.toMonoidHom) BinaryPermutation.FiveTensorSquare.deletedAction) := by
  rintro ⟨b⟩
  have hs : T ≤ subspaceStabilizer σ I := by
    intro t ht
    apply (subspace_map_eq_iff σ I t).mp
    apply hI.map_eq_of_quotient_model_twist σ ⟨t,ht⟩ ⊥
      (QuotientGroup.quotientBot.trans e) BinaryPermutation.FiveTensorSquare.deletedAction
      (constituentModelInflation σ hI.invariant hz e _ b)
    intro α
    obtain ⟨w,hw⟩ := BinaryPermutation.FiveTensorSquare.exists_wreath_intertwiner α
    exact ⟨BinaryPermutation.FiveTensorSquare.tensorWreathHom w,hw⟩
  exact hproper ((orbitSpan_eq_self σ hs).symm.trans hspan)

omit [Finite D] in
/-- The two natural types give exact coordinates on the whole moved orbit. -/
theorem proper_natural_whole_model
    {N T : Subgroup D} {I : Submodule (ZMod 2) U}
    (hI : IsIrrPlusWith σ N T I) (hz : fixedSpace σ N = ⊥)
    (hspan : orbitSpan σ T I = ⊤) (hproper : I ≠ ⊤)
    (e : N ≃* (Alt × Alt)) (base : Alt ≃* SL2FourNatural.SL) (c : Bool)
    (b : Representation.Equiv (((invariantSubspace σ N I hI.invariant).toRepresentation).comp
      e.symm.toMonoidHom)
      ((NaturalTypes.model c).comp (base.prodCongr base).toMonoidHom)) :
    Nonempty (Representation.Equiv (σ.comp N.subtype)
      (Natural.action.comp (e.trans (base.prodCongr base)).toMonoidHom)) := by
  let q := (QuotientGroup.quotientBot.trans e).trans (base.prodCongr base)
  let f := q.toMonoidHom.comp (QuotientGroup.mk' (⊥ : Subgroup N))
  let μ := NaturalTypes.model
  let b' : (quotientImage σ N I hI.invariant).toRepresentation.Equiv ((μ c).comp f) :=
    constituentModelInflation σ hI.invariant hz e _ b
  have hmoved : orbitSpan σ T I ≠ I := by rw [hspan]; exact Ne.symm hproper
  have htypes (α : MulAut (SL2FourNatural.SL × SL2FourNatural.SL)) :
      Nonempty (Representation.Equiv ((μ c).comp α.toMonoidHom) (μ c)) ∨
      Nonempty (Representation.Equiv ((μ c).comp α.toMonoidHom) (μ (!c))) := by
    obtain ⟨d,hd⟩ := NaturalTypes.model_automorphism_types α c
    cases c <;> cases d
    · exact Or.inl hd
    · exact Or.inr hd
    · exact Or.inr hd
    · exact Or.inl hd
  obtain ⟨a⟩ := hI.central_span_equiv_pair σ ⊥ q (μ c) (μ (!c)) b' hmoved htypes
  let z := (wholeCentralOrbitEquiv σ hI hz hspan).trans a
  cases c
  · exact ⟨z⟩
  · let flip : Representation.Equiv (((μ true).prod (μ false)).comp f)
        (Natural.action.comp f) := Representation.Equiv.mk
          (LinearEquiv.prodComm (ZMod 2) _ _) (fun _ => by ext v <;> rfl)
    exact ⟨z.trans flip⟩

omit [Finite D] in
/-- Either mixed orientation gives the same literal whole mixed-pair model. -/
theorem proper_mixed_whole_model
    {N T : Subgroup D} {I : Submodule (ZMod 2) U}
    (hI : IsIrrPlusWith σ N T I) (hz : fixedSpace σ N = ⊥)
    (hspan : orbitSpan σ T I = ⊤) (hproper : I ≠ ⊤)
    (e : N ≃* (Alt × Alt)) (base : Alt ≃* SL2FourNatural.SL)
    (hseed : Nonempty (Representation.Equiv (((invariantSubspace σ N I hI.invariant).toRepresentation).comp
        e.symm.toMonoidHom) (MixedTypes.firstSL.comp (base.prodCongr base).toMonoidHom)) ∨
      Nonempty (Representation.Equiv (((invariantSubspace σ N I hI.invariant).toRepresentation).comp
        e.symm.toMonoidHom) (MixedTypes.secondSL.comp (base.prodCongr base).toMonoidHom))) :
    Nonempty (Representation.Equiv (σ.comp N.subtype)
      (Mixed.action.comp (e.trans (base.prodCongr base)).toMonoidHom)) := by
  let q := QuotientGroup.quotientBot.trans e
  let f := q.toMonoidHom.comp (QuotientGroup.mk' (⊥ : Subgroup N))
  let τ₀ := MixedTypes.firstSL.comp (base.prodCongr base).toMonoidHom
  let τ₁ := MixedTypes.secondSL.comp (base.prodCongr base).toMonoidHom
  have hmoved : orbitSpan σ T I ≠ I := by rw [hspan]; exact Ne.symm hproper
  rcases hseed with hb | hb
  · obtain ⟨b⟩ := hb
    obtain ⟨a⟩ := hI.central_span_equiv_pair σ ⊥ q τ₀ τ₁
      (constituentModelInflation σ hI.invariant hz e _ b) hmoved (by
        intro α
        rcases MixedTypes.marked_model_automorphism_types base α with h | h
        · exact Or.inl h.1
        · exact Or.inr h.1)
    exact ⟨(wholeCentralOrbitEquiv σ hI hz hspan).trans a⟩
  · obtain ⟨b⟩ := hb
    obtain ⟨a⟩ := hI.central_span_equiv_pair σ ⊥ q τ₁ τ₀
      (constituentModelInflation σ hI.invariant hz e _ b) hmoved (by
        intro α
        rcases MixedTypes.marked_model_automorphism_types base α with h | h
        · exact Or.inl h.2
        · exact Or.inr h.2)
    let flip : Representation.Equiv ((Representation.prod τ₁ τ₀).comp f) ((Representation.prod τ₀ τ₁).comp f) :=
      Representation.Equiv.mk (LinearEquiv.prodComm (ZMod 2) _ _) (fun _ => by ext v <;> rfl)
    exact ⟨((wholeCentralOrbitEquiv σ hI hz hspan).trans a).trans flip⟩

/-- Strict normalizer estimates exclude every proper faithful homogeneous
constituent under the original cubic bound. -/
theorem homogeneous_constituent_eq_top [FiniteDimensional (ZMod 2) U]
    (hσ : Function.Injective σ) {N T : Subgroup D} [N.Normal]
    {I : Submodule (ZMod 2) U} (hI : IsIrrPlusWith σ N T I)
    (hz : fixedSpace σ N = ⊥) (hspan : orbitSpan σ T I = ⊤)
    [hirr : IsIrreducible (invariantSubspace σ N I hI.invariant).toRepresentation]
    (hfaith : Function.Injective (invariantSubspace σ N I hI.invariant).toRepresentation)
    (e : N ≃* (Alt × Alt)) (hc : cubicRatio σ ≤ 2) : I = ⊤ := by
  by_contra hproper
  let τ := ((invariantSubspace σ N I hI.invariant).toRepresentation).comp e.symm.toMonoidHom
  let : IsIrreducible τ := (irreducible_comp_surjective_iff e.symm.toMonoidHom
    e.symm.surjective _).mpr hirr
  have hf : Function.Injective τ := hfaith.comp e.symm.injective
  obtain ⟨g,hg⟩ := exists_ne (1 : Alt)
  have hl : ∃ g, τ (g,1) ≠ 1 := ⟨g,fun h => hg (congrArg Prod.fst (hf (h.trans (map_one τ).symm)))⟩
  have hr : ∃ g, τ (1,g) ≠ 1 := ⟨g,fun h => hg (congrArg Prod.snd (hf (h.trans (map_one τ).symm)))⟩
  let base := SL2FourNatural.alternatingFiveEquiv.symm
  let : N.subtype.range.Normal := by simpa only [range_subtype] using (inferInstance : N.Normal)
  rcases Chapter10.source_a5_product_module_alternatives_fixed_mixed_marking τ hl hr base with hn | hdn | hnd | hdd
  · obtain ⟨c,⟨b⟩,_⟩ := Chapter10.source_a5_cubicFree_marked_unique_type τ hn base
    obtain ⟨b⟩ := proper_natural_whole_model σ hI hz hspan hproper e base c b
    exact not_cubicRatio_le_of_marked_normal_range σ hσ N.subtype Natural.action
      (e.trans (base.prodCongr base)).toMonoidHom (e.trans (base.prodCongr base)).surjective
      b 2 Natural.normalizer_strict_cubic_bound hc
  · obtain ⟨b⟩ := proper_mixed_whole_model σ hI hz hspan hproper e base (Or.inr hdn)
    exact not_cubicRatio_le_of_marked_normal_range σ hσ N.subtype Mixed.action
      (e.trans (base.prodCongr base)).toMonoidHom (e.trans (base.prodCongr base)).surjective
      b 2 Mixed.normalizer_strict_cubic_bound hc
  · obtain ⟨b⟩ := proper_mixed_whole_model σ hI hz hspan hproper e base (Or.inl hnd)
    exact not_cubicRatio_le_of_marked_normal_range σ hσ N.subtype Mixed.action
      (e.trans (base.prodCongr base)).toMonoidHom (e.trans (base.prodCongr base)).surjective
      b 2 Mixed.normalizer_strict_cubic_bound hc
  · exact proper_constituent_not_deleted σ hI hz hspan hproper e hdd
end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition
