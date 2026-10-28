module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.SourceModels.QuadraticActor
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.SourceModels.Nonnormal
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalModule.Exchanged.PreservingModule
public import CFSG.Quasithin.ChapterB.Section01.ComponentNormalization.MarkedModel
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.OddRank.CoreNormalization.Models
public import Theory.Representation.CliffordSubquotient

/-!
# The model restriction for an exchanged component

The index-two normalizer gives the literal pair orbit. If the quadratic
actor moves a component, the genuine quadratic four-group theorem supplies
an actual binary PSL2 isomorphism. If it preserves the component, choose
an irreducible section detecting that perfect component. Clifford restriction
and a minimum-ratio subactor give a component-irreducible faithful image.
The Chapter K odd-linear and J1 exclusions reduce A.3.8's earlier model list
to binary PSL2, Suzuki, and PSL3(2). The PSL2(5) endpoint is identified with
PSL2(4) by the actual exceptional isomorphism.

No component model or module marking is assumed beyond the genuine A.3.8
list. `SourceModels.OriginalNonnormal` supplies that list, the pair orbit,
and the quadratic actor from the original Chapter 13 source hypotheses.

Source: Aschbacher--Smith, F.9.18(5), pp.325--326; D.3.6--7, pp.196--199;
A.3.8(3), pp.45--46; Chapter K, pp.451--460.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.Components.SourceModels
open Chapter1.Section02
open Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
open Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule
open Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged
open ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.ActionImage.Structure
open Representation.BinaryOffender.Homogeneous
universe u

/-- The actual group models in F.9.18(5); PSL2(4) includes A5. -/
@[expose] def NonnormalF918Models (X : Type*) [Group X] : Prop :=
  (∃ n, 2 ≤ n ∧ ClassicalGroup.IsPSL X 2 (2 ^ n)) ∨
  (∃ m, 1 ≤ m ∧ Nonempty (X ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) ∨
  ClassicalGroup.IsPSL X 3 2

theorem NonnormalF918Models.transport {X Y : Type*} [Group X] [Group Y]
    (h : NonnormalF918Models Y) (e : X ≃* Y) : NonnormalF918Models X := by
  rcases h with ⟨n,hn,hm⟩ | ⟨m,hm,he⟩ | hm
  · exact Or.inl ⟨n,hn,hm.of_mulEquiv e⟩
  · exact Or.inr (Or.inl ⟨m,hm,he.map (e.trans ·)⟩)
  · exact Or.inr (Or.inr (hm.of_mulEquiv e))

variable {D V : Type u} [Group D] [Finite D]
  [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem nonnormal_models_of_small_quadratic
    (ρ : Representation (ZMod 2) D V)
    (h : B4Hypotheses KnownSimple.IsKnownSimple ρ)
    (hq : quadraticRatio ρ ≤ 2)
    (hm : NonnormalCComponentModel (generalizedFitting D)) :
    NonnormalF918Models (generalizedFitting D) := by
  let : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  let : IsQuasisimple (generalizedFitting D) := h.quasisimple
  let : IsSimpleGroup ((generalizedFitting D) ⧸ center (generalizedFitting D)) := IsQuasisimple.simple
  let : Nontrivial (generalizedFitting D) :=
    (QuotientGroup.mk'_surjective (center (generalizedFitting D))).nontrivial
  have hz := Chapter15.Section03.ComponentIntersection.CoreNormalization.nonnormalModel_center_eq_bot
    hm (Group.IsPerfect.not_isSolvable (generalizedFitting D))
  let e : ((generalizedFitting D) ⧸ center (generalizedFitting D)) ≃* generalizedFitting D :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
  have hs : ChapterK.RankOne.SourceHypotheses ρ (generalizedFitting D) :=
    ⟨h.sqtk,rfl,h.quasisimple,h.faithful,h.irreducible,
      (Representation.BinaryOffender.cubicRatio_le_quadraticRatio ρ).trans hq⟩
  cases hm with
  | linear_even n hn hm => exact Or.inl ⟨n,hn,hm⟩
  | suzuki m hm he => exact Or.inr (Or.inl ⟨m,hm,he⟩)
  | linear_prime p hp ho hm =>
    have hmq : ClassicalGroup.IsPSL ((generalizedFitting D) ⧸ center (generalizedFitting D))
        2 (p ^ 1) := by simpa only [pow_one] using hm.of_mulEquiv e
    have he := Chapter7.NormalizedSource.NonMathieuFamily.odd_linear_two_parameters hs hp ho
      (by decide : 1 ≤ 2) hmq
    simp only [pow_one] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact Or.inl ⟨2,by decide,GaloisField 2 2,inferInstance,inferInstance,
        GaloisField.card 2 2 (by decide),ChapterK.OddCharacteristic.psl2Four_of_psl2_five hm⟩
    · exact Or.inr (Or.inr ⟨ZMod 2,inferInstance,inferInstance,by norm_num,
        ChapterK.OddCharacteristic.psl3Two_of_psl2_seven hm⟩)
    · norm_num at hp
    · norm_num at hp
  | janko he =>
    exact (ChapterK.SporadicCatalogue.sourceExclusion_j1 ρ
      ⟨h.sqtk,h.quasisimple,h.faithful,h.irreducible,hs.smallCubic⟩
      (he.map (e.trans ·))).elim

theorem nonnormal_models_of_stable_constituent
    (ρ : Representation (ZMod 2) D V) {K C : Subgroup D} [IsQuasisimple K]
    (hZ : center K = ⊥) (hs : IsSQTK KnownSimple.IsKnownSimple D)
    (hm : NonnormalCComponentModel K)
    {I : Submodule (ZMod 2) V} (hI : Homogeneous.IsIrrPlusWith ρ K C I)
    [IsSemisimpleRepresentation (ρ.comp K.subtype)]
    (hC : C ∈ ChapterD.RPlusBound ρ 2) (hq : IsQuadratic ρ C)
    (hn : ¬ C ≤ centralizer (K : Set D)) : NonnormalF918Models K := by
  let : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  obtain ⟨hD,hbound⟩ := ChapterD.stable_section_image_bound ρ hI
    (hI.isIrrPlus.inf_fixedSpace_eq_bot_of_semisimple ρ) hZ hC hq hn
  let E := K ⊔ C
  let L := K.subgroupOf E
  let σ : Representation (ZMod 2) E I := (invariantSubspace ρ E I hD).toRepresentation
  let e : L ≃* K := subgroupOfEquivOfLe (show K ≤ E from le_sup_left)
  let : L.Normal := (normal_subgroupOf_iff_le_normalizer (show K ≤ E from le_sup_left)).mpr
    (sup_le K.le_normalizer hI.normalizes)
  let : IsQuasisimple L := Normal.componentInSup_quasisimple K C
  have hquot : IsPGroup 2 (E ⧸ L) := by
    let : IsElementaryAbelian 2 C := hC.1.1.2
    exact isPGroup_quotient_of_sup_eq_top L (C.subgroupOf E)
      (IsElementaryAbelian.isPGroup 2 C).comap_subtype (Normal.componentInSup_generated K C)
  have hi : IsIrreducible (σ.comp L.subtype) := by
    have hir := hI.isIrrPlus.irreducible_of_semisimple ρ
    let τ := (invariantSubspace ρ K I hI.invariant).toRepresentation
    have heq : σ.comp L.subtype = τ.comp e.toMonoidHom := rfl
    rw [heq]
    exact (irreducible_comp_surjective_iff e.toMonoidHom e.surjective τ).mpr hir
  have hsurvive : ¬ L ≤ (actionHom σ).ker := by
    intro hh
    apply hI.isIrrPlus.not_le_fixedSpace ρ
    intro v hv k
    exact congrArg Subtype.val ((actionHom_eq_one_iff σ (e.symm k)).mp
      (hh (e.symm k).property) (⟨v,hv⟩ : I))
  have hzL := Normal.componentInSup_center K C hZ
  obtain ⟨hqs,hirr,hfit⟩ := image_structure σ L hsurvive hquot hi
  have hyp : B4Hypotheses KnownSimple.IsKnownSimple (imageRepresentation σ) := by
    refine ⟨image_sqtk σ L hsurvive (hs.subgroup E) hquot hzL,
      imageRepresentation_injective σ,?_,?_⟩
    · rw [hfit]; exact hqs
    · rw [hfit]; exact hirr
  let iso : K ≃* generalizedFitting (actionImage σ) :=
    e.symm.trans ((componentEquiv σ L hsurvive hzL).trans (MulEquiv.subgroupCongr hfit.symm))
  exact (nonnormal_models_of_small_quadratic (imageRepresentation σ) hyp hbound
    (hm.of_mulEquiv iso.symm)).transport iso

theorem nonnormal_models_of_preserving_actor
    (ρ : Representation (ZMod 2) D V) {K K₀ T B C A : Subgroup D}
    (geo : ExchangedGeometry K K₀ T B C)
    (hK : IsComponent D K) (hZ : center K = ⊥)
    (hs : IsSQTK KnownSimple.IsKnownSimple D) (hm : NonnormalCComponentModel K)
    (hAT : A ≤ T) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hd : fixedCodim ρ A ≤ 2 * rank A)
    (hAC : A ⊓ centralizer (K₀ : Set D) = ⊥)
    (hp : A ≤ normalizer (K : Set D)) (hn : ¬ K ≤ ρ.ker) :
    NonnormalF918Models K := by
  let : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  let : IsQuasisimple K := hK.2
  obtain ⟨U,N,hi,hn⟩ := QuadraticFourGroup.exists_irreducible_section_surviving_perfect K hn
  let σ := N.quotientRepresentation
  let : Finite (U ⧸ N.toSubmodule) := Module.finite_of_finite (ZMod 2)
  have hqσ : IsQuadratic σ A := quadratic_of_equivariant_surjection U.toRepresentation σ
    N.toSubmodule.mkQ N.toSubmodule.mkQ_surjective (fun _ _ => rfl) A
      (quadratic_subrepresentation ρ U hq)
  have hdσ : fixedCodim σ A ≤ 2 * rank A := by
    change fixedCodim N.quotientRepresentation A ≤ 2 * rank A
    have hU := fixedCodim_subrepresentation_le ρ U A
    have hN := fixedCodim_quotient_add_subrepresentation_le U.toRepresentation N A
    omega
  let : IsIrreducible σ := hi
  let : IsSemisimpleRepresentation (σ.comp K.subtype) :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mpr
      (subnormal_restriction_semisimple σ K hK.1)
  obtain ⟨J,hJN,hnJ,hJ,hqJ⟩ := Exchanged.exists_minimal_actor_on_component σ geo
    hAT hA hqσ hdσ hAC hp
  have hnf : ¬ (⊤ : Submodule (ZMod 2) (U ⧸ N.toSubmodule)) ≤ fixedSpace σ K := by
    intro hh
    apply hn
    intro k hk
    rw [MonoidHom.mem_ker]
    apply LinearMap.ext
    intro v
    exact hh (Submodule.mem_top) ⟨k,hk⟩
  obtain ⟨I,hI⟩ := exists_isIrrPlus_of_not_fixed σ K hnf
  let : IsElementaryAbelian 2 J := hJ.1.1.2
  obtain ⟨I',_,hI'⟩ := exists_isIrrPlusWith_le_orbitSpan σ hJN
    (IsElementaryAbelian.isPGroup 2 J) hI
  exact nonnormal_models_of_stable_constituent σ hZ hs hm hI' hJ hqJ hnJ

theorem nonnormal_models_of_moving_actor
    (ρ : Representation (ZMod 2) D V) {K K₀ T B C A : Subgroup D}
    (geo : ExchangedGeometry K K₀ T B C)
    (hTK : T ≤ normalizer (K₀ : Set D))
    (hf : Function.Injective ρ) (hK : IsComponent D K) (hZ : center K = ⊥)
    [IsElementaryAbelian 2 A] (hAT : A ≤ T) (hq : IsQuadratic ρ A)
    (hAC : A ⊓ centralizer (K₀ : Set D) = ⊥)
    (hm : ¬ A ≤ normalizer (K : Set D)) (hd : fixedCodim ρ A ≤ 2 * rank A) :
    NonnormalF918Models K := by
  let : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : IsSimpleGroup K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  obtain ⟨F,a,hF,_⟩ := Exchanged.moving_fourGroup_of_small_ratio ρ geo hTK hf hK hAT hq hAC hm hd
  obtain ⟨M,f,hf,hker,_⟩ := ChapterB.ComponentNormalization.QuadraticSource.exists_marked_model hF
  have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff _).mp (hker.trans hZ)
  exact Or.inl ⟨M.n,by have := M.one_lt; omega,GaloisField 2 M.n,
    inferInstance,inferInstance,GaloisField.card 2 M.n (by have := M.one_lt; omega),
    ⟨MulEquiv.ofBijective f ⟨hinj,hf⟩⟩⟩

omit [Finite D] in
theorem exchanged_geometry_of_index_two (K T : Subgroup D) (hK : IsComponent D K)
    (hZ : center K = ⊥) (hindex : (normalizer (K : Set D)).index = 2)
    (hmoved : ¬ T ≤ normalizer (K : Set D)) :
    ExchangedGeometry K (componentOrbit K T) T ⊥ ⊥ := by
  have pair {t : D} (ht : t ∈ T) (hout : t ∉ normalizer (K : Set D)) :
      K ⊔ K.conjBy t⁻¹ = componentOrbit K T ∧
      Disjoint K (K.conjBy t⁻¹) ∧ K ≤ centralizer (K.conjBy t⁻¹ : Set D) := by
    have hi : K.conjBy t⁻¹ ≠ K := by
      intro he
      have hn := (normalizer (K : Set D)).inv_mem (mem_normalizer_iff_map_conj_eq.mpr he)
      exact hout (by simpa only [inv_inv] using hn)
    have hc : K ≤ centralizer (K.conjBy t⁻¹ : Set D) :=
      commutator_eq_bot_iff_le_centralizer.mp
        (hK.commutator_eq_bot_of_ne (hK.map_conj t⁻¹) hi.symm)
    refine ⟨?_,?_,hc⟩
    · apply le_antisymm
      · exact sup_le (le_componentOrbit K T)
          (le_iSup (fun s : T => K.map (MulAut.conj (s : D)).toMonoidHom) ⟨t⁻¹,T.inv_mem ht⟩)
      · apply iSup_le
        intro s
        rcases NormPair.conjugate_eq_or_eq_of_normalizer_index_two hindex hi s with he | he
        · rw [he]; exact le_sup_left
        · rw [he]; exact le_sup_right
    · rw [disjoint_iff_inf_le]
      intro k hk
      have hkz : (⟨k,hk.1⟩ : K) ∈ center K :=
        mem_center_iff.mpr (fun x => Subtype.ext (le_centralizer_iff.mp hc hk.2 x x.property))
      rw [hZ,mem_bot] at hkz
      exact mem_bot.mpr (congrArg Subtype.val hkz)
  obtain ⟨t,ht,hout⟩ := SetLike.not_le_iff_exists.mp hmoved
  have hp := pair ht hout
  refine ⟨le_componentOrbit K T,?_,bot_le,?_,⟨t,ht,hout⟩,?_⟩
  · rw [←hp.1]
    exact sup_le K.le_normalizer ((le_centralizer_iff.mp hp.2.2).trans (Subgroup.centralizer_le_normalizer _))
  · rw [normalizer_eq_top]; exact le_top
  · intro s hs hout
    obtain ⟨he,hd,hc⟩ := pair hs hout
    refine ⟨he,hd,hc,?_,?_⟩
    · exact rightConjugate_return_of_square ((normalizer (K : Set D)).sq_mem_of_index_two hindex s)
    · simp only [conjBy,Subgroup.map_bot,sup_bot_eq]

theorem nonnormal_models_of_quadratic_actor
    (ρ : Representation (ZMod 2) D V) (K T A : Subgroup D)
    (hK : IsComponent D K) (hs : IsSQTK KnownSimple.IsKnownSimple D)
    (hmodel : NonnormalCComponentModel K)
    (hindex : (normalizer (K : Set D)).index = 2)
    (hmove : ¬ T ≤ normalizer (K : Set D))
    (hf : Function.Injective ρ) (hAT : A ≤ T) (hA : IsElementaryTwo A)
    (hq : IsQuadratic ρ A) (hd : fixedCodim ρ A ≤ 2 * rank A)
    (hAC : A ⊓ centralizer (componentOrbit K T : Set D) = ⊥) :
    NonnormalF918Models K := by
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  have hZ := Chapter15.Section03.ComponentIntersection.CoreNormalization.nonnormalModel_center_eq_bot
    hmodel (Group.IsPerfect.not_isSolvable K)
  have geo := exchanged_geometry_of_index_two K T hK hZ hindex hmove
  by_cases hp : A ≤ normalizer (K : Set D)
  · apply nonnormal_models_of_preserving_actor ρ geo hK hZ hs hmodel hAT hA hq hd hAC hp
    intro hh
    exact (nontrivial_iff_ne_bot K).mp inferInstance
      (bot_unique (hh.trans ((MonoidHom.ker_eq_bot_iff _).mpr hf).le))
  · let : IsElementaryAbelian 2 A := hA.2
    exact nonnormal_models_of_moving_actor ρ geo (le_normalizer_componentOrbit K T)
      hf hK hZ hAT hq hAC hp hd

end CFSG.Quasithin.Chapter13.Section08.Components.SourceModels
