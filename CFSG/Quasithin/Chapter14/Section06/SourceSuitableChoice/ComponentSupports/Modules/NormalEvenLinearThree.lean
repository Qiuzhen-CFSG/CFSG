module
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.SourceQuadratic
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalModule.Normal.QuadraticModules

/-!
# Even-degree ternary linear constituents

Pass to the faithful image of a nontrivial irreducible component action.
The literal common quadratic actor supplies ratio at most two. The proved
Chapter K recognition then gives an actual natural SL₃ action over the same
defining field. Its scalar center is nontrivial in even binary degree, in
contradiction with the original centerless component. Odd-index traces carry
this irreducible exclusion through the original module's invariant extensions.

Classification/Sieve/LinearThree supplies the original terminal action and
Borel and applies this result to its generating seed. No action-recognition
or composition-factor premise is left in that source consumer.
Source: Aschbacher--Smith 14.6.20, p.1037, B.4.5 and K.3.2, pp.87,454--456.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.NormalEvenLinearThree
open ChapterB.QuasisimpleSource
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open OriginalModule.Normal RepresentationReduction
open RepresentationReduction.SourceRestrictions.Cases.Single.SmallRatio
open RepresentationReduction.SourceRestrictions
open RepresentationReduction.SourceRestrictions.FFExclusions.ModelRigidity
open Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.ActionImage.Structure
universe u
variable {D V : Type u} [Group D] [Finite D] [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) D V) (K : Subgroup D) [K.Normal] [IsQuasisimple K]

/-- Genuine natural recognition contradicts the scalar center in even defining degree. -/
theorem irreducible_component_false
    (hs : IsSQTK KnownSimple.IsKnownSimple D)
    (hquot : IsPGroup 2 (D ⧸ K)) (hZ : center K = ⊥)
    (hi : IsIrreducible (ρ.comp K.subtype))
    (hn : ¬ (⊤ : Submodule (ZMod 2) V) ≤ fixedSpace ρ K)
    (A : Subgroup D) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hc : fixedCodim ρ A ≤ 2 * rank A) (hAC : A ⊓ centralizer (K : Set D) = ⊥)
    {f : ℕ} (hf : 0 < f) (he : Even f)
    (hm : ClassicalGroup.IsPSL (K ⧸ center K) 3 (2 ^ f)) : False := by
  let : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  have hnact : ¬ ∀ k ∈ K, ∀ v, ρ k v = v := by
    intro h
    apply hn
    intro v _ k
    exact h k k.property v
  have hsurvive : ¬ K ≤ (actionHom ρ).ker := by
    intro h
    exact hnact (fun k hk v => (actionHom_eq_one_iff ρ k).mp (h hk) v)
  have hfaith := faithful_on_section_of_central_kernel ρ K A hAC
    (central_kernel_of_quasisimple ρ K hnact)
  have hbound : quadraticRatio (imageRepresentation ρ) ≤ 2 := by
    apply (quadraticRatio_le_two_iff _).mpr
    refine ⟨actionSubgroup ρ A,hA.actionSubgroup ρ hfaith,?_,?_⟩
    · rintro a ⟨x,hx,rfl⟩ b ⟨y,hy,rfl⟩ v
      exact hq x hx y hy v
    · rw [fixedCodim_actionSubgroup,actionSubgroup_rank ρ A hfaith]
      exact hc
  obtain ⟨hqs,hirr,hfit⟩ := image_structure ρ K hsurvive hquot hi
  let e : K ≃* generalizedFitting (actionImage ρ) :=
    (componentEquiv ρ K hsurvive hZ).trans (MulEquiv.subgroupCongr hfit.symm)
  have hyp : ChapterK.RankOne.SourceHypotheses (imageRepresentation ρ)
      (generalizedFitting (actionImage ρ)) := by
    refine ⟨image_sqtk ρ K hsurvive hs hquot hZ,rfl,?_,imageRepresentation_injective ρ,?_,?_⟩
    · rw [hfit]; exact hqs
    · rw [hfit]; exact hirr
    · exact (cubicRatio_le_quadraticRatio _).trans hbound
  let h : ChapterK.Linear.Recognition.SourceHypothesis KnownSimple.IsKnownSimple
      (imageRepresentation ρ) (generalizedFitting (actionImage ρ)) :=
    ⟨inferInstance,inferInstance,hyp.sqtk,hyp.fitting,hyp.quasisimple,
      hyp.faithful,hyp.irreducible,hyp.smallCubic⟩
  have hm' : ClassicalGroup.IsPSL
      (generalizedFitting (actionImage ρ) ⧸ center (generalizedFitting (actionImage ρ)))
      3 (2 ^ f) := by
    obtain ⟨E,_,_,hE,⟨eE⟩⟩ := hm
    exact ⟨E,inferInstance,inferInstance,hE,⟨(centralQuotientCongr e).symm.trans eE⟩⟩
  obtain ⟨F,hF,eQ,C,_⟩ := ChapterK.Linear.Recognition.SourceFF.exists_binaryField_cover h f hf hm'
  obtain ⟨hnat⟩ := ChapterK.Linear.Recognition.SourceQuadratic.naturalSourceInput_of_quadratic_le_two
    h C eQ hbound
  have hz : center (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) = ⊥ :=
    centerless_of_equiv hZ (e.trans hnat.natural.groupEquiv)
  have hmod := (Matrix.SL3.center_eq_bot_iff_card_mod_three F.Carrier).mp hz
  rw [F.card_eq,hF,Nat.BinaryTorusParity.two_pow_mod_three] at hmod
  exact hmod (by simp [Nat.even_iff.mp he])

/-- Apply the irreducible exclusion through invariant extensions using odd-index traces. -/
theorem fixedSpace_le_of_quadratic_supplement
    (hZ : center K = ⊥) (A : Subgroup D) (hgen : K ⊔ A = ⊤)
    (hs : IsSQTK KnownSimple.IsKnownSimple D) (hquot : IsPGroup 2 (D ⧸ K))
    (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hc : fixedCodim ρ A ≤ 2 * rank A) (hAC : A ⊓ centralizer (K : Set D) = ⊥)
    {f : ℕ} (hf : 0 < f) (he : Even f)
    (hm : ClassicalGroup.IsPSL (K ⧸ center K) 3 (2 ^ f))
    (B : Subgroup K) (hB : ∃ P : Sylow 2 K, normalizer (P : Set K) = B) :
    fixedSpace (ρ.comp K.subtype) B ≤ fixedSpace (ρ.comp K.subtype) ⊤ := by
  obtain ⟨P,hP⟩ := hB
  have hindex : Odd B.index := odd_index_of_sylow_le P B (hP ▸ le_normalizer)
  apply fixedSpace_le_by_quadratic_irreducibles K A B hindex ?_ ρ hq hc
  intro W _ _ _ σ hi hq hc
  by_cases hn : (⊤ : Submodule (ZMod 2) W) ≤ fixedSpace σ K
  · intro w hw k
    exact hn Submodule.mem_top k.val
  · have hK := component_irreducible_of_quadratic_supplement σ K A hZ hgen hA hq hc hAC hi hn
    exact (irreducible_component_false σ K hs hquot hZ hK hn A hA hq hc hAC hf he hm).elim

/-- The fixed-space consequence retains the original component and its marked Borel. -/
theorem fixedSpace_le_of_quadratic_actor
    (hZ : center K = ⊥) (hs : IsSQTK KnownSimple.IsKnownSimple D)
    (A : Subgroup D) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hc : fixedCodim ρ A ≤ 2 * rank A) (hAC : A ⊓ centralizer (K : Set D) = ⊥)
    {f : ℕ} (hf : 0 < f) (he : Even f)
    (hm : ClassicalGroup.IsPSL (K ⧸ center K) 3 (2 ^ f))
    (B : Subgroup K) (hB : ∃ P : Sylow 2 K, normalizer (P : Set K) = B) :
    fixedSpace (ρ.comp K.subtype) B ≤ fixedSpace (ρ.comp K.subtype) ⊤ := by
  let : IsQuasisimple (K.subgroupOf (K ⊔ A)) := componentInSup_quasisimple K A
  apply fixedSpace_le_of_componentInSup ρ K A B
  exact fixedSpace_le_of_quadratic_supplement (ρ.comp (K ⊔ A).subtype)
    (K.subgroupOf (K ⊔ A)) (componentInSup_center K A hZ) (A.subgroupOf (K ⊔ A))
    (componentInSup_generated K A) (hs.subgroup (K ⊔ A)) (componentInSup_quotient K A hA)
    (actorInSup_elementary K A hA) (actorInSup_quadratic ρ K A hq)
    (actorInSup_bound ρ K A hc) (actorInSup_faithful K A hAC) hf he
    (by
      obtain ⟨E,_,_,hE,⟨eE⟩⟩ := hm
      exact ⟨E,inferInstance,inferInstance,hE,
        ⟨(centralQuotientCongr (componentInSupEquiv K A)).trans eE⟩⟩)
    (borelInSup K A B) (borelInSup_sylow K A B hB)

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.NormalEvenLinearThree
