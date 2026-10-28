module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalModule.Normal.QuadraticModules
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.RemainingModels.Unitary
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.SpecialBorel

/-!
# The unitary component Borel on the original binary module

Recognition on the faithful image of each nontrivial irreducible component
factor gives the actual SU₃ column action. Simultaneous basis change and Sylow
conjugacy align its Borel with the original subgroup. Its full torus has zero
fixed space. Odd-index traces extend the resulting equality of fixed spaces
through invariant extensions, retaining the original common quadratic actor.

Classification/Sieve/Unitary applies this to the literal KT span quotient,
discharging every recognition and Borel premise from the source setup.
Source: Aschbacher--Smith 14.6.20, p.1037, K.3.3, p.456 and F.9.18, pp.325--326.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.NormalUnitary
open ChapterB.QuasisimpleSource
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open OriginalModule.Normal RepresentationReduction
open RepresentationReduction.SourceRestrictions.Cases.Single.SmallRatio
open RepresentationReduction.SourceRestrictions
open RepresentationReduction.SourceRestrictions.FFExclusions.ModelRigidity
open Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.ActionImage.Structure
open BenderSuzuki.MatrixGroups
open HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport
universe u v

/-- Recognize the unitary module and align the actual component Borel. -/
theorem fixedSpace_eq_bot_of_source_model
    {D : Type u} [Group D] [Finite D] {V : Type v}
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (K : Subgroup D)
    (h : ChapterK.RankOne.SourceHypotheses ρ K)
    {f : ℕ} (hf : 2 ≤ f) (hm : ClassicalGroup.IsPSU (K ⧸ center K) 3 (2 ^ f))
    (B : Subgroup K) (hB : ∃ P : Sylow 2 K, normalizer (P : Set K) = B) :
    fixedSpace (ρ.comp K.subtype) B = ⊥ := by
  obtain ⟨F,_,_,J,hF,hconj,⟨eF⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.UnitaryRootNormalizer.charP_binary (by omega) hF
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hc := ChapterB.SourceClassification.unitary_central_quotient h J hf hF hconj eF
  obtain ⟨N⟩ := ChapterK.RankOne.UnitaryRecognition.source_unitaryModel_of_centralQuotient
    J hf hF hconj h hc
  obtain ⟨N⟩ := N.exists_standard (by omega : 0 < f) hF hconj
  let J' := standardForm J
  have hconj' : ∀ x : F, J'.conj x = x ^ (2 ^ f) := hconj
  have hstandard : J'.form = !![0,0,1;0,1,0;1,0,0] := rfl
  obtain ⟨_,_,P,hP,_,_,_,hPB,_⟩ := ChapterF.Source.Unitary.standard_su_borel_data
    J' f (by omega) hF hconj' hstandard
  have hC : ∃ P : Sylow 2 J'.specialSubgroup,
      normalizer (P : Set J'.specialSubgroup) = RemainingModels.unitaryBorel J' hstandard := by
    refine ⟨P,?_⟩
    change normalizer ((P : Subgroup J'.specialSubgroup) : Set J'.specialSubgroup) = _
    rw [hP]
    exact hPB
  obtain ⟨g,hg,he⟩ := exists_innerIntertwiner_sylowNormalizer B
    (RemainingModels.unitaryBorel J' hstandard) hB hC (ρ.comp K.subtype)
    (RemainingModels.unitaryNatural J') N.groupEquiv N.coordinates N.intertwines
  exact fixedSpace_eq_bot_of_equivariant (ρ.comp K.subtype) (RemainingModels.unitaryNatural J')
    (N.groupEquiv.trans (MulAut.conj g)).toMonoidHom
    (N.coordinates.trans (innerIntertwiner (RemainingModels.unitaryNatural J') g)) he
    B (RemainingModels.unitaryBorel J' hstandard) hg
    (RemainingModels.unitary_borel_fixedSpace_eq_bot J' hstandard f (by omega) hF hconj')

variable {D V : Type u} [Group D] [Finite D] [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) D V) (K : Subgroup D) [K.Normal] [IsQuasisimple K]

/-- The same vanishing after passage through the faithful component image. -/
theorem fixedSpace_eq_bot_of_irreducible_component
    (hs : IsSQTK KnownSimple.IsKnownSimple D)
    (hquot : IsPGroup 2 (D ⧸ K)) (hZ : center K = ⊥)
    (hi : IsIrreducible (ρ.comp K.subtype))
    (hn : ¬ (⊤ : Submodule (ZMod 2) V) ≤ fixedSpace ρ K)
    (A : Subgroup D) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hc : fixedCodim ρ A ≤ 2 * rank A) (hAC : A ⊓ centralizer (K : Set D) = ⊥)
    {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSU (K ⧸ center K) 3 (2 ^ f))
    (B : Subgroup K) (hB : ∃ P : Sylow 2 K, normalizer (P : Set K) = B) :
    fixedSpace (ρ.comp K.subtype) B = ⊥ := by
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
  let C := B.map e.toMonoidHom
  have hC : ∃ P : Sylow 2 (generalizedFitting (actionImage ρ)), normalizer (P : Set _) = C :=
    exists_sylow_normalizer_of_equiv e.symm C B
      ((Subgroup.map_symm_eq_iff_map_eq (e := e) B).mpr rfl) hB
  have hm' : ClassicalGroup.IsPSU
      (generalizedFitting (actionImage ρ) ⧸ center (generalizedFitting (actionImage ρ)))
      3 (2 ^ f) := by
    obtain ⟨E,_,_,J,hE,hconj,⟨eE⟩⟩ := hm
    exact ⟨E,inferInstance,inferInstance,J,hE,hconj,⟨(centralQuotientCongr e).symm.trans eE⟩⟩
  have hzero := fixedSpace_eq_bot_of_source_model (imageRepresentation ρ)
    (generalizedFitting (actionImage ρ)) hyp hf hm' C hC
  apply bot_unique
  intro w hw
  apply hzero.le
  rintro ⟨x,hx⟩
  obtain ⟨b,hb,rfl⟩ := hx
  exact hw ⟨b,hb⟩

/-- Extend the irreducible fixed-space calculation through invariant sections. -/
theorem fixedSpace_le_of_quadratic_supplement
    (hZ : center K = ⊥) (A : Subgroup D) (hgen : K ⊔ A = ⊤)
    (hs : IsSQTK KnownSimple.IsKnownSimple D) (hquot : IsPGroup 2 (D ⧸ K))
    (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hc : fixedCodim ρ A ≤ 2 * rank A) (hAC : A ⊓ centralizer (K : Set D) = ⊥)
    {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSU (K ⧸ center K) 3 (2 ^ f))
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
    rw [fixedSpace_eq_bot_of_irreducible_component σ K hs hquot hZ hK hn
      A hA hq hc hAC hf hm B ⟨P,hP⟩]
    exact bot_le

/-- The fixed-space consequence retains the original component and its marked Borel. -/
theorem fixedSpace_le_of_quadratic_actor
    (hZ : center K = ⊥) (hs : IsSQTK KnownSimple.IsKnownSimple D)
    (A : Subgroup D) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hc : fixedCodim ρ A ≤ 2 * rank A) (hAC : A ⊓ centralizer (K : Set D) = ⊥)
    {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSU (K ⧸ center K) 3 (2 ^ f))
    (B : Subgroup K) (hB : ∃ P : Sylow 2 K, normalizer (P : Set K) = B) :
    fixedSpace (ρ.comp K.subtype) B ≤ fixedSpace (ρ.comp K.subtype) ⊤ := by
  let : IsQuasisimple (K.subgroupOf (K ⊔ A)) := componentInSup_quasisimple K A
  apply fixedSpace_le_of_componentInSup ρ K A B
  exact fixedSpace_le_of_quadratic_supplement (ρ.comp (K ⊔ A).subtype)
    (K.subgroupOf (K ⊔ A)) (componentInSup_center K A hZ) (A.subgroupOf (K ⊔ A))
    (componentInSup_generated K A) (hs.subgroup (K ⊔ A)) (componentInSup_quotient K A hA)
    (actorInSup_elementary K A hA) (actorInSup_quadratic ρ K A hq)
    (actorInSup_bound ρ K A hc) (actorInSup_faithful K A hAC) hf
    (by
      obtain ⟨E,_,_,J,hE,hconj,⟨eE⟩⟩ := hm
      exact ⟨E,inferInstance,inferInstance,J,hE,hconj,
        ⟨(centralQuotientCongr (componentInSupEquiv K A)).trans eE⟩⟩)
    (borelInSup K A B) (borelInSup_sylow K A B hB)

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.NormalUnitary
