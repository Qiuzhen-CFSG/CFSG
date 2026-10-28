module
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.ComponentNormality
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.RecognitionStep.Models
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.CoverProjection
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.CoverSeed
public import Theory.Representation.SLThreeCentralExtension.SylowCover
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.GroupTheory.SylowNormalIntersection
/-!
# The original three-dimensional linear section gives the full natural action

The actual point of the source flag survives the central covering map and
is fixed by the image of the original Sylow subgroup. The binary SL₃ cover
criterion therefore makes that map bijective. Its full linear actor identifies
H* with GL₃(2), compatibly with every original component representative.

Source: Aschbacher–Smith, 13.7.6(1), printed p.939, the n=3 contained case.
This supplies the natural action used to construct the later C3 system.
-/
@[expose] public section
open Subgroup Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section07.ModelExclusions
open Section08.SourceCompletion
open Section08.TransvectionRecognition Component
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionRecognition.Component.RecognitionStep
open Section08.TransvectionParabolic.Marking
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
  [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
private theorem tilde_faithful
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ) : Function.Injective ρ := by
  apply faithful_of_centralizer_le_core ρ hρ
  intro x hx
  change x ∈ (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).QH
  rw [← hF9.kernel_UH_eq_QH]
  apply (hF9.mem_kernel_iff hF9.UH_le_H).mpr
  refine ⟨commutatorPreimage_le _ _ _ hx, ?_⟩
  intro u hu
  rw [← commutatorElement_inv]
  apply V₁.inv_mem
  exact commutator_commutatorPreimage_le H (Section08.Source.UH H V₃) V₁
    (hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
      (commutator_mem_commutator hx hu)

include d
/-- The actual linear-three section gives the whole faithful natural H* module. -/
theorem special_linear_three_full_action_of_one_le
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (hs : HasSectionModel H V₃ V₁ ρ K hKH BinaryLinearThree.W eK) :
    ∃ (eH : Section08.Source.Hstar H ≃* BinaryLinear.GL (Fin 3 → ZMod 2))
      (eV : Additive (Section08.Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)),
      (∀ k : K, eH (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) =
        BinaryLinear.OuterCyclic.slEquivLinear 3 (eK (QuotientGroup.mk' (pCore 2 K) k))) ∧
      ∀ a v, eV (ρ a v) = eH a (eV v) := by
  obtain ⟨hKn,hgen⟩ := component_normal_and_span_of_one_le d hH hF9 hKH hK hL₁K
  let : Module.Finite (ZMod 2) (Additive (Section08.Source.Utilde H V₃ V₁)) := Module.Finite.of_finite
  obtain ⟨p,hp⟩ := exists_cover_of_section hKH hK ρ hρ hgen.symm BinaryLinearThree.W eK hs
  let hL₁H := hL₁K.trans hKH
  have hker (u) (hu : p u = 0) (l : sourceOne L T V₁) :
      ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hL₁H l)) u = u := by
    have hh := hp.2.1 hu (eK (QuotientGroup.mk' (pCore 2 K) ⟨l,hL₁K l.property⟩))
    have hie : inclusion hKH (⟨l,hL₁K l.property⟩ : K) = inclusion hL₁H l := Subtype.ext rfl
    simpa only [MonoidHom.comp_apply,modelActor_mk,hie] using hh
  have hpi := seed_cover_injective d hL₁H ρ hρ p.toLinearMap hker
  have hP₂ : sectionImage H V₃ V₁ V₂ ≠ ⊥ := by
    intro hz
    have hh := plane_section_finrank d (H := H)
    rw [hz,finrank_bot] at hh
    omega
  obtain ⟨u,hu,hu0⟩ := (Submodule.ne_bot_iff _).mp hP₂
  have huP : u ∈ sectionImage H V₃ V₁ V₃ := by
    obtain ⟨v,hv,rfl⟩ := hu
    exact ⟨v,d.plane_le_seed hv,rfl⟩
  have hpu : p u ≠ 0 := by
    intro hz
    have hh := hpi (a₁ := ⟨u,huP⟩) (a₂ := 0) (hz.trans (map_zero _).symm)
    exact hu0 (congrArg Subtype.val hh)
  let KN := K.subgroupOf H
  let : KN.Normal := (normal_subgroupOf_iff_le_normalizer hKH).mpr hKn
  have hTH : (T : Subgroup G) ≤ H := hF9.T_le_H
  obtain ⟨Q,hQ⟩ := (T.subtype hTH).exists_subgroupOf_eq_of_normal KN
  let e0 : KN ≃* K := subgroupOfEquivOfLe hKH
  let q := eK.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 K)).comp e0.toMonoidHom)
  have hq : Function.Surjective q := eK.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp e0.surjective)
  let S := Q.mapSurjective hq
  have hfixed : ∀ g ∈ S, (ρ.comp (modelActor hKH hK eK)) g u = u := by
    rintro g ⟨k,hk,rfl⟩
    change ρ (modelActor hKH hK eK (eK (QuotientGroup.mk' (pCore 2 K) (e0 k)))) u = u
    rw [modelActor_mk]
    apply plane_vector_fixed d ρ hρ _ _ u hu hu0
    have ht : k ∈ ((T.subtype hTH : Sylow 2 H) : Subgroup H).subgroupOf KN := hQ ▸ hk
    exact ht
  have hbij := OneCohomology.SLThreeCentralExtension.cover_bijective_of_sylow_fixed
    (ρ.comp (modelActor hKH hK eK)) p hp S u hpu hfixed
  let eV := LinearEquiv.ofBijective p.toLinearMap hbij
  let c := BinaryLinear.OuterCyclic.slEquivLinear 3
  have heV : ∀ a v, eV (ρ (modelActor hKH hK eK a) v) = c a (eV v) :=
    fun a v => LinearMap.congr_fun (p.isIntertwining' a) v
  let f : Section08.Source.Hstar H →* BinaryLinear.GL (Fin 3 → ZMod 2) := {
    toFun a := eV.symm.trans ((LinearEquiv.ofBijective (ρ a) (ρ.apply_bijective a)).trans eV)
    map_one' := by
      apply LinearEquiv.ext
      intro v
      change eV (ρ 1 (eV.symm v)) = v
      rw [map_one,Module.End.one_apply,eV.apply_symm_apply]
    map_mul' a b := by
      apply LinearEquiv.ext
      intro v
      change eV (ρ (a*b) (eV.symm v)) =
        eV (ρ a (eV.symm (eV (ρ b (eV.symm v)))))
      rw [eV.symm_apply_apply,map_mul,Module.End.mul_apply] }
  have hf : Function.Injective f := by
    intro a b hab
    apply tilde_faithful hF9 ρ hρ
    apply LinearMap.ext
    intro v
    apply eV.injective
    have hh := LinearEquiv.congr_fun hab (eV v)
    change eV (ρ a (eV.symm (eV v))) = eV (ρ b (eV.symm (eV v))) at hh
    simpa only [eV.symm_apply_apply] using hh
  have hmodel (a : BinaryLinearThree.Group) : f (modelActor hKH hK eK a) = c a := by
    apply LinearEquiv.ext
    intro v
    change eV (ρ (modelActor hKH hK eK a) (eV.symm v)) = c a v
    rw [heV,eV.apply_symm_apply]
  have hfs : Function.Surjective f := fun a =>
    ⟨modelActor hKH hK eK (c.symm a),(hmodel _).trans (c.apply_symm_apply a)⟩
  let eH := MulEquiv.ofBijective f ⟨hf,hfs⟩
  refine ⟨eH,eV,?_,?_⟩
  · intro k
    exact (congrArg f (modelActor_mk hKH hK eK k)).symm.trans (hmodel _)
  · intro a v
    change eV (ρ a v) = eV (ρ a (eV.symm (eV v)))
    rw [eV.symm_apply_apply]
/-- The same full action in the literal binary linear-group convention. -/
theorem linear_three_full_action_of_one_le
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinear.GL (Fin 3 → ZMod 2))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (linearRepresentation 3) eK) :
    ∃ (eH : Section08.Source.Hstar H ≃* BinaryLinear.GL (Fin 3 → ZMod 2))
      (eV : Additive (Section08.Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)),
      (∀ k : K, eH (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) =
        eK (QuotientGroup.mk' (pCore 2 K) k)) ∧
      ∀ a v, eV (ρ a v) = eH a (eV v) := by
  let c := BinaryLinear.OuterCyclic.slEquivLinear 3
  have hs' : HasSectionModel H V₃ V₁ ρ K hKH BinaryLinearThree.W (eK.trans c.symm) := by
    obtain ⟨hst,e,he⟩ := hs
    refine ⟨hst,e,?_⟩
    intro k v
    rw [he]
    change eK (QuotientGroup.mk' (pCore 2 K) k) _ = c (c.symm (eK (QuotientGroup.mk' (pCore 2 K) k))) _
    rw [c.apply_symm_apply]
  obtain ⟨eH,eV,heK,heV⟩ :=
    special_linear_three_full_action_of_one_le d hH hF9 hKH hK hL₁K ρ hρ (eK.trans c.symm) hs'
  refine ⟨eH,eV,?_,heV⟩
  intro k
  exact (heK k).trans (c.apply_symm_apply _)
end CFSG.Quasithin.Chapter13.Section07.ModelExclusions
