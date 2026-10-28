module
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.ComponentNormality
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.RecognitionStep.Models
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.CoverProjection
public import Theory.Representation.BinaryParabolicNatural.CentralCovers
/-!
# The original four-dimensional linear section determines the full actor

Original component generation makes the actual section projection a central
cover. The checked natural-cover theorem in dimension four makes it an
isomorphism. Conjugating the full H* action through that map gives a faithful
linear action containing all GL₄(2), hence identifies H* with GL₄(2) itself.
The actual K/O₂(K) marking is retained on every representative.

Source: Aschbacher–Smith, 13.7.6(1), printed p.939, n=4 and L₁≤K case;
I.1.6(6), printed p.408.
-/
@[expose] public section
open Subgroup Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section07.ModelExclusions
open Section08.SourceCompletion
open Section08.TransvectionRecognition Component
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionRecognition.Component.RecognitionStep
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
/-- The actual linear-four section gives the whole faithful natural H* module. -/
theorem linear_four_full_action_of_one_le
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinear.GL (Fin 4 → ZMod 2))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (linearRepresentation 4) eK) :
    ∃ (eH : Section08.Source.Hstar H ≃* BinaryLinear.GL (Fin 4 → ZMod 2))
      (eV : Additive (Section08.Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)),
      (∀ k : K, eH (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) =
        eK (QuotientGroup.mk' (pCore 2 K) k)) ∧
      ∀ a v, eV (ρ a v) = eH a (eV v) := by
  have hgen := (component_normal_and_span_of_one_le d hH hF9 hKH hK hL₁K).2.symm
  let : Module.Finite (ZMod 2) (Additive (Section08.Source.Utilde H V₃ V₁)) := Module.Finite.of_finite
  obtain ⟨p,hp⟩ := exists_cover_of_section hKH hK ρ hρ hgen (linearRepresentation 4) eK hs
  let eV := BinaryParabolicNatural.naturalCoverEquiv (by decide : 4 ≤ 4) p hp
  have heV : ∀ a v, eV (ρ (modelActor hKH hK eK a) v) = a (eV v) :=
    fun a v => LinearMap.congr_fun (p.isIntertwining' a) v
  let f : Section08.Source.Hstar H →* BinaryLinear.GL (Fin 4 → ZMod 2) := {
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
  have hmodel (a : BinaryLinear.GL (Fin 4 → ZMod 2)) : f (modelActor hKH hK eK a) = a := by
    apply LinearEquiv.ext
    intro v
    change eV (ρ (modelActor hKH hK eK a) (eV.symm v)) = a v
    rw [heV,eV.apply_symm_apply]
  have hfs : Function.Surjective f := fun a => ⟨modelActor hKH hK eK a,hmodel a⟩
  let eH := MulEquiv.ofBijective f ⟨hf,hfs⟩
  refine ⟨eH,eV,?_,?_⟩
  · intro k
    exact (congrArg f (modelActor_mk hKH hK eK k)).symm.trans (hmodel _)
  · intro a v
    change eV (ρ a v) = eV (ρ a (eV.symm (eV v)))
    rw [eV.symm_apply_apply]
end CFSG.Quasithin.Chapter13.Section07.ModelExclusions
