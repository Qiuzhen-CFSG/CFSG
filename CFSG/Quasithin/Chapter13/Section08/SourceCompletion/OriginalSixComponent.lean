module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.OriginalTransvection
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly.OriginalInputs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly.Six

/-!
# The whole original A₆ component action

The source component theorem constructs its normality, Sylow supplement,
generalized Fitting image and full commutator generation. If the original
action has rank-one displacement, the source transvection theorem recognizes
its whole module and hence the prescribed component section. Otherwise the
proved strict critical-pair argument constructs that same section. Its
literal six-letter extension gives both whole-module alternatives and the
point-residual chief factors.

The original component's A₆ quotient is the row under consideration; no
section, module marking, component structure or earlier-interface callback
is assumed. Source: Aschbacher--Smith, 13.8.26, printed p.962.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open TransvectionRecognition TransvectionRecognition.Component
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.SixAndG2

private theorem rank_one_transvection
    {A E : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E]
    (ρ : Representation (ZMod 2) A E) (g : A)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ g - LinearMap.id)) = 1) :
    IsTransvection ρ g := by
  let t := LinearEquiv.ofBijective (ρ g) (ρ.apply_bijective g)
  obtain ⟨f,v,he⟩ := LinearEquiv.mem_dilatransvections_iff_finrank.mpr
    (show Module.finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) ≤ 1 from hr.le)
  have hact (w : E) : ρ g w = w + f w • v := LinearMap.congr_fun he w
  have hne : ρ g ≠ LinearMap.id := by
    intro h
    rw [h,sub_self,LinearMap.range_zero,finrank_bot] at hr
    contradiction
  have hf : f ≠ 0 := by
    intro h
    apply hne
    ext w
    simpa [h] using hact w
  have hv : v ≠ 0 := by
    intro h
    apply hne
    ext w
    simpa [h] using hact w
  have hfv : f v = 0 := by
    rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (f v) with h | h
    · exact h
    · have htv : t v = 0 := by
        change ρ g v = 0
        rw [hact,h,one_smul,ZModModule.add_self]
      exact (hv (t.map_eq_zero_iff.mp htv)).elim
  exact ⟨f,v,hf,hv,hfv,hact⟩

universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

/-- Both critical cases construct the prescribed A₆ component section and
the full compatible action on the unchanged U_H/V₁. -/
theorem original_six_component_models_of_plane_noncentral
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hmax : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hF9all : ∀ J ∈ Source.Hz (sourceOne L T V₁) T G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
    (hm : ⁅G₁.pCoreIn 2,V₂⁆ ≠ ⊥)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) :
    let := d.uh_elementary hH
    let := (V₁.subgroupOf (Source.UH H V₃)).normal_of_isMulCommutative
    ∀ (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁))),
      IsConjugation H V₃ V₁ ρ →
      ∃ eK' : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6),
        HasSectionModel H V₃ V₁ ρ K hKH
          (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) eK' ∧
        (H : Set G) = (K : Set G) * (T : Set G) ∧
        Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
        SourceSix.MarkedFullAction hKH eK' ρ ∧
        CriticalGeometry.Reorientation.TwoNoncentralChiefFactors
          (ChiefQuotient.loneQuotientRepresentation H V₃ V₁ (sourceOne L T V₁)
            (le_sup_left.trans hH.1.2) ρ) := by
  let := d.uh_elementary hH
  let := (V₁.subgroupOf (Source.UH H V₃)).normal_of_isMulCommutative
  dsimp only
  intro ρ hρ
  have hm' : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥ := by
    rwa [← d.first_normalizer]
  have hcentral := Section05.AmbientSource.source_parabolic_centralizer
    (localNaturalSetup d) eL hmax hm'
  have hcomm : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥ := by
    intro he
    apply hm
    apply bot_unique
    rw [commutator_comm] at he
    exact (commutator_mono le_rfl d.plane_le_seed).trans_eq he
  have earlier := original_earlier_inputs_of_ordinary_plane_noncentral d eL hmax hF9all hm
  have groups := ComponentSieve.FieldComponents.LinearThree.OriginalExclusion.original_linear_group_facts
    d hmax hF9all hcentral hcomm
  obtain ⟨hfit,hUK,_⟩ := SourceAssembly.original_component_structure d hmax hF9all
    hcentral hcomm hH hKH hK
  by_cases hno : ∀ g, Module.finrank (ZMod 2) (LinearMap.range (ρ g - LinearMap.id)) ≠ 1
  · exact SourceAssembly.six_alternative_of_no_rank_one d earlier hH (hF9all H hH)
      hKH hK (groups.component_normal hH hKH hK) (groups.supplement hH hKH hK)
      hfit hUK hcentral hcomm eK ρ hρ hno
  · obtain ⟨t,ht⟩ := not_forall.mp hno
    have htrans := rank_one_transvection ρ t (Classical.not_not.mp ht)
    have hfull := (original_transvection_recognition_of_plane_noncentral d eL hmax
      hF9all hm hH ρ hρ ⟨t,htrans⟩).2
    obtain ⟨eK',hs⟩ := SixRecognition.Constituents.section_of_full_alternatives
      hKH hK eK hfit.symm ρ hρ hUK L (sourceOne L T V₁) (le_sup_left.trans hH.1.2) hfull
    exact ⟨eK',hs,SourceSix.source_alternative_of_section T d earlier hH hKH hK ρ hρ eK' hs⟩

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion
