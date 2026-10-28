module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.OriginalEarlierInputs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FourLocalFactors.ChiefGeneration

/-!
# Original six-letter flags and chief factors

The actual Sylow-stable source flag supplies simultaneous natural or
augmentation coordinates. Its faithful six-letter action sends the actual
component onto A₆, as its image has index two. Restricting that same action
therefore constructs the point marking without changing the chosen module.
The fixed order-two kernel transfers the two noncentral chief factors from
U_H to its literal quotient U_H/V₁.

These are the exact fixed-configuration 13.7.6 interfaces used by the
ordinary terminal argument. The preceding component interface is proved
from the original plane noncentrality, rather than assumed here.
Source: Aschbacher–Smith, 13.7.6(3a), printed p.939.
-/

public section
open Subgroup Representation BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open TransvectionRecognition TransvectionRecognition.Component
open TransvectionRecognition.Component.ModelExtension
open TransvectionParabolic.Marking

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

private theorem component_permutation_marking
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (f : Source.Hstar H →* Equiv.Perm (Fin 6)) (hf : Function.Injective f) :
    ∃ e : Source.starImage H K ≃* alternatingGroup (Fin 6),
      ∀ k, (e k : Equiv.Perm (Fin 6)) = f k := by
  let C := Source.starImage H K
  let eC := componentModelEquiv hKH hK eK
  have hc : Nat.card (C.map f) = 360 := by
    rw [card_map_of_injective hf, Nat.card_congr eC.toEquiv]
    exact Theory.SpecificGroups.SymmetricSix.a6_order
  have hi := (C.map f).index_mul_card
  rw [hc,Theory.SpecificGroups.SymmetricSix.s6_order] at hi
  have he : C.map f = alternatingGroup (Fin 6) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two (by omega)
  exact ⟨(C.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr he),fun _ => rfl⟩

private theorem original_six_point_marking
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hLK : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (alternatingNaturalRepresentation (Fin 6)) eK) :
    NaturalSection.SixPointMarking H K V₂ V₃ V₁ ρ := by
  obtain ⟨_,hcases⟩ := Section07.ModelExclusions.six_seed_marking_of_one_le
    (localNaturalSetup d) hH hF9 hKH hK hLK ρ hρ eK hs
  rcases hcases with ⟨f,E,hf,he,hp,_⟩ | ⟨f,E,hf,he,hp,_⟩
  · obtain ⟨e,heq⟩ := component_permutation_marking hKH hK eK f hf
    refine ⟨e,Or.inl ⟨E,?_,hp⟩⟩
    intro k v
    change E (ρ k v) = naturalRepresentation (Fin 6) (e k).val (E v)
    rw [heq]
    exact he k v
  · obtain ⟨e,heq⟩ := component_permutation_marking hKH hK eK f hf
    refine ⟨e,Or.inr ⟨E,?_,hp⟩⟩
    intro k v
    change E (ρ k v) = coreRepresentation (Fin 6) (e k).val (E v)
    rw [heq]
    exact he k v

/-- The original point-marked 13.7.6 family for the fixed ordinary source. -/
theorem original_earlier1376_of_ordinary_plane_noncentral
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hmax : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hF9all : ∀ H ∈ Source.Hz (sourceOne L T V₁) T G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hm : ⁅G₁.pCoreIn 2,V₂⁆ ≠ ⊥) :
    NaturalSection.Earlier1376 L (sourceOne L T V₁) T G₁ M V₂ V₃ V₁ := by
  have earlier := original_earlier_inputs_of_ordinary_plane_noncentral d eL hmax hF9all hm
  intro H hH _ hnormal hmodule ρ hρ K hKH hK n hn eK hs
  let := d.uh_elementary hH
  obtain ⟨hg,hLK,hprod,hcases⟩ := earlier.alternating d H hH ρ hρ K hKH hK n hn eK hs
  refine ⟨hg,hLK,hprod,?_⟩
  rcases hcases with ⟨rfl,hL,_⟩ | ⟨_,hc⟩
  · exact Or.inl ⟨rfl,hL,original_six_point_marking d hH (hF9all H hH)
      hKH hK hLK ρ hρ eK hs⟩
  · obtain ⟨ec⟩ := hc
    have hh := Nat.card_congr (centerCongr (ec.symm.trans eL)).toEquiv
    rw [Representation.Hexacode.even_center_card,
      alternatingGroup.center_eq_bot (by simp),card_bot] at hh
    omega

/-- The source chief count descends through the actual fixed line V₁. -/
theorem original_earlier1376_chief_of_ordinary_plane_noncentral
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hmax : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hF9all : ∀ H ∈ Source.Hz (sourceOne L T V₁) T G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hm : ⁅G₁.pCoreIn 2,V₂⁆ ≠ ⊥) :
    TransvectionQuotients.FourLocalFactors.ChiefGeneration.Earlier1376ChiefFactors
      (sourceOne L T V₁) T G₁ M V₃ V₁ := by
  have earlier := original_earlier_inputs_of_ordinary_plane_noncentral d eL hmax hF9all hm
  intro H hH hline hnormal hmodule ρ hρ K hKH hK eK hs
  let := d.uh_elementary hH
  obtain ⟨_,_,_,hcases⟩ := earlier.alternating d H hH ρ hρ K hKH hK 6 (by decide) eK hs
  rcases hcases with ⟨_,_,hchief⟩ | ⟨hn,_⟩
  · exact ChiefQuotient.twoNoncentralChiefFactors_utilde H V₃ V₁
      (sourceOne L T V₁) (le_sup_left.trans hH.1.2) ρ hρ hline d.line_card hchief
  · omega

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion
