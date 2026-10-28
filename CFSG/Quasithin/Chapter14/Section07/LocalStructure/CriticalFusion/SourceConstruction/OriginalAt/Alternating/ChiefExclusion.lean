module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ChiefExclusion
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.Alternating.CriticalOffender

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CriticalOffender
public import Theory.Representation.AlternatingFiveSmallDisplacement

/-!
# Chief-factor exclusion at the same G,T

A nonidentity selected actor moves at most three dimensions. Two noncentral alternating sections would each move at least two, so every invariant subspace or its quotient has trivial alternating action.

Only Structural1222At at the original G,T is used. Independent model and
section lemmas are reused from LocalReduction; its universal APIs are preserved.
Source: Aschbacher–Smith, final paragraph of 14.7.40, printed p.1063,
and 14.7.52–63, printed pp.1065–1069. Earlier structural source discharge
and the unconditional classification remain with their existing owners.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) F.H W}

/-- The literal section has no invariant subspace on which both it and the
corresponding quotient have nontrivial alternating action. Each would move
at least two dimensions, contradicting the selected actor's bound three. -/
theorem alternating_section_submodule_dichotomy_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hAlt : AlternatingResidual F)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (e : HStar F.H ≃* ChapterJ.S5) (σ : Representation (ZMod 2) ChapterJ.S5 W)
    (hσ : σ.comp (quotientMarking e) = ρ)
    (P : Subrepresentation (σ.comp (alternatingGroup (Fin 5)).subtype)) :
    P.toRepresentation = 1 ∨ P.quotientRepresentation = 1 := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  let : Finite W := Finite.of_surjective (fun v : F.U => (s.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  obtain ⟨c,hs,hplace,_,_⟩ := exists_selected_critical_geometry_of_alternating_at h hab structural hAlt
  let A := star F c.Uα
  let : Nontrivial A := (nontrivial_iff_ne_bot _).mpr (c.star_ne_bot hs)
  obtain ⟨x,hx⟩ := exists_ne (1:A)
  obtain ⟨a,ha,he⟩ := x.property
  have hxa : quotientMarking e a ∈ alternatingGroup (Fin 5) :=
    point_core_image_le_alternating_at h structural e (mem_map_of_mem _ (hplace ha))
  let b : alternatingGroup (Fin 5) := ⟨quotientMarking e a,hxa⟩
  have hb : b ≠ 1 := by
    intro hz
    apply hx
    apply Subtype.ext
    apply e.injective
    have hz' : e (starMap F a) = 1 := congrArg Subtype.val hz
    rw [he] at hz'
    change e (x:HStar F.H) = e (1:HStar F.H)
    simpa only [map_one] using hz'
  let : IsElementaryAbelian 2 c.Uα :=
    IsElementaryAbelian.map (MulAut.conj c.conjugator⁻¹).toMonoidHom
  have hb2 : b^2=1 := by
    apply Subtype.ext
    change quotientMarking e a ^ 2 = 1
    rw [←map_pow]
    have haa : (a:G) ∈ c.Uα := ha
    have he : a^2=1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (a:G) haa)
    rw [he,map_one]
  have hd := selected_critical_displacement_le_three_at h hab structural e s c hs a ha
  have hrep : (σ.comp (alternatingGroup (Fin 5)).subtype) b = ρ a :=
    congrArg (fun k : Representation (ZMod 2) F.H W => k a) hσ
  exact AlternatingFiveSmallDisplacement.submodule_or_quotient_trivial _ b (orderOf_eq_prime hb2 hb)
    (hrep.symm ▸ hd) P

/-- The existing faithful symmetric descent now carries the original
alternating chief-factor exclusion, on the same coordinates and marking. -/
theorem exists_faithful_symmetric_action_with_chief_dichotomy_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hAlt : AlternatingResidual F)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ) :
    ∃ (e : HStar F.H ≃* ChapterJ.S5) (σ : Representation (ZMod 2) ChapterJ.S5 W),
      σ.comp (quotientMarking e) = ρ ∧ Function.Injective σ ∧
      ∀ P : Subrepresentation (σ.comp (alternatingGroup (Fin 5)).subtype),
        P.toRepresentation = 1 ∨ P.quotientRepresentation = 1 := by
  obtain ⟨e⟩ := exists_symmetric_star_at h structural hAlt
  obtain ⟨σ,hσ,hf⟩ := exists_faithful_symmetric_representation h e s
  exact ⟨e,σ,hσ,hf,alternating_section_submodule_dichotomy_at h hab structural hAlt s e σ hσ⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
