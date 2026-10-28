module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSevenAutomizer
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledSevenPair
public import CFSG.Quasithin.ChapterE.Section04.Basic

/-!
# H.8 on the actual doubled A₇ orbit

The original component and conjugator construct the full S₇ automizer.
Transporting its action through the same product coordinates gives the
genuine H.8 pair. Its first and second subspaces are exactly the chosen
seed and its original conjugate. H.8 therefore gives m = 4, a = 2,
β ≥ 4, α = ∞ and exclusion of every (F - 1)-offender on the full ambient
automizer, not just on an auxiliary concrete model.

These are the representation inputs to 7.5.5. The source's row-scoped
centralizer argument, global w bound and improved r ≥ 6 remain to be
proved before the chosen-module contradiction can be asserted.
Source: Aschbacher--Smith D.3.10, H.8 and 7.5.5, printed pp.201,389,701.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
open Representation.AlternatingSevenConjugatePair
open Representation.AlternatingSevenConjugatePair.Model
open ChapterE ChapterH.AlternatingPair
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The H.8 pair is equivalent to the full ambient action and retains both
original seed axes. No extra representation or exchange hypothesis is used. -/
theorem sourceOrbit_seven_H8_pair
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) Four)
    (hσ : Function.Injective σ)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ)) :
    ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
      ∃ P : Pair Eight, ∃ E : ActionEquiv (automizerRepresentation D.sourceOrbit) P.representation,
        (∀ v, E.linearEquiv v ∈ P.first.toSubmodule ↔ (v.toMul : G) ∈ V) ∧
        (∀ v, E.linearEquiv v ∈ P.second.toSubmodule ↔
          (v.toMul : G) ∈ V.map (MulAut.conj t).toMonoidHom) := by
  obtain ⟨C⟩ := D.sourceOrbit_seven_action_coordinates h hd σ hσ hmodel
  let μ := automizerRepresentation D.sourceOrbit
  let τ := σ.comp C.twist.toMonoidHom
  let γ : Representation (ZMod 2) (Automizer D.sourceOrbit) Eight :=
    C.coordinates.conjRingEquiv.toMonoidHom.comp μ
  let ρ : Representation (ZMod 2) (Equiv.Perm (Fin 7)) Eight :=
    γ.comp C.automizer.symm.toMonoidHom
  have hρ : Function.Injective ρ := C.coordinates.conjRingEquiv.injective.comp
    ((automizerRepresentation_injective D.sourceOrbit).comp C.automizer.symm.injective)
  have hinner (a : alternatingGroup (Fin 7)) : ρ a.val = (σ.prod τ) a := by
    obtain ⟨l,rfl⟩ := C.component_surjective a
    apply LinearMap.ext
    intro w
    obtain ⟨v,rfl⟩ := C.coordinates.surjective w
    change C.coordinates (μ (C.automizer.symm (C.component l).val)
      (C.coordinates.symm (C.coordinates v))) = (σ.prod τ) (C.component l) (C.coordinates v)
    rw [C.coordinates.symm_apply_apply,← C.component_formula,C.automizer.symm_apply_apply]
    exact C.action l v
  obtain ⟨P,hP,hF,hS⟩ := doubledSeven_pair_of_symmetric_action σ τ hσ
    (hσ.comp C.twist.injective) four_dimension C.inequivalent ρ hρ hinner
  let E : ActionEquiv μ P.representation := {
    groupEquiv := C.automizer
    linearEquiv := C.coordinates
    intertwines := by
      intro g v
      rw [hP]
      change C.coordinates (μ g v) = C.coordinates
        (μ (C.automizer.symm (C.automizer g)) (C.coordinates.symm (C.coordinates v)))
      rw [C.automizer.symm_apply_apply,C.coordinates.symm_apply_apply] }
  refine ⟨C.conjugator,C.in_sylow,C.moves_seed,P,E,?_,?_⟩
  · intro v
    rw [hF]
    exact C.first_axis v
  · intro v
    rw [hS]
    exact C.second_axis v

/-- H.8's parameters for the actual whole-orbit automizer. These are local
representation parameters; the global source parameter r is not inferred here. -/
theorem sourceOrbit_seven_H8_parameters
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) Four)
    (hσ : Function.Injective σ)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ)) :
    localM D.sourceOrbit = 4 ∧ localA D.sourceOrbit = 2 ∧
      4 ≤ moduleBeta (automizerRepresentation D.sourceOrbit) ∧
      moduleAlpha (automizerRepresentation D.sourceOrbit) = ⊤ ∧
      (∀ A, ¬ IsFMinusOneOffender (automizerRepresentation D.sourceOrbit) A) ∧
      (∀ t : Automizer D.sourceOrbit, orderOf t = 2 →
        fixedCodim (automizerRepresentation D.sourceOrbit) (zpowers t) = 4) := by
  obtain ⟨_,_,_,P,E,_,_⟩ := D.sourceOrbit_seven_H8_pair h hd σ hσ hmodel
  let μ := automizerRepresentation D.sourceOrbit
  have hcod (t : Automizer D.sourceOrbit) : fixedCodim μ (zpowers t) =
      fixedCodim P.representation (zpowers (E.groupEquiv t)) := by
    simpa only [MonoidHom.map_zpowers,MulEquiv.coe_toMonoidHom] using fixedCodim_map_equivariant μ P.representation
      E.groupEquiv.toMonoidHom E.linearEquiv E.intertwines (zpowers t)
  have hinv (t : Automizer D.sourceOrbit) (ht : orderOf t = 2) :
      fixedCodim μ (zpowers t) = 4 := by
    rw [hcod]
    exact P.involution_fixedCodim _ ((orderOf_injective E.groupEquiv.toMonoidHom E.groupEquiv.injective t).trans ht)
  have hm : moduleM μ = 4 := moduleM_eq_of_constant_involution_codim μ
    ⟨E.groupEquiv.symm (Equiv.swap (0 : Fin 7) 1),
      (orderOf_injective E.groupEquiv.symm.toMonoidHom E.groupEquiv.symm.injective _).trans
        (orderOf_eq_prime (by decide) (by decide))⟩ hinv
  obtain ⟨_,_,ha,_,hnoP,_⟩ := parameters P
  have ha' : moduleA μ = 2 := (moduleA_eq_of_equivariant_equiv μ P.representation
    E.groupEquiv E.linearEquiv E.intertwines).trans ha
  have hbeta : 4 ≤ moduleBeta μ := le_moduleBeta_of_odd_prime_codim μ (by
    intro t ht ht2
    rw [hcod]
    have he := orderOf_injective E.groupEquiv.toMonoidHom E.groupEquiv.injective t
    exact P.odd_prime_fixedCodim _ (he ▸ ht) (he ▸ ht2))
  have hno (A : Subgroup (Automizer D.sourceOrbit)) : ¬ IsFMinusOneOffender μ A := by
    intro hA
    let : IsElementaryAbelian 2 A := hA.1.2
    apply hnoP (A.map E.groupEquiv.toMonoidHom)
    refine ⟨⟨?_,IsElementaryAbelian.map E.groupEquiv.toMonoidHom⟩,?_⟩
    · intro hb
      apply hA.1.1
      apply Subgroup.map_injective (f := E.groupEquiv.toMonoidHom) E.groupEquiv.injective
      simpa only [Subgroup.map_bot] using hb
    · rw [← fixedCodim_map_equivariant μ P.representation E.groupEquiv.toMonoidHom
        E.linearEquiv E.intertwines,rank_map_injective E.groupEquiv.toMonoidHom E.groupEquiv.injective]
      exact hA.2
  exact ⟨hm,ha',hbeta,moduleAlpha_eq_top_of_no_offender μ hno,hno,hinv⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
