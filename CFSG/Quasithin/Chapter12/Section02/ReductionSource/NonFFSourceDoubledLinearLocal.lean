module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledLinearLocal
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledLinearGeneration
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.SourceCompleteBound
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledLinearRank

/-!
# Initial whole-orbit bounds for the original nonbinary linear-three pair

The original normal component embeds the whole automizer in the marked
pair normalizer. Its involution bound gives m ≥ 2n; completed E.6.3 then
gives r ≥ m. The proved Hall and Cartan bound separates the actual
minimum, yielding w ≤ n. The stronger r ≥ 4n of 7.4.1 remains a genuine
source duty and is not assumed or asserted here.
Source: Aschbacher--Smith Table7.2.1, 7.3.2 and 7.3.4, pp.698--699.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE

private theorem local_of_marked_pair
    {H J P U X Y : Type*} [Group H] [Finite H] [Group J] [Group P]
    [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y] [FiniteDimensional (ZMod 2) Y]
    (σ : Representation (ZMod 2) P X) (τ : Representation (ZMod 2) P Y)
    [IsIrreducible σ] [IsIrreducible τ]
    (ρ : Representation (ZMod 2) H U) (hρ : Function.Injective ρ)
    (i : J →* H) [i.range.Normal] (q : J →* P) (hq : Function.Surjective q)
    (E : U ≃ₗ[ZMod 2] (X × Y))
    (hE : ∀ j v, E (ρ (i j) v) = (σ.prod τ) (q j) (E v)) :
    ChapterE.moduleM (normalizerRepresentation (σ.prod τ)) ≤ ChapterE.moduleM ρ := by
  let μ := σ.prod τ
  let γ : Representation (ZMod 2) H (X × Y) := E.conjRingEquiv.toMonoidHom.comp ρ
  have he (g : H) (v : U) : E (ρ g v) = γ g (E v) := by
    change E (ρ g v) = E (ρ g (E.symm (E v)))
    rw [E.symm_apply_apply]
  have hγ : Function.Injective γ := E.conjRingEquiv.injective.comp hρ
  have hres (j : J) : γ (i j) = μ (q j) := by
    apply LinearMap.ext
    intro w
    obtain ⟨v,rfl⟩ := E.surjective w
    rw [←he]
    exact hE j v
  have himage : i.range.map γ.asGroupHom = actionImage μ := by
    ext z
    constructor
    · rintro ⟨_,⟨j,rfl⟩,rfl⟩
      exact ⟨q j,Units.ext (hres j).symm⟩
    · rintro ⟨p,rfl⟩
      obtain ⟨j,rfl⟩ := hq p
      exact ⟨i j,⟨j,rfl⟩,Units.ext (hres j)⟩
  have hn (g : H) : γ.asGroupHom g ∈ linearNormalizer μ := by
    change γ.asGroupHom g ∈ normalizer (actionImage μ : Set _)
    rw [←himage]
    exact i.range.le_normalizer_map γ.asGroupHom
      (mem_map_of_mem _ (show g ∈ normalizer (i.range : Set H) from
        le_normalizer_of_normal (mem_top g)))
  let j : H →* linearNormalizer μ := γ.asGroupHom.codRestrict _ hn
  have hj : Function.Injective j := by
    intro x y hxy
    exact hγ (congrArg (fun z : linearNormalizer μ => z.val.val) hxy)
  apply le_csInf ⟨_,Set.mem_insert _ _⟩
  rintro d (rfl | ⟨g,hg,rfl⟩)
  · rw [E.finrank_eq]
    exact ChapterE.moduleM_le_dimension _
  · have horder : orderOf (j g) = 2 := (orderOf_injective j hj g).trans hg
    have hcod := fixedCodim_map_equivariant ρ (normalizerRepresentation μ) j E he (zpowers g)
    rw [MonoidHom.map_zpowers] at hcod
    exact hcod ▸ ChapterE.moduleM_le_involution _ horder

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Every involution of the actual whole-orbit automizer moves at least 2n dimensions. -/
theorem sourceOrbit_linear_localM
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) : 2*F.degree ≤ localM D.sourceOrbit := by
  obtain ⟨a,q,hq,hne,E,hE⟩ := D.original_twisted_coordinates h hd F hmodel
  let σ := linearNatural F 3
  let τ := σ.comp a.toMonoidHom
  let : IsIrreducible σ := ExtensionConsequences.linearNatural_irreducible F (by decide)
  let : IsIrreducible τ := (irreducible_comp_surjective_iff
    a.toMonoidHom a.surjective σ).mpr inferInstance
  let W := D.sourceOrbit
  let N := normalizer (W : Set G)
  let qN := W.normalizerMonoidHom.rangeRestrict
  let i : L →* Automizer W := qN.comp (inclusion D.sourceOrbit_component_normalizes)
  have hi : i.range = (L.subgroupOf N).map qN := by
    ext z
    constructor
    · rintro ⟨l,rfl⟩
      exact ⟨inclusion D.sourceOrbit_component_normalizes l,l.property,rfl⟩
    · rintro ⟨l,hl,rfl⟩
      exact ⟨⟨l,hl⟩,rfl⟩
  let : (L.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer
    (D.sourceOrbit_normalizer_le h.toHypothesis1221)
  let : i.range.Normal := hi ▸ Normal.map inferInstance qN
    W.normalizerMonoidHom.rangeRestrict_surjective
  exact (doubledLinear_normalizer_moduleM F a hne).trans
    (local_of_marked_pair σ τ (automizerRepresentation W)
      (automizerRepresentation_injective W) i q hq E hE)

/-- The completed original E.6.3 applies to the whole pair for n>1. -/
theorem sourceOrbit_linear_initial_globalR
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hn : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) :
    ((2*F.degree : ℕ) : ℕ∞) ≤ globalR D.sourceOrbit := by
  have hm := D.sourceOrbit_linear_localM h hd F hmodel
  have hr := (Section06.FrobeniusReduction.lower_bound_knownSimple
    (D.sourceOrbit_hypothesisE61_of_markedDoubled h hd) (by omega)).1
  have hm' : ((2*F.degree : ℕ) : ℕ∞) ≤ (localM D.sourceOrbit : ℕ∞) := by exact_mod_cast hm
  exact hm'.trans hr

/-- Hall faithfulness and the actual initial centralizer bound give w≤n. -/
theorem sourceOrbit_linear_globalW_le_degree
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (F : BinaryField) (hn : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) : globalW D.sourceOrbit T ≤ F.degree := by
  have hb := D.sourceOrbit_linear_min_parameters_le_degree h hd hmany hnon F hn hmodel
  have hr : (F.degree : ℕ∞) < globalR D.sourceOrbit :=
    (show (F.degree : ℕ∞) < ((2*F.degree : ℕ) : ℕ∞) by exact_mod_cast (by omega : F.degree < 2*F.degree)).trans_le
      (D.sourceOrbit_linear_initial_globalR h hd F hn hmodel)
  exact (min_le_iff.mp hb).resolve_right (not_le_of_gt hr)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
