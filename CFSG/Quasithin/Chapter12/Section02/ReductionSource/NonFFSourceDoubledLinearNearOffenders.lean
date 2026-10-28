module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledLinearNearOffenders
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledLinearLocal
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuRankOneThompson
-- Retain the exact original twisted-pair coordinates and normal component image.
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledLinearRank

/-!
# Original nonbinary near-offender and Thompson centralization

The original component image is normal in the actual whole-orbit automizer.
Its literal pair coordinates therefore embed that automizer in the native
full pair normalizer, preserving the same actor and fixed codimensions.
The native strict near-offender gap makes every higher-Thompson generator
centralize the entire original orbit. In particular the J1 hypothesis of
E.6.27 holds for each original local subspace centralizer.
No beta bound, local Cartan bound or source callback is assumed.
Source: Aschbacher--Smith H.4.1, 7.4.1 and E.6.27, printed pp.383--385,
700 and257, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE

private theorem gap_of_marked_pair
    {H J P U X Y : Type*} [Group H] [Finite H] [Group J] [Group P]
    [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y] [FiniteDimensional (ZMod 2) Y]
    (σ : Representation (ZMod 2) P X) (τ : Representation (ZMod 2) P Y)
    (ρ : Representation (ZMod 2) H U) (hρ : Function.Injective ρ)
    (i : J →* H) [i.range.Normal] (q : J →* P) (hq : Function.Surjective q)
    (E : U ≃ₗ[ZMod 2] (X × Y))
    (hE : ∀ j v, E (ρ (i j) v) = (σ.prod τ) (q j) (E v)) :
    (∀ A : Subgroup (linearNormalizer (σ.prod τ)), IsElementaryTwo A →
      rank A+1 < fixedCodim (normalizerRepresentation (σ.prod τ)) A) →
    ∀ A : Subgroup H, IsElementaryTwo A → rank A+1 < fixedCodim ρ A := by
  intro hgap A hA
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
  let := hA.2
  have hAm : IsElementaryTwo (A.map j) :=
    ⟨fun hz => hA.1 ((A.map_eq_bot_iff_of_injective hj).mp hz),IsElementaryAbelian.map j⟩
  have hg := hgap (A.map j) hAm
  rw [rank_map_injective j hj A,←fixedCodim_map_equivariant ρ
    (normalizerRepresentation μ) j E he A] at hg
  exact hg

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original nonbinary whole-orbit automizer has no near offenders. -/
theorem sourceOrbit_linear_no_near_offender
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hn : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (A : Subgroup (Automizer D.sourceOrbit)) (hA : IsElementaryTwo A) :
    rank A+1 < fixedCodim (automizerRepresentation D.sourceOrbit) A := by
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
  exact gap_of_marked_pair σ τ (automizerRepresentation W)
    (automizerRepresentation_injective W) i q hq E hE
    (doubledLinear_no_near_offender F hn a hne) A hA

/-- The actual higher Thompson subgroup centralizes the original whole orbit
in every overgroup that normalizes and contains that orbit. -/
theorem sourceOrbit_linear_thompson_one_centralizes
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hn : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (X : Subgroup G) (hWX : D.sourceOrbit ≤ X)
    (hXN : X ≤ normalizer (D.sourceOrbit : Set G)) :
    ChapterB.thompsonJ X 1 ≤ centralizer (D.sourceOrbit : Set G) :=
  thompson_centralizes_of_fixedCodim_gap D.sourceOrbit X hWX hXN
    (D.sourceOrbit_linear_no_near_offender h hd F hn hmodel)

/-- The original local subspace centralizer satisfies the higher-Thompson
hypothesis of E.6.27, independently of the odd-prime displacement bound. -/
theorem sourceOrbit_linear_local_thompson_one
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hn : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (U : Subgroup G) (hUW : U ≤ D.sourceOrbit) :
    ChapterB.thompsonJ (normalizer (L : Set G) ⊓ centralizer (U : Set G)) 1 ≤
      normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) := by
  have hWM : D.sourceOrbit ≤ normalizer (L : Set G) := by
    rw [←D.sourceOrbit_normalizer_eq_of_markedDoubled h hd]
    exact D.sourceOrbit.le_normalizer
  have hWC : D.sourceOrbit ≤ centralizer (U : Set G) :=
    D.sourceOrbit.le_centralizer.trans (centralizer_le hUW)
  refine le_inf ((ChapterB.thompsonJ_le _ 1).trans inf_le_left) ?_
  exact D.sourceOrbit_linear_thompson_one_centralizes h hd F hn hmodel _
    (le_inf hWM hWC) (inf_le_left.trans (D.sourceOrbit_normalizer_eq_of_markedDoubled h hd).ge)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
