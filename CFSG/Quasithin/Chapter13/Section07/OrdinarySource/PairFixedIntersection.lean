module
public import CFSG.Quasithin.Chapter13.Section07.PairFixedIntersection.Source
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalLocal
/-!
# The original paired fixed intersection under Hypothesis12.2.1

The natural module's TI theorem makes a normal component escape M under
Hypothesis12.2.1 itself. Apply that escape to the literal chosen conjugator
and paired quotient geometry. This removes the stronger universal
structural hypothesis from the13.7.17 application while retaining the
actual earlier13.7.15–16 component normality and fixed-space conclusions.

Source: Aschbacher–Smith13.7.17, printed p.944.
-/
public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.OrdinarySource
open Section08.SourceCompletion ChapterF.Section09.Setup
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d
/-- Both original13.7.17 conclusions on the same conjugator used to choose
the offender and component, with ordinary component escape discharged. -/
theorem pair_fixed_intersection_of_normal_component
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (J : Subgroup H) (hJ : J.IsCComponent) (hn : J.Normal)
    (hc : J.map H.subtype ≤ centralizer
      ((Section08.Source.UH H V₃ ⊓ centralizer (H.pCoreIn 2 : Set G) : Subgroup G) : Set G))
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hs : (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) g) ^ 2 = 1)
    (hout : ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃) :
    let U := Section08.Source.UH H V₃
    let U₀ := U ⊓ centralizer (H.pCoreIn 2 : Set G)
    let E := Section08.Source.VH H V ⊓ conjugate (Section08.Source.VH H V) (g : G)
    let A := conjugate (Section08.Source.VH H V) (g : G) ⊓
      (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2
    U₀ ⊓ conjugate U (g : G) = ⊥ ∧ E ⊓ U₀ = V₁ ∧
      (U₀ ≤ ⁅U, A⁆ ⊔ V₃ → U₀ = V₁) := by
  let K := J.map H.subtype
  have he : K.subgroupOf H = J := comap_map_eq_self_of_injective H.subtype_injective J
  have hKH : K ≤ H := map_subtype_le J
  have hK : (K.subgroupOf H).IsCComponent := he.symm ▸ hJ
  have hKn : H ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKH).mp (he.symm ▸ hn)
  obtain ⟨eL⟩ := nonabelian_source_ordinary d h hU hV
  have hKM := PlusAction.Original.ordinary_normal_component_not_le_local d h1221 h eL hKH hK hKn
  have hHG : H ≤ G₁ := by
    rw [d.first_normalizer]
    exact h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)
  have hu := source_pair_maximal_uniqueness d h1221
  have hnon := seed_noncentral_on_local_core h hHG hne
  have hdis := pair_fixed_disjoint_conjugate d h hU hV hnon hu hc hKM g hout
  have hE := pair_intersection_fixed_eq_point d h hU hV hnon hu hc hKM g hs hout
  refine ⟨hdis, hE, ?_⟩
  intro hbound
  have hcomm := pair_seed_actor_commutator_le_intersection d h hU g
  have hseed := (pair_seed_complement d h hU g hs hout).2.2.2.2
  apply le_antisymm
  · exact (le_inf (hbound.trans (sup_le hcomm hseed)) le_rfl).trans hE.le
  · exact le_inf (h.point_lt.le.trans (le_conjugateSpanBy V₃ H))
      (le_centralizer_iff.mp ((pCoreIn_le 2 H).trans h.H_centralizes))

end CFSG.Quasithin.Chapter13.Section07.OrdinarySource
