module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.NormalizerSource
public import CFSG.Quasithin.ChapterC.Section06.Thompson.CubicSingle

/-!
# The literal single A₃ model and Thompson source

The original minimal-block configuration constructs the marked C.5 action and escaping conjugator. The single A₃ recognition therefore applies to the actual local group H and Sylow image: Q=U gives S₄, while Q≠U gives C₂ × S₄ and unchanged Thompson subgroup in the chosen index-two overgroup.

Source: Aschbacher–Smith 2.4.5(3), 2.4.6 and C.6.1, printed pp.528–529,165. The final global two-overgroup classification is assembled separately.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter2
open ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_cubic_local_source
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hK : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 3)
    (M₀ : Subgroup G) (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    let R := (d.S : Subgroup d.H).map d.H.subtype
    let U := sourceModule (d.block.map d.H.subtype)
    ChapterB.baumann R = R ∧
      (twoCore d.H = U → Nonempty (d.H ≃* Equiv.Perm (Fin 4))) ∧
      (twoCore d.H ≠ U →
        Nonempty (d.H ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) ∧
        elementaryAbelianMaxJ M₀ = elementaryAbelianMaxJ R) := by
  obtain ⟨c,F,hF,h,x,hx,hnc⟩ := d.single_rankOne_configuration hG T hST hsingle
    (Or.inr hK) M₀ hSM hMT hi
  refine ⟨ChapterC.Section06.cubic_baumann_eq_original c h hK hi x hx hnc,?_,?_⟩
  · intro hsmall
    exact ChapterC.Section06.cubic_small_core_model_from_original c h hK hi x hx hnc hsmall
  · intro hlarge
    exact ⟨(ChapterC.Section06.cubic_large_core_model_from_original c h hK hi x hx hnc hlarge).2,
      ChapterC.Section06.cubic_large_core_thompson_from_original c h hK hi x hx hnc hlarge⟩
end CFSG.Quasithin.Chapter2
