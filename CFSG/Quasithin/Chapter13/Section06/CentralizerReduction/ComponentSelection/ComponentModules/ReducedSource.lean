module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Applicability.Preparation
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.Source1366
public import CFSG.Quasithin.Chapter6.SourceDefs

/-!
# The reduced module before component invariance

The Sylow fixes the seed and its conjugates generate W_K. The resulting
faithful quotient therefore has trivial two-core. Characteristic two puts
W_K inside the elementary omega-center of O₂(C_G(v)). Identifying the
literal plus kernel with the internal centralizer proves the full reduced
family assertion, including containment and normality, before 13.6.14.
The actual component image is consequently quasisimple.

Source: Aschbacher--Smith, paragraph preceding 13.6.14, printed p.929.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives
universe u
variable {G : Type u} [Group G] [Finite G]

/-- All clauses of B.2.14's reduced-family assertion on the actual W_K. -/
theorem WK_mem_reducedFamily_source (K L T : Subgroup G) (z v : G)
    (hK : K ≤ Gv v)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hzOmega : z ∈ omegaOneCenterAmbient (Tv T v))
    (hf : generalizedFitting (Gv v) = pCore 2 (Gv v)) :
    WK K L T z v ∈ Chapter6.Source.reducedFamily (plusActor K L T v) := by
  have hzT := ((mem_omegaOneCenterAmbient_iff _ _).mp hzOmega).1
  have hWA : WK K L T z v ≤ plusActor K L T v := conjugateSpanBy_le
    (zpowers_le.mpr ((show Tv T v ≤ plusActor K L T v from le_sup_right) hzT))
    ((show Kminus K T v ⊔ Lv L v ≤ plusActor K L T v from le_sup_left).trans
      (plusActor K L T v).le_normalizer)
  have hN := normal_subgroupOf_of_le_normalizer
    (plusActor_normalizes_WK K L T z v hL hz)
  refine ⟨hWA, wk_elementary K L T z v hK hSylow hzOmega hf, hN, ?_⟩
  let := hN
  have hk : (plusConjugation K L T z v hL hz).ker =
      centralizer ((WK K L T z v).subgroupOf (plusActor K L T v) :
        Set (plusActor K L T v)) := by
    rw [plusConjugation_ker]
    ext x
    constructor
    · intro hx y hy
      exact Subtype.ext (hx y hy)
    · intro hx y hy
      exact congrArg Subtype.val (hx ⟨y, hWA hy⟩ hy)
  let e := QuotientGroup.quotientMulEquivOfEq hk
  have hcore := plus_twoCore_eq_bot K L T z v hK hL hz hSylow
  change pCore 2 (plusActor K L T v ⧸ (plusConjugation K L T z v hL hz).ker) = ⊥ at hcore
  rw [← pCore_map_iso (p := 2) e, hcore, Subgroup.map_bot]

/-- Quasisimplicity of the literal plus component needs no invariance premise. -/
theorem plusImage_K_quasisimple_source (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hK : K ∈ Yz L T z v)
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v)) :
    IsQuasisimple (plusImage K L T z v hL hz K) :=
  plusImage_K_quasisimple K L T z v hL hz hK
    (plus_twoCore_eq_bot K L T z v hK.1.1 hL hz hSylow)

open A5Module ComponentReduction InitialSieve
variable {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}

/-- The seed's Sylow omega-center membership on the original marking. -/
theorem markedZ_mem_Tv_omega (d : FlagSource T L V V₁ V₂) :
    markedZ d.flag.module ∈ omegaOneCenterAmbient (Tv (T : Subgroup G) (markedV d.flag.module)) := by
  obtain ⟨hzT, hz2, hzC⟩ := (mem_omegaOneCenterAmbient_iff _ _).mp d.flag.z_central
  exact (mem_omegaOneCenterAmbient_iff _ _).mpr
    ⟨⟨hzT, markedZ_mem_Gv d.flag.module⟩, hz2, fun t ht => hzC t ht.1⟩

/-- The earlier T-invariance of L restricts to the actual residual L_v. -/
theorem markedTv_normalizes_Lv (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module)) :
    Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G) := by
  have hn : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer ((L ⊓ Gv (markedV d.flag.module) : Subgroup G) : Set G) :=
    (inf_le_inf earlier.T_normalizes_L (Gv _).le_normalizer).trans
      inf_normalizer_le_normalizer_inf
  exact hn.trans (normalizer_le_normalizer_characteristic_image
    (L ⊓ Gv (markedV d.flag.module)) (pResidual 2 ↥(L ⊓ Gv (markedV d.flag.module))))

/-- Full reduced-family membership with the 13.6.6 source theorem supplying
characteristic two. The contrary containment hypothesis is unnecessary here. -/
theorem WK_mem_reducedFamily_original_source
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hcounter : IsA5Counterexample G) (hfusion : ControlsFusionOfZ d.flag.module)
    (K : Subgroup G) (hK : K ≤ Gv (markedV d.flag.module)) :
    WK K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) ∈
      Chapter6.Source.reducedFamily (plusActor K L (T : Subgroup G) (markedV d.flag.module)) := by
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier hcounter hfusion
  have hz := markedZ_mem_Tv_omega d
  have hfix : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G) := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr
      (((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht)
  exact WK_mem_reducedFamily_source K L (T : Subgroup G) _ _ hK
    (markedTv_normalizes_Lv d V₃ earlier) hfix
    ⟨c.reductions.centralizerSylow, c.reductions.sylow_image⟩ hz
    (generalizedFitting_eq_pCore_of_earlier_source d V₃ earlier hG hm hcounter hfusion)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
