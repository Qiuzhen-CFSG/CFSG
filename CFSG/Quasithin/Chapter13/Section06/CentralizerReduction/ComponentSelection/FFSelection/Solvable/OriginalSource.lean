module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.KnownSimpleSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.Source1366

/-!
# Original 13.6.13 on the constructed source configuration

The earlier configuration supplies the centralizer Sylow, cubic residual
quotient, and the product decomposition of V_v. Its product orders give
|[V,L_v]| = 4. The proved 13.6.6--9 reduction supplies elementary abelianity
of U_v and nonnormality of V_v under the contrary containment assumption.
These facts discharge every local premise of the solvable exclusion, using
the same marked groups and the full known-simple catalogue.

FlagSource, EarlierLocal, SymmetricSix.ModuleData and the earlier fusion
statements still require their source producers in the section assembly.
Source: Aschbacher--Smith, combined manuscript, 13.6.6--13, pp.927--929.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable
open A5Module ComponentReduction InitialSieve
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}

/-- Solvable exclusion on the same literal groups as the 13.6.6 source theorem. -/
theorem no_solvable_member_original_source
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hcounter : IsA5Counterexample G) (hfusion : ControlsFusionOfZ d.flag.module)
    (hform : FusionPreservesForm d.flag.module)
    (hfailure : ¬ Gv (markedV d.flag.module) ≤ normalizer (V : Set G)) :
    ∀ X ∈ XFamily L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module),
      ¬ Group.IsSolvable X := by
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier hcounter hfusion
  have r := geometric_reduction_of_earlier_source d V₃ earlier hG hm hcounter hfusion
    hform hfailure
  let := r.module_reduced.2.1
  have hz := (mem_omegaOneCenterAmbient_iff (T : Subgroup G) _).mp d.flag.z_central
  have hfix : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G) := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr (hz.2.2 t ht.1)
  have hT : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G) := by
    have hn : Tv (T : Subgroup G) (markedV d.flag.module) ≤
        normalizer ((L ⊓ Gv (markedV d.flag.module) : Subgroup G) : Set G) :=
      (inf_le_inf earlier.T_normalizes_L (Gv _).le_normalizer).trans
        inf_normalizer_le_normalizer_inf
    exact hn.trans (normalizer_le_normalizer_characteristic_image
      (L ⊓ Gv (markedV d.flag.module)) (pResidual 2 ↥(L ⊓ Gv (markedV d.flag.module))))
  have hV : IsPGroup 2 V :=
    T.isPGroup'.of_injective (inclusion d.V_le_T) (inclusion_injective d.V_le_T)
  have hL : Lv L (markedV d.flag.module) ≤ normalizer (V : Set G) :=
    ((map_subtype_le _).trans inf_le_left).trans d.flag.module.normalizes
  have hsmall : Nat.card ↥(⁅V, Lv L (markedV d.flag.module)⁆ : Subgroup G) = 4 := by
    have he := Nat.card_congr c.product.toEquiv
    rw [Nat.card_prod, Nat.card_zpowers, (marked_orders d.flag.module).2,
      Vv_card d.flag.module] at he
    omega
  exact no_solvable_member_knownSimple d.flag.module (T : Subgroup G)
    c.reductions.centralizerSylow c.reductions.sylow_image hfix hT hV hL
    c.residual_card c.span_eq hsmall r.nonnormal
    (hG.involution_centralizer_sqtk (marked_orders d.flag.module).2)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable
