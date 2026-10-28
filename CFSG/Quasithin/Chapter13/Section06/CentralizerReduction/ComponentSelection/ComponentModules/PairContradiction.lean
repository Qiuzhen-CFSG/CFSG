module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.PairBaumannImage
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.PairBorelConstruction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.PairSeedKernel
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.PairBorelObstruction

/-!
# The paired natural contradiction on the original A₅ module

The original two-component join has a two-group kernel. Its paired Borel
normalizes Baum(Tᵥ), hence V by 13.6.5. A seed with nonzero projections in
both natural summands has two-group centralizer. The Borel's two odd tori
therefore contradict the genuine five-point normalizer action on V.

This closes the final Borel step of 13.6.14 with literal plus placement,
paired action, and seed-coordinate inputs. Their producers use 1.2.2 and
B.5.6; no component-invariance premise is used here.
Source: Aschbacher--Smith 13.6.14, pp.929--930.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open A5Module ComponentReduction InitialSieve
open ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}

theorem pair_contradiction_original_source
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hcounter : IsA5Counterexample G) (hfusion : ControlsFusionOfZ d.flag.module)
    (K : Subgroup G)
    [IsElementaryAbelian 2 (WK K L T (markedZ d.flag.module) (markedV d.flag.module))]
    (hK : K ∈ Yz L T (markedZ d.flag.module) (markedV d.flag.module))
    (hn : ¬ Tv T (markedV d.flag.module) ≤ normalizer (K : Set G))
    (hL : Tv T (markedV d.flag.module) ≤ normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv T (markedV d.flag.module) ≤ centralizer ({markedZ d.flag.module} : Set G))
    (hLv : plusImage K L T (markedZ d.flag.module) (markedV d.flag.module) hL hz
      (Lv L (markedV d.flag.module)) ≤
        plusImage K L T (markedZ d.flag.module) (markedV d.flag.module) hL hz
          (Kminus K T (markedV d.flag.module)))
    (F : Type*) [Field F] [Finite F] [Algebra (ZMod 2) F] (hF : 4 ≤ Nat.card F)
    (e : plusImage K L T (markedZ d.flag.module) (markedV d.flag.module) hL hz
      (Kminus K T (markedV d.flag.module)) ≃*
        Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F)
    (f : Additive (WK K L T (markedZ d.flag.module) (markedV d.flag.module)) →ₗ[ZMod 2]
      ((Fin 2 → F) × (Fin 2 → F)))
    (he : ∀ (g : plusImage K L T (markedZ d.flag.module) (markedV d.flag.module) hL hz
        (Kminus K T (markedV d.flag.module))) w,
      f (wkRepresentation K L T (markedZ d.flag.module) (markedV d.flag.module) hL hz g w) =
        SL2NaturalOffenders.naturalPair (F := F) (e g) (f w))
    (hzW : markedZ d.flag.module ∈ WK K L T (markedZ d.flag.module) (markedV d.flag.module))
    (hz₁ : (f (Additive.ofMul ⟨markedZ d.flag.module,hzW⟩)).1 ≠ 0)
    (hz₂ : (f (Additive.ofMul ⟨markedZ d.flag.module,hzW⟩)).2 ≠ 0)
    (hB : plusImage K L T (markedZ d.flag.module) (markedV d.flag.module) hL hz
        (ChapterB.baumann (Tv T (markedV d.flag.module))) =
      plusImage K L T (markedZ d.flag.module) (markedV d.flag.module) hL hz (Tv T (markedV d.flag.module)) ⊓
        plusImage K L T (markedZ d.flag.module) (markedV d.flag.module) hL hz (Kminus K T (markedV d.flag.module))) : False := by
  let z := markedZ d.flag.module
  let v := markedV d.flag.module
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier hcounter hfusion
  have hs : Chapter1.IsSylowIn 2 (Tv T v) (Gv v) :=
    ⟨c.reductions.centralizerSylow,c.reductions.sylow_image⟩
  obtain ⟨P,hP⟩ := hs.restrict (show Tv T v ≤ K ⊔ Tv T v from le_sup_right)
    (sup_le hK.1.1 inf_le_right)
  have hk := joinPlusMap_ker_isTwoGroup_source K L T z v
    (hG.involution_centralizer_sqtk (marked_orders d.flag.module).2) hL hz hK hn
  have hc : Gv v ⊓ normalizer (ChapterB.baumann (Tv T v) : Set G) ≤ normalizer (V : Set G) := by
    rw [←c.reductions.baumann_eq]
    exact c.reductions.normalizer_baumann.trans (c.reductions.local_centralizer.le.trans inf_le_left)
  obtain ⟨B,hBN,hBH,hBC,hcard⟩ := exists_pairBorel_source K L T V z v hK hL hz hk hLv P hP F e hB hc
  have hseed := pair_seed_centralizer_isTwoGroup_source K L T z v hL hz hk F e f he hzW hz₁ hz₂ B hBH hBC
  have ho : Odd (Nat.card F - 1) := by
    let := Fintype.ofFinite F
    have he : Even (Nat.card F) := by
      rw [Nat.card_eq_fintype_card,Nat.even_iff]
      exact FiniteField.even_card_of_char_two (ringChar.eq F 2)
    exact Nat.Even.sub_odd (by omega) he odd_one
  exact pairBorel_card_contradiction_source d B hBN hseed ho (by omega) hcard

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
