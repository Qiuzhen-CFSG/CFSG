module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientTitsNonFF
public import Theory.SpecificGroups.Tits.CoreQuotient
public import Theory.GroupTheory.ReducedNormal.SimpleCoreOmega
public import Stellmacher.CentralizerQuotientRepresentation

/-!
# Tits components centralize the ambient omega-center

The literal centralizer-quotient action on the ambient omega-center is
faithful.  If an actual Tits component moved that center, the Thompson
inequality would produce an FF offender in this action.  The marked Tits
quotient has no such offender, so the component centralizes the center.

This is the omega movement cut in Aschbacher--Smith 6.1.4, pp.665--666.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open PerfectCentralCovering
variable {H : Type*} [Group H] [Finite H]

/-- An actual Tits component cannot move the omega-center of the ambient
 two-core when the ambient Sylow Thompson subgroup is not in that core. -/
theorem tits_component_centralizes_omega
    (C S : Subgroup H) [C.Normal]
    (hC : C.IsCComponent)
    (hq : IsQuasisimple (C ⧸ pCore 2 C))
    (hS : IsPGroup 2 S)
    (hgen : C ⊔ S = ⊤)
    (hWS : omegaOneCenterAmbient (pCore 2 H) ≤ S)
    (e : coreCentralQuotient C ≃* Tits.ParrottGroup)
    (hJ : ¬ elementaryAbelianMaxJ S ≤ pCore 2 H) :
    ⁅omegaOneCenterAmbient (pCore 2 H), C⁆ = ⊥ := by
  let : Group.IsPerfect C := hC.perfect
  let : IsQuasisimple (C ⧸ pCore 2 C) := hq
  let W := omegaOneCenterAmbient (pCore 2 H)
  let : IsElementaryAbelian 2 W := by
    exact omegaOneCenterAmbient_elementaryAbelian _
  let : W.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    intro b _
    rw [mem_normalizer_iff_map_conj_eq]
    change W.map (MulAut.conj b).toMonoidHom = W
    rw [← omegaOneCenterAmbient_map_injective _ (MulAut.conj b).injective]
    congr 1
    exact mem_normalizer_iff_map_conj_eq.mp
      ((le_normalizer_of_normal : (⊤ : Subgroup H) ≤
        normalizer (pCore 2 H : Set H)) (mem_top b))
  let q := QuotientGroup.mk' (pCore 2 H)
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective _
  by_contra hmove
  have hmove' : ⁅W, C⁆ ≠ ⊥ := hmove
  have hz : center (C ⧸ pCore 2 C) = ⊥ :=
    PerfectCentralCovering.center_eq_bot_of_centralQuotientEquiv
      Tits.CentralCoverLifting.CompatibleGenerators.universalProjection_ker_eq_bot e
  obtain ⟨hker, hred⟩ := omegaCenter_reduced_of_simple_component C S hC hz hS hgen hmove'
  have hkerW : centralizer (W : Set H) = pCore 2 H := by
    simpa only [W] using hker
  have hker' : q.ker = centralizer (W : Set H) := by
    rw [QuotientGroup.ker_mk', hkerW]
  have hJ' : ¬ elementaryAbelianMaxJ S ≤ q.ker := by
    intro hh
    apply hJ
    have hh' : elementaryAbelianMaxJ S ≤ centralizer (W : Set H) := by
      rw [← hker']
      exact hh
    exact hkerW ▸ hh'
  let ρ : Representation (ZMod 2) (H ⧸ pCore 2 H) (Additive W) :=
    NormalElementaryQuotient.representation W q hqsurj hker'
  have hff : IsFFModule ρ :=
    NormalElementaryQuotient.isFFModule_of_thompson_not_le W q hqsurj hker'
      S hWS hJ'
  let N : Subgroup (H ⧸ pCore 2 H) := C.map q
  have hJC : IsPGroup 2 (H ⧸ C) := by
    exact isPGroup_quotient_of_sup_eq_top C S hS hgen
  obtain ⟨f, _, hcN⟩ := Tits.marked_core_quotient C hJC e
  have hNnormal : N.Normal := (inferInstance : C.Normal).map q hqsurj
  let : N.Normal := hNnormal
  have hf : Function.Injective ρ := NormalElementaryQuotient.representation_injective W q hqsurj hker'
  exact (normal_tits_not_ff ρ N f hcN hf) hff

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
