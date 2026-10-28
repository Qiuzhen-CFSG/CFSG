module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.PointCommutator
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.Quasisimple
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.LocalAlternatives.SevenSource

/-!
# Both clauses of 14.7.68 from the original local inputs

The original A₅ module theorem gives the point commutator and two
noncentral chief factors. The actual nonquasisimple component is short
with its moved subgroup of order 64; the resulting bound of one chief
factor is impossible. In the quasisimple case the checked marked Ru
normalizer calculation gives the Sylow contradiction.

Using 14.7.67(4), the characteristic subgroup and source component
selection now prove C_G(u) ≤ H. The literal residual recovers every
conjugator of U₀ containing u, and gives zᴳ ∩ U₀ = {z}. Thus all clauses
use the same original G,T,L,V,F and the same quotient/action maps.

The only earlier inputs here are original 13.3.2(3) at G,T,L and the
14.7.67(4) residual-normalizer and maximality conclusions. Their final
discharge remains with qt-d-14775-source, using qt-d-1332-source and the
proved natural-point Baumann and weak-closure branches. No universal
Structural1222, C.2.7, fixed-component alternatives or model premise is
required. This does not yet finish source 14.7.75.
Source: AS 14.7.67–68, printed pp.1070–1072.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data
open Chapter12.Section08 Chapter13.Section03.SourceCompletion
open Chapter1.RadicalExclusions.ModelReduction
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

/-- The actual nonquasisimple component has incompatible chief-factor bounds. -/
theorem false_of_nonquasisimple_fixedComponent_from_original_modules_at
    (five : OriginalAlternatingFiveModules1332At T L)
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu) : False := by
  have hcomm := d.U_core_commutator_eq_point_of_original_modules_at five
  have hs := d.fixedComponent_short_from_source u h
  obtain ⟨s,hs0,hs1,hs2⟩ := d.exists_K_two_chief_of_point_commutator hcomm
  have hb := AlternatingBound.count_le_one_of_embedding hs
    (d.KToFixedComponent u h) (inclusion_injective h.larger.le)
    (d.fixedComponent_C27_core_alternatingSeven u h).some d.KCoreA5 (K_twoPerfect F)
    (d.fixedComponent_C27_module_bound_of_short u h hs) s hs0 hs1
  omega

/-- Centralizer containment on the literal source fixed elements. -/
theorem fixedCentralizer_le_H_from_original_modules_at
    (five : OriginalAlternatingFiveModules1332At T L)
    (hNK : normalizer (K F : Set G) = F.H) (hmax : IsMaximalTwoLocal F.H)
    (u : F.U) (hu : (u : G) ∈ d.U₀) (hne : (u : G) ≠ 1)
    (hfix : d.FixedModuloPoint u) : d.fixedCentralizer u ≤ F.H := by
  by_contra hout
  have hcomm := d.U_core_commutator_eq_point_of_original_modules_at five
  have hsyl := d.fixedSylow_isSylow_fivePoint_source hcomm u hu hne hfix hmax
  obtain ⟨Lu,hLu,hc,hKLu,hn⟩ := d.exists_fixedComponent_of_known_simple_source u hu hne hfix hsyl
  have hLH := d.fixedComponent_not_le_H u hu hNK hout hLu hc hKLu hn
  have hlt : K F < Lu := lt_of_le_of_ne hKLu (fun he => hLH (he ▸ K_le_H F))
  by_cases hqs : IsQuasisimple Lu
  · exact d.false_of_quasisimple_fixedComponent_from_chosen u hu hne hfix hNK hmax
      hsyl Lu hLu hc hn hlt hLH hqs hcomm
  · exact d.false_of_nonquasisimple_fixedComponent_from_original_modules_at five u
      (d.fixedComponent_case_of_source u hu hne hfix hmax hNK hsyl hLu hc hlt hn hLH hqs)

/-- Both original source clauses, including uniqueness among all conjugates
of U₀ containing the specified nonidentity fixed element. -/
theorem source_lemma_14_7_68_at
    (five : OriginalAlternatingFiveModules1332At T L)
    (hNK : normalizer (K F : Set G) = F.H) (hmax : IsMaximalTwoLocal F.H) :
    {x : G | IsConj d.z x} ∩ (d.U₀ : Set G) = {d.z} ∧
      ∀ u : F.U, (u : G) ∈ d.U₀ → (u : G) ≠ 1 → d.FixedModuloPoint u →
        centralizer ({(u : G)} : Set G) ≤ F.H ∧
          ∀ g : G, (u : G) ∈ conjugate d.U₀ g → conjugate d.U₀ g = d.U₀ := by
  refine ⟨d.fusion_z_of_normalizer_K hNK, ?_⟩
  intro u hu hne hfix
  have hc := d.fixedCentralizer_le_H_from_original_modules_at five hNK hmax u hu hne hfix
  exact ⟨hc,fun g hg => d.U₀_conjugate_eq_of_centralizer_le hNK u g hc hg⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
open Chapter12.Section08 CriticalFusion.Source Chapter13.Section03.SourceCompletion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

/-- Supply the literal local C.2.7 contract from the ambient module source. -/
theorem fixedComponentAlternatives_from_original_modules_at
    (five : OriginalAlternatingFiveModules1332At T L) : FixedComponentAlternatives d := by
  intro u Lu h
  exact (d.false_of_nonquasisimple_fixedComponent_from_original_modules_at five u h).elim

/-- The original classification interface receives all three C.2.7 clauses
on the actual relatively normal fixed components. -/
theorem fixedComponentClassification_from_original_modules_at
    (five : OriginalAlternatingFiveModules1332At T L) : FixedComponentClassification d :=
  fixedComponentClassification_of_alternatives d
    (fixedComponentAlternatives_from_original_modules_at d five)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
