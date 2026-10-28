module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Setup
public import CFSG.Quasithin.ChapterC.Section01.BlockBasics
public import CFSG.Quasithin.Chapter1.Section01Inheritance
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.PCoreImage

/-!
# Local structure and the non-short obstruction in 14.7.68

For the literal join J = K C_T(u), the earlier fixed-centralizer reductions
supply relative normality in H. Condition (E) at the original maximal two-local
H therefore gives characteristic two for J, and the involution centralizer
supplies its full-known-simple SQTK hypothesis.

The two source identities U = [U,K] and [U,O₂(H)] = V₁ give a direct
commutator form of the dual-chief-factor obstruction. If K were short, its
commutator layer would centralize O₂(K). Since [O₂(H),K] lies in O₂(K),
the three-subgroups lemma would force [U,O₂(H)] = 1, contradicting V₁ ≠ 1.
The two cores are related by intersection, never identified with each other.

The identities remain explicit earlier-source inputs, owned respectively by
qt-14-07-components (14.7.48(2)) and qt-14-05-terminal-duality (14.5.21(2)).
This module does not yet assert existence of the characteristic witness or
the quasisimplicity of the larger component's two-core quotient.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.68(2), pp.1071–1072; 14.7.48(2), p.1064; 14.5.21(2), pp.1019–1020;
C.1.7, p.123.
-/

@[expose] public section
noncomputable section
open Subgroup Representation Theory.GroupTheory
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

namespace Data
variable (d : Data T L V F W)

/-- The source product K Tᵤ, retaining its embedding in G. -/
def fixedJoin (u : F.U) : Subgroup G := K F ⊔ d.fixedSylow u

theorem fixedJoin_le_H (u : F.U) : d.fixedJoin u ≤ F.H :=
  sup_le (K_le_H F) (inf_le_left.trans (F.invariant 1))

theorem fixedJoin_normal (u : F.U) (hu : (u : G) ∈ d.U₀)
    (hfix : d.FixedModuloPoint u) : ((d.fixedJoin u).subgroupOf F.H).Normal := by
  rw [fixedJoin, ← d.fixedCentralizer_inter_H u hu]
  exact d.fixedCentralizer_inter_H_normal u hu hfix

theorem fixedJoin_sqtk (u : F.U) (hu : (u : G) ∈ d.U₀) (hne : (u : G) ≠ 1) :
    IsSQTK KnownSimple.IsKnownSimple (d.fixedJoin u) := by
  have hle : d.fixedJoin u ≤ d.fixedCentralizer u :=
    sup_le (d.K_le_fixedCentralizer u hu) inf_le_right
  exact (IsSQTK.equiv (subgroupOfEquivOfLe hle)).mp
    ((d.fixedCentralizer_sqtk u hne).subgroup
      ((d.fixedJoin u).subgroupOf (d.fixedCentralizer u)))

theorem fixedJoin_characteristicTwo (u : F.U) (hu : (u : G) ∈ d.U₀)
    (hfix : d.FixedModuloPoint u) (hmax : IsMaximalTwoLocal F.H) :
    HasCharacteristicTwo (d.fixedJoin u) := by
  have hH := d.counterexample.qtke.evenCharacteristic T F.H hmax (F.invariant 1)
  exact Chapter1.mem_He_iff.mp (pCoreIn_selfCentralizing_of_subnormal
    (Chapter1.mem_He_iff.mpr hH) (d.fixedJoin_le_H u)
    (d.fixedJoin_normal u hu hfix).isSubnormal)

theorem fixedJoin_fitting (u : F.U) (hu : (u : G) ∈ d.U₀)
    (hfix : d.FixedModuloPoint u) (hmax : IsMaximalTwoLocal F.H) :
    generalizedFitting (d.fixedJoin u) = pCore 2 (d.fixedJoin u) :=
  generalizedFitting_eq_pCore_of_selfCentralizing 2
    (d.fixedJoin_characteristicTwo u hu hfix hmax)

omit [Finite G] in
theorem K_core_eq_inter : (K F).pCoreIn 2 = F.H.pCoreIn 2 ⊓ K F := by
  apply le_antisymm
  · exact le_inf (pCoreIn_mono_of_normalizes (K_le_H F) (H_normalizes_K F))
      (pCoreIn_le 2 _)
  · rw [inf_comm]
    exact inf_pCoreIn_le_of_le 2 (K_le_H F)

include d in
theorem U_le_core : F.U ≤ F.H.pCoreIn 2 := by
  let := d.U_elementary
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 _)
    d.conjugationSection.section_le d.conjugationSection.normalized

include d in
/-- The actual source commutator layers violate the centrality clause of a short group. -/
theorem K_not_short_of_source_commutators
    (hUK : ⁅F.U, K F⁆ = F.U) (hUQ : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    ¬ ChapterC.IsShort (K F) := by
  intro hshort
  have hUKle : F.U ≤ K F := by
    rw [← hUK]
    exact le_normalizer_iff_commutator_le_right.mp
      (d.conjugationSection.section_le.trans (H_normalizes_K F))
  have hUcore : F.U ≤ (K F).pCoreIn 2 := by
    rw [K_core_eq_inter]
    exact le_inf d.U_le_core hUKle
  have hUblock : F.U ≤ (ChapterC.blockU (K F)).map (K F).subtype := by
    change F.U ≤ (⁅pCore 2 (K F), ⊤⁆ : Subgroup (K F)).map (K F).subtype
    rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    conv_lhs => rw [← hUK]
    exact commutator_mono hUcore le_rfl
  have hcentral : F.U ≤ centralizer ((K F).pCoreIn 2 : Set G) :=
    hUblock.trans ((map_mono hshort.central).trans
      (map_centralizer_le_centralizer_image (pCore 2 (K F)) (K F).subtype))
  have hQK : ⁅F.H.pCoreIn 2, K F⁆ ≤ (K F).pCoreIn 2 := by
    rw [K_core_eq_inter]
    refine le_inf ?_ ?_
    · exact le_normalizer_iff_commutator_le_left.mp
        ((K_le_H F).trans (F.H.le_normalizer.trans
          (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H))))
    · exact le_normalizer_iff_commutator_le_right.mp
        ((pCoreIn_le 2 F.H).trans (H_normalizes_K F))
  have h₁ : ⁅⁅K F, F.H.pCoreIn 2⁆, F.U⁆ = ⊥ := by
    rw [commutator_comm (K F) (F.H.pCoreIn 2), commutator_eq_bot_iff_le_centralizer]
    exact hQK.trans (le_centralizer_iff.mp hcentral)
  have h₂ : ⁅⁅F.H.pCoreIn 2, F.U⁆, K F⁆ = ⊥ := by
    rw [commutator_comm (F.H.pCoreIn 2) F.U, hUQ,
      commutator_eq_bot_iff_le_centralizer]
    exact le_centralizer_iff.mp ((K_le_H F).trans d.H_centralizes_point)
  have hzero := commutator_commutator_eq_bot_of_rotate h₁ h₂
  rw [hUK, hUQ] at hzero
  have hz : d.z ∈ (⊥ : Subgroup G) := hzero ▸ (d.point ▸ mem_zpowers d.z)
  exact d.z_ne_one hz

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
