module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FivePointCharacteristic.Source
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Characteristic.Preparation
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Overgroups
/-!
# The original fixed-centralizer characteristic witness

Identify the two-residual of K C_T(u) with the original C-component K and
transport its actual A₅ quotient. The five-point map has two-group kernel.
The proved point-commutator obstruction excludes shortness, so the specialized
C.1.26 source produces a nontrivial characteristic subgroup of the original
C_T(u), normal in K C_T(u). Its existing normalizer argument proves that this
same C_T(u) is Sylow in C_G(u). No universal pushing-up input remains.
Source: Aschbacher–Smith 14.7.68(2), pp.1071–1072, using C.1.26, p.132.
-/
public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

theorem fixedCharacteristic_fivePoint_source
    (hUQ : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (u : F.U) (hu : (u : G) ∈ d.U₀) (hne : (u : G) ≠ 1)
    (hfix : d.FixedModuloPoint u) (hmax : IsMaximalTwoLocal F.H) :
    Nonempty (d.FixedCharacteristicWitness u) := by
  have hsyl : Chapter1.IsSylowIn 2 (d.fixedSylow u) (d.fixedJoin u) :=
    (d.K_mem_fixedLocalFamily u hu hfix).2.1
  obtain ⟨P, hP⟩ := hsyl
  have hres : (pResidual 2 (d.fixedJoin u)).map (d.fixedJoin u).subtype = K F :=
    embedded_pResidual_join_pGroup (K F) (d.fixedSylow u) (K_twoPerfect F)
      (T.isPGroup'.to_le inf_le_left)
      (inf_le_left.trans ((F.invariant 1).trans (H_normalizes_K F)))
  have heq : pResidual 2 (d.fixedJoin u) = (K F).subgroupOf (d.fixedJoin u) := by
    apply map_injective (d.fixedJoin u).subtype_injective
    rw [hres, map_subgroupOf_eq_of_le (show K F ≤ d.fixedJoin u from le_sup_left)]
  have hc : (pResidual 2 (d.fixedJoin u)).IsCComponent :=
    heq.symm ▸ (d.K_mem_fixedLocalFamily u hu hfix).1
  let eK : pResidual 2 (d.fixedJoin u) ≃* K F :=
    (MulEquiv.subgroupCongr heq).trans
      (subgroupOfEquivOfLe (show K F ≤ d.fixedJoin u from le_sup_left))
  let eL := (QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)).trans d.K_quotient_equiv_A5
  have hf : IsPGroup 2 (d.fixedJoinMap u).ker := by
    rw [d.fixedJoinMap_ker u hu hfix]
    exact pCore_isPGroup
  have hshort : ¬ ChapterC.IsShort (pResidual 2 (d.fixedJoin u)) :=
    fun h => d.K_not_short_of_point_commutator hUQ (h.of_mulEquiv eK)
  obtain ⟨A,hA,hneA,hn⟩ := ChapterC.RankOne.FivePointCharacteristic.exists_normal_characteristic
    (d.fixedJoin_sqtk u hu hne) P (d.fixedJoin_minimalParabolic u hu hfix P)
    (d.fixedJoin_fitting u hu hfix hmax) hc eL (d.fixedJoinMap u) hf hshort
  let e : P ≃* d.fixedSylow u :=
    ((P : Subgroup (d.fixedJoin u)).equivMapOfInjective (d.fixedJoin u).subtype
      (d.fixedJoin u).subtype_injective).trans (MulEquiv.subgroupCongr hP)
  let A' := A.map e.toMonoidHom
  have he : (A'.map (d.fixedSylow u).subtype).subgroupOf (d.fixedJoin u) =
      A.map (P : Subgroup (d.fixedJoin u)).subtype := by
    apply map_injective (d.fixedJoin u).subtype_injective
    rw [map_subgroupOf_eq_of_le (show A'.map (d.fixedSylow u).subtype ≤ d.fixedJoin u from
      (map_subtype_le A').trans le_sup_right), map_map, map_map]
    rfl
  refine ⟨⟨A', ?_, ?_, ?_⟩⟩
  · let := hA
    apply characteristic_iff_le_comap.mpr
    intro a x hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨(MulAut.congr e.symm a) y,
      characteristic_iff_le_comap.mp hA (MulAut.congr e.symm a) hy, ?_⟩
    exact e.apply_symm_apply _
  · exact fun hb => hneA ((A.map_eq_bot_iff_of_injective e.injective).mp hb)
  · exact he.symm ▸ hn

theorem fixedSylow_isSylow_fivePoint_source
    (hUQ : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (u : F.U) (hu : (u : G) ∈ d.U₀) (hne : (u : G) ≠ 1)
    (hfix : d.FixedModuloPoint u) (hmax : IsMaximalTwoLocal F.H) :
    Chapter1.IsSylowIn 2 (d.fixedSylow u) (d.fixedCentralizer u) := by
  obtain ⟨w⟩ := d.fixedCharacteristic_fivePoint_source hUQ u hu hne hfix hmax
  exact w.fixedSylow_isSylow hu hfix hmax
end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
