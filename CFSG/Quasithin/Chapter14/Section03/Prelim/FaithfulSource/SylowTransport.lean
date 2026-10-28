module
public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource.Contract
public import CFSG.Quasithin.ChapterA.Section04.ReducedWitness.Intrinsic

/-!
# Changing the Sylow subgroup in the earlier faithful classification

Conjugacy of ambient Sylow subgroups transports the canonical local family,
its inclusion-maximal members, relative normality and the intrinsic module.
The quotient equivalence uses the actual two-core in both coordinates.
Thus the earlier classification at one fixed Sylow applies at every Sylow
of the same simple QTKE group, without assuming a universal classification.

Source: Aschbacher–Smith 14.3.4(1–2), printed p.990; used at the Sylow T_A
in the proof of 14.7.6, printed p.1045, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.Components
open ChapterA.Section04
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

/-- The earlier faithful classification at one ambient Sylow transports to
any other ambient Sylow, retaining the exact local family and two-cores. -/
theorem EarlierFaithfulClassification.sylow_transport
    (hG : IsSimpleQTKE κ G) (T S : Sylow 2 G)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G)) :
    EarlierFaithfulClassification G (S : Subgroup G) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G S T
  let e := MulAut.conj g
  have hST : (S : Subgroup G).map e.toMonoidHom = (T : Subgroup G) :=
    congrArg Sylow.toSubgroup hg
  intro C hC hCf
  have hCL : C.map e.toMonoidHom ∈ Chapter1.L G (T : Subgroup G) := by
    rw [←hST]
    exact (Chapter1.mem_L_map_iff e.toMonoidHom e.injective).mpr hC
  have hCF : IsFaithfulSignalizerType (C.map e.toMonoidHom) := by
    refine ⟨Chapter1.Section02.Adequate.mem_L_isSignalizerType T (hG.evenCharacteristic T) hCL,?_⟩
    rw [intrinsicSignalizerModule_map_of_injective e.toMonoidHom e.injective]
    exact fun hz => hCf.2 (((intrinsicSignalizerModule C).map_eq_bot_iff_of_injective e.injective).mp hz)
  obtain ⟨hmodel,hn,hmax⟩ := faithful _ hCL hCF
  let c := C.equivMapOfInjective e.toMonoidHom e.injective
  let q := QuotientGroup.congr (pCore 2 C) (pCore 2 (C.map e.toMonoidHom)) c (pCore_map_iso 2 c)
  refine ⟨hmodel.imp (fun ⟨a⟩ => ⟨q.trans a⟩) (fun ⟨a⟩ => ⟨q.trans a⟩),?_,?_⟩
  · apply (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    have hh := (normal_subgroupOf_iff_le_normalizer le_sup_left).mp hn
    rw [←hST,←Subgroup.map_sup,←map_normalizer_eq_of_bijective C e.bijective] at hh
    exact (map_le_map_iff_of_injective e.injective).mp hh
  · rw [←hST] at hmax
    exact (Chapter1.mem_LStar_map_iff e).mp hmax

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.Components
