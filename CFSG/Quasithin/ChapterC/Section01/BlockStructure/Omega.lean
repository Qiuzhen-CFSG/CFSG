module
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.ProductCentralizer
public import Theory.GroupTheory.PGroup.OmegaCenterIn
public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# The omega-center action above a block

For a block K of H, its intrinsic layer U(K) lies in Ω₁Z(O₂(H)) and is
exactly the commutator of that omega-center with K. If K is normal with
two-group quotient, the omega-center has centralizer O₂(H). Thus the star
quotient in C.2.7 loses no further kernel in the block case.

The first equality uses two-perfection and the subnormal two-core action
lemma; the centralizer statement follows from C.1.11's single-block bound.
Source: Aschbacher--Smith C.1.7--11, pp.123--124, and C.2.7, pp.145--147.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.BlockOmega
variable {G : Type*} [Group G] [Finite G] {K : Subgroup G}

/-- The intrinsic block layer lies in the ambient central omega subgroup. -/
theorem layer_le_omega (hb : IsBlock K) :
    (blockU K).map K.subtype ≤ omegaCenterIn (pCore 2 G) := by
  let U := (blockU K).map K.subtype
  let : IsElementaryAbelian 2 U := hb.short.elementary.map K.subtype
  intro u hu
  apply (mem_omegaCenterIn_iff _ _).mpr
  refine ⟨?_, (le_centralizer_iff.mp hb.core_centralizes_blockU) hu,
    elemPow_eq_one_of_isElementaryAbelian u hu⟩
  exact (map_mono blockU_le_core |>.trans (pCoreIn_le_of_subnormal 2 hb.subnormal)) hu

/-- The moved omega-center is precisely U(K), including its central attachment. -/
theorem omega_commutator (hb : IsBlock K) :
    ⁅omegaCenterIn (pCore 2 G), K⁆ = (blockU K).map K.subtype := by
  apply le_antisymm
  · apply (commutator_mono (map_subtype_le _) le_rfl).trans
    exact commutator_le_core_commutator_of_isSubnormal K (pCore 2 G)
      hb.subnormal hb.short.twoPerfect pCore_isPGroup le_normalizer_of_normal
  · have hi := commutator_isPPerfect_idempotent K (K.pCoreIn 2)
      hb.short.twoPerfect (isPGroup_pCoreIn 2 K)
      (K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))
    have hm : ⁅(blockU K).map K.subtype,K⁆ = (blockU K).map K.subtype := by
      simpa only [pCoreIn,blockU,map_commutator,←MonoidHom.range_eq_map,range_subtype] using hi
    exact hm.symm.le.trans (commutator_mono (layer_le_omega hb) le_rfl)

/-- For a normal block with two-group quotient, the star kernel is exactly O₂. -/
theorem omega_centralizer [K.Normal] (hb : IsBlock K) (hq : IsPGroup 2 (G ⧸ K)) :
    centralizer (omegaCenterIn (pCore 2 G) : Set G) = pCore 2 G := by
  apply le_antisymm
  · exact (centralizer_le (layer_le_omega hb)).trans
      (centralizer_blockU_le_core_of_normal K hb.short.fitting hq)
  · intro x hx v hv
    exact ((mem_omegaCenterIn_iff _ _).mp hv).2.1 x hx |>.symm

end CFSG.Quasithin.ChapterC.BlockOmega
