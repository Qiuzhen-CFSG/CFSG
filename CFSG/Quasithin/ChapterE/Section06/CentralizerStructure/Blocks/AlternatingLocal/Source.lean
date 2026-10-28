module
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.AlternatingLocal
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingFiveCentralizer

/-!
# The intrinsic central quotient of an original alternating-five block

For an actual A₅ block, the projective natural module eliminates the fixed
kernel in U(L). The C.1.13 centralizer decomposition then gives
O₂(L) = U(L) Z(L), retaining the possible central factor. These two source
consequences discharge the natural-lift, equivariance, and core-decomposition
inputs of the Sylow omega-center calculation: Ω₁(Z(P)) modulo its intersection
with Z(L) has order two for every Sylow two-subgroup P of L.

Source: Aschbacher–Smith, The Classification of Quasithin Groups, C.1.13(c),
printed pp.124–125, and the A₅ case in E.6.7, printed p.246.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]

theorem IsAlternatingBlock.core_eq_module_sup_center {L : Subgroup G}
    (h : IsAlternatingBlock L 5) : pCore 2 L = blockU L ⊔ center L := by
  have hc : center L ≤ pCore 2 L := by
    have hn : Group.IsNilpotent (center L) := by
      refine ⟨1, ?_⟩
      rw [Subgroup.upperCentralSeries_one_eq_top_iff]
      infer_instance
    rw [← h.2.1.fitting]
    exact (show center L ≤ fittingSubgroup L from
      le_sSup ⟨inferInstance, hn⟩).trans (fitting_le_generalizedFitting L)
  apply (map_injective L.subtype_injective)
  rw [Subgroup.map_sup]
  have hh := h.normalizer_twoCore_eq_module_sup_centralizer le_rfl L.le_normalizer
  change (pCore 2 L).map L.subtype = _ at hh
  rw [hh]
  congr 1
  apply le_antisymm
  · rintro x ⟨⟨l, hl, rfl⟩, hx⟩
    refine ⟨l, ?_, rfl⟩
    exact mem_center_iff.mpr (fun y => Subtype.ext (hx y y.property))
  · rintro x ⟨l, hl, rfl⟩
    refine ⟨mem_map_of_mem L.subtype (hc hl), ?_⟩
    intro y hy
    exact congrArg Subtype.val (mem_center_iff.mp hl ⟨y,hy⟩)

end CFSG.Quasithin.ChapterC
namespace CFSG.Quasithin.ChapterE.Section06.AlternatingLocal
open ChapterC
variable {G : Type*} [Group G] [Finite G]

theorem a5_omega_center_quotient_card_source {L : Subgroup G}
    (h : IsAlternatingBlock L 5) (P : Sylow 2 L) :
    let Z := Stellmacher.omegaOneCenterAmbient (P : Subgroup L)
    Nat.card (Z ⧸ (center L).subgroupOf Z) = 2 := by
  obtain ⟨ρ,⟨m⟩,hρ⟩ := h.2.2
  have hq : Function.Bijective (QuotientGroup.mk' (blockFixed L)) :=
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk',h.blockFixed_eq_bot]),
      QuotientGroup.mk'_surjective _⟩
  let eU := (MulEquiv.ofBijective (QuotientGroup.mk' (blockFixed L)) hq).trans m.moduleIso
  apply a5_omega_center_quotient_card h m.quotientIso eU ?_ h.core_eq_module_sup_center P
  intro l u
  change (m.moduleIso (QuotientGroup.mk' _ (blockConjugate L l u))).toAdd = _
  rw [m.intertwining]
  exact hρ (m.quotientIso (QuotientGroup.mk' _ l)) (eU u)

end CFSG.Quasithin.ChapterE.Section06.AlternatingLocal
