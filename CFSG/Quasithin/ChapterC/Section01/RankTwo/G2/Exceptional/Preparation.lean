module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.ExceptionalModule
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.Geometry

/-!
# The exceptional MS pair on its generated group

The root-eight input gives the two-group edge and core containment used by
MS93's holomorph argument. The relative component is the two-residual, and
its actual core quotient is the derived binary G₂ group. These inputs do
not include a block, critical-distance, or Frattini conclusion.

This adapts the preparation in Chapter15's MarkedMS.G2Reconstruction to
MS2(b), preserving that earlier MS2(a) interface. Source: AS C.1.31--32,
pp.135--136; MS93 (2.0)--(3.2).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.G2Exceptional
universe u
variable {G : Type u} [Group G] {κ : GroupClass.{u}} {L R : Subgroup G}

abbrev Pair (κ : GroupClass.{u}) (L R : Subgroup G) :=
  Input κ (L.subgroupOf (L ⊔ R)) (R.subgroupOf (L ⊔ R))

namespace Reconstruction
variable [Finite G]
local notation "H" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf (L ⊔ R)
local notation "T" => R.subgroupOf (L ⊔ R)

omit [Finite G] in
theorem relative_product (h : Pair κ L R) :
    ∀ g : H, ∃ k ∈ K, ∃ t ∈ T, k * t = g := h.product

omit [Finite G] in
theorem edge_two_group (h : Pair κ L R) : IsPGroup 2 T := h.radical_two_group

omit [Finite G] in
theorem core_le_edge (h : Pair κ L R) : pCore 2 H ≤ T := h.core_le_radical

theorem relative_residual (h : Pair κ L R) : pResidual 2 H = K := h.component_residual

theorem relative_normal (h : Pair κ L R) : (K).Normal := h.component_normal

theorem relative_twoPerfect (h : Pair κ L R) : IsPPerfect 2 K := h.component_twoPerfect

theorem core_self_centralizing (h : Pair κ L R) :
    centralizer (pCore 2 H : Set H) ≤ pCore 2 H := h.core_self_centralizing

theorem edge_ne_bot (h : Pair κ L R) : T ≠ ⊥ := h.radical_ne_bot

omit [Finite G] in
theorem edge_characteristic (h : Pair κ L R) : MSCharacteristicCondition T := h.characteristic

def relativeCoreEquiv (_h : Pair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    (K ⧸ pCore 2 K) ≃* commutator (Atlas.G2.Model (ZMod 2)) :=
  (QuotientGroup.congr _ _ (show K ≃* L from subgroupOfEquivOfLe le_sup_left)
    (pCore_map_iso 2 (show K ≃* L from subgroupOfEquivOfLe le_sup_left))).trans e

omit [Finite G] in
theorem relativeCoreEquiv_apply (h : Pair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2))) (k : K) :
    relativeCoreEquiv h e (QuotientGroup.mk' (pCore 2 K) k) =
      e (QuotientGroup.mk' (pCore 2 L) ((subgroupOfEquivOfLe le_sup_left) k)) := rfl

theorem intrinsic_core_eq (h : Pair κ L R) :
    ⁅pCore 2 H,K⁆ = (blockU K).map (K).subtype := by
  let := relative_normal h
  exact MSCentralOrbit.commutatorCore_eq_intrinsic K (relative_twoPerfect h)

end Reconstruction

-- The exact core quotient, without introducing a central quotient convention.
theorem Pair.core_quasisimple_of_centralCore [Finite G]
    (h : Pair KnownSimple.IsKnownSimple L R)
    (e : (L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    IsQuasisimple (L ⧸ pCore 2 L) := by
  let := h.quotientComponent_structure.2.2.1
  exact IsQuasisimple.of_mulEquiv (h.quotientComponentEquiv.trans e.symm)
end CFSG.Quasithin.ChapterC.G2Exceptional
