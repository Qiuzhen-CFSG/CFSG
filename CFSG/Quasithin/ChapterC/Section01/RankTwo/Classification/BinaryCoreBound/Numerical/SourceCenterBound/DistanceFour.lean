module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.Numerical.SourceCenterBound.DistanceFour.Cover
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup

/-!
# The source center bound for the binary distance-four branch

From LocalSource, CommonFacts, RadiusFacts and b=4, source span recognition
constructs the starred quotient. The descended cover has dimension at most
eight, and U_alpha has order eight, so the core has order at most 2048.
Its quotient by its center has order 64. Hence the center has order at most
32, which is the sufficient bound needed by the Chapter C numerical route.

The final theorem applies this result through InputSetup.coreEquiv to the
original commutator core. Construction of the earlier common/radius facts
and the other distance branch belong to the enclosing numerical assembly.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6) and (4.6.12),
pp.908--912. This proves the sufficient center bound used by Chapter C,
not the stronger exact-center conclusion of the full source theorem.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterC.BinaryMS.Numerical.SourceCenterBound.DistanceFour

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open MS93 MS93.DistanceFour

private theorem card_of_surjective {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Surjective f) :
    Nat.card A = Nat.card f.ker * Nat.card B := by
  rw [← f.ker.card_mul_index, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hf,
    Subgroup.card_top]

universe u
variable {M : Type u} [Group M] [Finite M] {L R : Subgroup M}
  (source : LocalSource L R) {geometry : Geometry R}
  (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
  (hb : geometry.b R = 4)

local notation "C" => core R (alpha R)
local notation "Z" => Z R (alpha R)
local notation "U" => U R (alpha R)

include common radius hb in
/-- The exact descended covering kernel may be nonzero, but has dimension
at most two. This gives the complete source b=4 center bound. -/
theorem source_center_bound : Nat.card (center C) ≤ 32 := by
  obtain ⟨⟨q⟩, hSC⟩ := LargeBranch.fullSpans source common radius hb
    (LargeBranch.RankOne.source_spanRecognition common radius hb)
  obtain ⟨d⟩ := SmallBranch.exists_quotientAction source geometry common radius
  have hu : Nat.card U = 8 :=
    (Nat.card_congr common.natural.equiv.toEquiv).trans (by
      norm_num [Nat.card_eq_fintype_card])
  have hdker : Nat.card d.projection.ker = 8 := by
    rw [d.kernel]
    exact (Nat.card_congr (subgroupOfEquivOfLe
      (MS93.DistanceFour.U_le_core source geometry common)).toEquiv).trans hu
  let _ : Module.Finite (ZMod 2) d.Space := Module.Finite.of_finite
  have hd : Nat.card (Multiplicative d.Space) ≤ 256 := by
    change Nat.card d.Space ≤ 256
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
      (quotient_dimension_le_eight source common radius q hSC d)).trans_eq (by decide)
  have hc : Nat.card C ≤ 2048 := by
    rw [card_of_surjective d.projection d.onto, hdker]
    exact (Nat.mul_le_mul_left 8 hd).trans_eq (by decide)
  have hcenter : (coreProjection source common radius q).ker = center C := by
    apply map_injective (C).subtype_injective
    rw [coreProjection_kernel, center_core_image source common radius hb,
      subgroupOf_map_subtype, inf_comm]
  have hcard : Nat.card C = Nat.card (center C) * 64 := by
    rw [card_of_surjective (coreProjection source common radius q)
      (coreProjection_onto source common radius q hSC), hcenter]
    congr 1
    norm_num [Linear.W, Nat.card_eq_fintype_card]
  omega

/-- Apply the bound to the original commutator core through the constructed
source setup's actual isomorphism. Common/radius construction and the split
between b=4 and b>4 remain with the original numeric assembly owner. -/
theorem inputSetup_center_bound
    {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L T : Subgroup J}
    {h : Input κ L T} (s : InputSetup h)
    (common : CommonFacts s.reduction.radical s.source s.geometry)
    (radius : RadiusFacts s.reduction.radical s.geometry)
    (hb : s.geometry.b s.reduction.radical = 4) :
    Nat.card (center (commutatorCore L)) ≤ 32 := by
  have hc := source_center_bound s.source common radius hb
  rw [Nat.card_congr (Subgroup.centerCongr s.coreEquiv).toEquiv] at hc
  exact hc

end CFSG.Quasithin.ChapterC.BinaryMS.Numerical.SourceCenterBound.DistanceFour
