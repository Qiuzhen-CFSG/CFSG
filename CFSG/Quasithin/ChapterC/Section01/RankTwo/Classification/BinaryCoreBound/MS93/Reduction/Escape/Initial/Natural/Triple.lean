module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Triple.Composition
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Triple.Radical

/-!
# The initial triple commutator

The residual moves the two-core-fixed space of the actual dual radius module.
The endpoint actor has fixed codimension at most one, so its entire displacement
bound is consumed on this fixed space. The quotient is therefore residual-fixed,
and the dual moving space is fixed by Q_a. Duality transports this to
[[V_a,Q_a],Ltilde_a] ≤ Z_a in the actual free amalgam.

This proves the triple-commutator clause of the expanded c(V_a/Z_a)=1
assertion. The remaining natural splitting and generation clauses are owned
by the separate natural-section assembly.

Source: Meierfrankenfeld--Stellmacher (1993), notation p.881 and
(4.3.1)(iii), pp.882--883; this supplies the required binary representation
implication directly, without assuming later source conclusions.
-/

public section

open Subgroup Representation Stellmacher.PushingUp.AmalgamGraph
open Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural.Triple
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The source's unconditional triple bound in the actual free amalgam. -/
theorem radius_triple_commutator (source : LocalSource L R)
    (geometry : Geometry R) (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (p : Counterexample geometry)
    (hfour : Nat.card (radiusCommutator p.a p.a') = 4) :
    ⁅⁅V R p.a, Q R p.a⁆, Ltilde R p.a⁆ ≤ Z R p.a := by
  apply radius_triple_of_dual_fixed source geometry hb modules p.a p.color_a
  let S := stabilizer R p.a
  let H := (V R p.a).subgroupOf S
  let N := (Z R p.a).subgroupOf S
  let := radius_normal (R := R) p.a
  let := geometry.Z_normal p.a
  let : IsElementaryAbelian 2 (H ⧸ N.subgroupOf H) :=
    elementary_radius_quotient source geometry hb modules p.a p.color_a
  let := finite_stabilizer R p.a
  obtain ⟨π, hπ, hker, hk, _hA, hc⟩ :=
    exists_endpoint_projection source geometry hb modules p hfour
  have hne : ((Z R p.a').subgroupOf S).map π ≠ ⊥ := by
    intro hh
    rw [hh, card_bot] at hc
    omega
  have hn : ¬ fixedSpace (sectionRepresentation H N).dual π.ker ≤
      fixedSpace (sectionRepresentation H N).dual (pResidual 2 S) := by
    rw [hker]
    exact radius_dual_fixedSpace_moving source geometry hb modules p.a p.color_a
  have hd := moving_le_fixed_of_fixedSpace_not_le π hπ hk
    ((Z R p.a').subgroupOf S) hne (sectionRepresentation H N).dual
    (radius_dual_displacement source geometry hb modules p) hn
  rw [hker] at hd
  exact hd
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural.Triple
