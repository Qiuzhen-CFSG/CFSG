module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.ConjugateGraph
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.LocalActionFusion
public import Theory.GroupTheory.TwoInvolutionClassOrder
public import Theory.GroupTheory.PGroup.CyclicInvolution
public import Theory.GroupTheory.PCoreProduct

/-!
# Involutions and the literal Thompson pairs in the J₂ source argument

The two involution classes admit representatives commuting with the fixed z.
Indeed the central involution of a mixed dihedral pair belongs to one of the
two classes; conjugating that pair, if necessary, puts its z-class member at z.

The book defines P(x) by x ∈ ⟨uv⟩. The existing Thompson formula instead uses
the half-order power of uv. Uniqueness of an involution in a cyclic group
identifies these definitions, without a fusion-control assumption.

Source: Aschbacher, *Sporadic Groups* (1994), 7.2 and 47.1, pp.259–260.
This module does not assert the second centralizer or either local pair count.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open Theory.GroupTheory.TwoInvolutionClassOrder

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry

variable {G : Type*} [Group G] [Finite G]

/-- An involution in the other ambient class, without any placement assumption. -/
def OtherInvolution (D : Seed G) (t : G) : Prop :=
  orderOf t = 2 ∧ ¬ IsConj D.z t

theorem OtherInvolution.classes {D : Seed G} {t : G} (ht : OtherInvolution D t)
    (u : G) (hu : orderOf u = 2) : IsConj D.z u ∨ IsConj t u := by
  obtain ⟨v, hv, hnv, hclasses⟩ :=
    D.classes.representatives D.localType.involution
  have htv : IsConj t v := (hclasses t ht.1).resolve_left (fun h => ht.2 h.symm)
  exact (hclasses u hu).imp IsConj.symm (fun h => htv.trans h.symm)

theorem OtherInvolution.isConj {D : Seed G} {t u : G}
    (ht : OtherInvolution D t) (hu : OtherInvolution D u) : IsConj t u :=
  (ht.classes u hu.1).resolve_left hu.2

/-- The second class has a representative commuting with the original z. -/
theorem exists_commuting_other (D : Seed G) :
    ∃ t : G, OtherInvolution D t ∧ Commute D.z t := by
  obtain ⟨v, hv, hnv, hclasses⟩ :=
    D.classes.representatives D.localType.involution
  have hp := halfOrder_properties D.localType.involution hv hnv
    (IsConj.refl D.z) (IsConj.refl v)
  rcases hclasses (halfOrder D.z v) hp.1 with hz | ht
  · obtain ⟨g, hg⟩ := isConj_iff.mp hz
    let e := MulAut.conj g
    have he : e (halfOrder D.z v) = D.z := hg
    have hve : IsConj v (e v) := isConj_iff.mpr ⟨g, rfl⟩
    refine ⟨e v, ⟨(e.orderOf_eq v).trans hv,
      fun h => hnv (h.trans hve.symm)⟩, ?_⟩
    simpa only [he] using hp.2.2.map e
  · exact ⟨halfOrder D.z v, ⟨hp.1, fun h => hnv (h.trans ht)⟩,
      hp.2.1.symm⟩

/-- The pair set P(x) in the printed statement, with ambient fusion. -/
abbrev SourcePairs (z t x : G) :=
  {p : G × G // IsConj z p.1 ∧ IsConj t p.2 ∧ x ∈ zpowers (p.1 * p.2)}

noncomputable def sourceCount (z t x : G) : ℕ := Nat.card (SourcePairs z t x)

/-- Membership in the cyclic rotation subgroup singles out its half-order power. -/
theorem mem_zpowers_iff_halfOrder {z t x u v : G}
    (hz : orderOf z = 2) (ht : orderOf t = 2) (hn : ¬ IsConj z t)
    (hx : orderOf x = 2) (hu : IsConj z u) (hv : IsConj t v) :
    x ∈ zpowers (u * v) ↔ halfOrder u v = x := by
  have hp := halfOrder_properties hz ht hn hu hv
  have hm : halfOrder u v ∈ zpowers (u * v) := by
    rw [halfOrder_def]
    exact pow_mem (mem_zpowers _) _
  constructor
  · intro hxmem
    exact congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two
      (x := (⟨halfOrder u v, hm⟩ : zpowers (u * v)))
      (y := (⟨x, hxmem⟩ : zpowers (u * v)))
      ((orderOf_coe _).symm.trans hp.1) ((orderOf_coe _).symm.trans hx))
  · intro he
    exact he ▸ hm

/-- The book's pairs and the fibers used in the proved Thompson formula coincide. -/
noncomputable def sourcePairsEquivFiber {z t x : G}
    (hz : orderOf z = 2) (ht : orderOf t = 2) (hn : ¬ IsConj z t)
    (hx : orderOf x = 2) : SourcePairs z t x ≃ Fiber z t x :=
  Equiv.subtypeEquivRight fun p => by
    constructor
    · rintro ⟨hu, hv, hp⟩
      exact ⟨hu, hv, (mem_zpowers_iff_halfOrder hz ht hn hx hu hv).mp hp⟩
    · rintro ⟨hu, hv, hp⟩
      exact ⟨hu, hv, (mem_zpowers_iff_halfOrder hz ht hn hx hu hv).mpr hp⟩

theorem sourceCount_eq_kappa {z t x : G}
    (hz : orderOf z = 2) (ht : orderOf t = 2) (hn : ¬ IsConj z t)
    (hx : orderOf x = 2) : sourceCount z t x = kappa z t x := by
  rw [sourceCount, kappa_def]
  simpa only [Fiber, halfOrder_def] using
    Nat.card_congr (sourcePairsEquivFiber hz ht hn hx)

/-- Every printed pair actually lies in the full centralizer of its index. -/
theorem sourcePairs_mem_centralizer {D : Seed G} {t x : G}
    (ht : OtherInvolution D t) (hx : orderOf x = 2) (p : SourcePairs D.z t x) :
    p.val.1 ∈ involutionCentralizer x ∧ p.val.2 ∈ involutionCentralizer x :=
  fiber_mem_centralizer D.localType.involution ht.1 ht.2
    (sourcePairsEquivFiber D.localType.involution ht.1 ht.2 hx p)

/-- Thompson's formula with precisely the pair convention used on printed p.259. -/
theorem source_order_formula {D : Seed G} {t : G} (ht : OtherInvolution D t) :
    Nat.card G = sourceCount D.z t D.z * Nat.card (involutionCentralizer t) +
      sourceCount D.z t t * 1920 := by
  rw [sourceCount_eq_kappa D.localType.involution ht.1 ht.2 D.localType.involution,
    sourceCount_eq_kappa D.localType.involution ht.1 ht.2 ht.1,
    ← D.localType.centralizer_card]
  exact card_eq D.z t D.localType.involution ht.1 ht.2 ht.classes

/-- The earlier-source inputs to second-centralizer recognition. Constructing this
record requires the w = 2 branch of §46 and the first count in 47.1; these are not
extra assumptions of the eventual source theorem. Fusion stays inside the core. -/
structure LocalCensus (D : Seed G) : Prop where
  core_fusion : ∀ u ∈ involutionCentralizer D.z, orderOf u = 2 →
    (IsConj D.z u ↔ u ∈ ambientCore D.z)
  outside_fusion : ∀ u v : involutionCentralizer D.z,
    orderOf u = 2 → orderOf v = 2 →
    (u : G) ∉ ambientCore D.z → (v : G) ∉ ambientCore D.z → IsConj u v
  count_at_z : ∀ t : G, OtherInvolution D t → sourceCount D.z t D.z = 960

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry
