module
public import Theory.GroupAction.PPerfectFixedCentralizer
public import Theory.GroupTheory.PCoreInRestriction
public import Theory.GroupTheory.PerfectSmallTwoAction
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Fully moved sections in a group with a small two-core center

Suppose a full Sylow normalizes a perfect actor B and an elementary section
E with [E,B] = E, while O₂(B) fixes E. The ambient two-core Q then commutes
with the B-action on E. Its fixed subgroup lies in Z(Q) when Q is
self-centralizing. If |Z(Q)| ≤ 4, perfectness makes B fix that subgroup;
the commuting fixed-point theorem makes B fix E, so E is trivial.

The restriction theorem retains the literal actor, section and full Sylow
inside a containing subgroup. Unlike a bound on the whole section, this
small-center contradiction needs no irreducibility assumption.
Source: Aschbacher--Smith A.1.41 and C.1.11, pp.31,124; application to
involution centralizers in the point-component inspection of 10.2.9, p.750.
-/

public section

open Subgroup
namespace Theory.GroupAction
variable {G : Type*} [Group G] [Finite G]

/-- A small self-centralizing core center excludes every nonzero fully moved section. -/
theorem fully_moved_eq_bot_of_small_core_center
    (S : Sylow 2 G) (B E : Subgroup G) [Group.IsPerfect B]
    (hB : IsPPerfect 2 B)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hSE : (S : Subgroup G) ≤ normalizer (E : Set G))
    (hE : IsElementaryAbelian 2 E) (hEB : E ≤ B)
    (hcore : B.pCoreIn 2 ≤ centralizer (E : Set G)) (hmove : ⁅E,B⁆ = E)
    (hC : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hsmall : Nat.card (center (pCore 2 G)) ≤ 4) : E = ⊥ := by
  let Q := pCore 2 G
  let W := E ⊓ centralizer (Q : Set G)
  have hQS : Q ≤ S := pCore_isPGroup.le_sylow_of_normal S
  have hBQ : B ≤ normalizer (Q : Set G) := le_normalizer_of_normal
  have hBE : B ≤ normalizer (E : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr hmove.le
  have hcomm : ⁅Q,B⁆ ≤ B.pCoreIn 2 :=
    le_pCoreIn_of_normalizes
      (pCore_isPGroup.to_le (le_normalizer_iff_commutator_le_left.mp hBQ))
      (le_normalizer_iff_commutator_le_right.mp (hQS.trans hSB))
      (normalizer_commutator_ge_right Q B)
  have hWZ : W ≤ (center Q).map Q.subtype := by
    intro w hw
    have hwQ := hC hw.2
    refine ⟨⟨w,hwQ⟩,mem_center_iff.mpr (fun q => ?_),rfl⟩
    exact Subtype.ext (hw.2 q q.property)
  have hWcard : Nat.card W ≤ 4 := by
    have hh := card_le_of_le hWZ
    rw [card_map_of_injective Q.subtype_injective] at hh
    exact hh.trans hsmall
  have hWB : W ≤ B := inf_le_left.trans hEB
  have hBW : B ≤ normalizer (W : Set G) :=
    (le_inf hBE (hBQ.trans (normalizer_le_normalizer_centralizer Q))).trans
      inf_normalizer_le_normalizer_inf
  let : (W.subgroupOf B).Normal := normal_subgroupOf_of_le_normalizer hBW
  have hfixed : ⁅W,B⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    have hc := le_centralizer_of_isPerfect_of_card_le_four (⊤ : Subgroup B)
      (W.subgroupOf B) (by
        rwa [Nat.card_congr (subgroupOfEquivOfLe hWB).toEquiv])
    intro w hw b hb
    exact (congrArg B.subtype (hc (mem_top (⟨b,hb⟩ : B)) ⟨w,hWB hw⟩ hw)).symm
  let := hE
  exact hmove.symm.trans (hB.centralizes_of_commuting_fixed B Q E pCore_isPGroup
    hBE (hQS.trans hSE) (hcomm.trans hcore) hfixed)

end Theory.GroupAction

namespace Theory.GroupAction
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Apply the obstruction in a subgroup containing the same full Sylow and actor. -/
theorem fully_moved_eq_bot_of_overgroup_small_core_center
    (S : Sylow 2 G) (B E K : Subgroup G) [Group.IsPerfect B]
    (hB : IsPPerfect 2 B)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hSE : (S : Subgroup G) ≤ normalizer (E : Set G))
    (hE : IsElementaryAbelian 2 E) (hEB : E ≤ B)
    (hcore : B.pCoreIn 2 ≤ centralizer (E : Set G)) (hmove : ⁅E,B⁆ = E)
    (hBK : B ≤ K) (hSK : (S : Subgroup G) ≤ K)
    (hC : centralizer (pCore 2 K : Set K) ≤ pCore 2 K)
    (hsmall : Nat.card (center (pCore 2 K)) ≤ 4) : E = ⊥ := by
  have hEK := hEB.trans hBK
  let := hE
  let : Group.IsPerfect (B.subgroupOf K) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hBK).symm.toMonoidHom)
    (subgroupOfEquivOfLe hBK).symm.surjective
  have hB' := hB.of_surjective (subgroupOfEquivOfLe hBK).symm.toMonoidHom
    (subgroupOfEquivOfLe hBK).symm.surjective
  have hh := fully_moved_eq_bot_of_small_core_center
    (S.subtype hSK) (B.subgroupOf K) (E.subgroupOf K) hB' (by
      intro s hs
      apply mem_normalizer_iff.mpr
      intro b
      exact mem_normalizer_iff.mp (hSB hs) (b : G)) (by
      intro s hs
      apply mem_normalizer_iff.mpr
      intro e
      exact mem_normalizer_iff.mp (hSE hs) (e : G))
    (IsElementaryAbelian.subgroupOf hEK) (comap_mono hEB) (by
      rw [pCoreIn_subgroupOf 2 B K hBK]
      intro b hb e he
      exact Subtype.ext (hcore hb e he)) (by
      apply map_injective K.subtype_injective
      rw [map_commutator,map_subgroupOf_eq_of_le hEK,map_subgroupOf_eq_of_le hBK,hmove])
    hC hsmall
  have hm := congrArg (map K.subtype) hh
  simpa only [map_subgroupOf_eq_of_le hEK,Subgroup.map_bot] using hm

end Theory.GroupAction
