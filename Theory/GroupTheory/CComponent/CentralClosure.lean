module
public import Theory.GroupTheory.CComponent.SimplePairKernel
public import Theory.GroupTheory.ComponentPairRankDescent
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Mathlib.GroupTheory.IndexNormal

/-!
# Proper normal closures for Sylow-central elements above a component pair

A Sylow subgroup meets an even simple component nontrivially. A centralizing
element must normalize that component: otherwise the fixed intersection
would lie in the trivial center of two distinct commuting components.
For a normal exchanged pair the component normalizer has index two, so it
contains the entire normal closure and is proper.

The second theorem performs this argument on the literal ambient two-core
quotient of a pair of simple-core C-components. Both the component image and
the original conjugator are retained. Source application: Aschbacher--Smith,
15.2.27(2), printed p.1119, via G.6.4(4).
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem simple_centerless (A : Subgroup G) [IsSimpleGroup A] [Group.IsPerfect A] :
    center A = ⊥ := by
  exact (inferInstance : (center A).Normal).eq_bot_or_eq_top.resolve_right
    (fun he => Group.IsPerfect.not_isMulCommutative A (center_eq_top_iff.mp he))

/-- A centralizing element cannot normally generate an exchanged simple-component pair. -/
theorem normalClosure_ne_top_of_central_sylow_simple_pair
    (A : Subgroup G) (hA : IsComponent G A) [IsSimpleGroup A]
    (t : G) (hne : A ≠ A.conjBy t) [(A ⊔ A.conjBy t).Normal]
    (hdiv : 2 ∣ Nat.card A) (S : Sylow 2 G) (z : G)
    (hc : ∀ s ∈ S, Commute z s) : normalClosure ({z} : Set G) ≠ ⊤ := by
  let := hA.2
  have hnorm : z ∈ normalizer (A : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    by_contra hn
    have hcomm := hA.commutator_eq_bot_of_ne (hA.map_conj z) (Ne.symm hn)
    obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_subnormal A hA.1
    have hPn := P.ne_bot_of_dvd_card hdiv
    let : Nontrivial (P : Subgroup A) := (Subgroup.nontrivial_iff_ne_bot _).mpr hPn
    obtain ⟨x,hx,hx1⟩ := (P : Subgroup A).exists_ne_one_of_nontrivial
    have hxS : (x : G) ∈ S := by rw [hP] at hx; exact hx
    have hfix : MulAut.conj z (x : G) = x := by
      change z * (x : G) * z⁻¹ = x
      rw [(hc x hxS).eq,mul_inv_cancel_right]
    have hxconj : (x : G) ∈ A.conjBy z :=
      hfix ▸ mem_map_of_mem (MulAut.conj z).toMonoidHom x.property
    have hxcenter : x ∈ center A := mem_center_iff.mpr fun y => Subtype.ext
      (((commutator_eq_bot_iff_le_centralizer.mp hcomm y.property) x hxconj).symm)
    exact hx1 (mem_bot.mp (simple_centerless A ▸ hxcenter))
  have hi := ComponentPairRankDescent.component_normalizer_index_two_of_normal_pair A hA t hne
  let := normal_of_index_eq_two hi
  have hle : normalClosure ({z} : Set G) ≤ normalizer (A : Set G) :=
    normalClosure_le_normal (Set.singleton_subset_iff.mpr hnorm)
  intro he
  have ht := hle (he ▸ mem_top t)
  exact hne (mem_normalizer_iff_map_conj_eq.mp ht).symm

/-- The same obstruction on the actual quotient by the ambient two-core. -/
theorem normalClosure_ne_top_of_central_sylow_simpleCore_pair
    (B : Subgroup G) (hB : B.IsCComponent) [IsSimpleGroup (B ⧸ pCore 2 B)]
    (t : G) (hne : B ≠ B.conjBy t) [(B ⊔ B.conjBy t).Normal]
    (hdiv : 2 ∣ Nat.card (B ⧸ pCore 2 B))
    (S : Sylow 2 (G ⧸ pCore 2 G)) (z : G ⧸ pCore 2 G)
    (hc : ∀ s ∈ S, Commute z s) : normalClosure ({z} : Set _) ≠ ⊤ := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let A := B.map q
  let : Group.IsNilpotent (pCore 2 G) := pCore_isPGroup.isNilpotent
  have hAc := hB.map_quotient (pCore 2 G)
  let := hAc.perfect
  let : IsSimpleGroup A := (cComponentTwoCoreQuotientEquiv hB).symm.isSimpleGroup
  have hA : IsComponent (G ⧸ pCore 2 G) A :=
    ⟨hAc.subnormal, ⟨((QuotientGroup.quotientMulEquivOfEq (simple_centerless A)).trans
      QuotientGroup.quotientBot).isSimpleGroup⟩⟩
  have hconj : (B.conjBy t).map q = A.conjBy (q t) := by
    change (B.map (MulAut.conj t).toMonoidHom).map q =
      (B.map q).map (MulAut.conj (q t)).toMonoidHom
    rw [Subgroup.map_map,Subgroup.map_map]
    congr 1
  have hn : A ≠ A.conjBy (q t) := by
    intro he
    apply hne
    exact hB.eq_of_map_quotient_eq (hB.map_equiv (MulAut.conj t)) (pCore 2 G)
      (he.trans hconj.symm)
  have hp : (A ⊔ A.conjBy (q t)).Normal := by
    rw [←hconj,show A=B.map q from rfl,←Subgroup.map_sup]
    exact Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let := hp
  have hd : 2 ∣ Nat.card A := by
    rw [←Nat.card_congr (cComponentTwoCoreQuotientEquiv hB).toEquiv]
    exact hdiv
  exact normalClosure_ne_top_of_central_sylow_simple_pair A hA (q t) hn hd S z hc
end Theory.GroupTheory
