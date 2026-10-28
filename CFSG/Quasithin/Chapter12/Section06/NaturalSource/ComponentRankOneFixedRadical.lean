module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentRankOneLinear

/-!
# The original marked involution has a non-two radical

Condition (*) forces a cubic divisor in the radical of the literal
centralizer inside the original action range. For a model with two-group
outer automorphisms, a two-group radical in the fixed subgroup of the
specified module involution would make that centralizer radical a
two-group as well. The contradiction retains the same involution, not
just an existentially chosen model automorphism.

This supplies the exact obstruction used to remove field involutions in
the original PSL2 branch. All earlier geometric inputs remain explicit.
Source: Aschbacher--Smith, proof of 12.6.26, printed pp.832--833, condition (*).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1)
  (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
  (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)


include hz hTV hTz hbound hH hn a in
theorem SourceHypothesis.original_model_fixed_radical_not_two
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {B : Type*} [Group B] [Finite B] (e : Nonabelian.Setup.star H c.K ≃* B)
    (ho : IsPGroup 2 (MulAut.Outer B))
    (b : MulAut (Nonabelian.Setup.star H c.K))
    (hb : b ∈ (V.subgroupOf c.localActor).map a.action) (hb2 : orderOf b = 2) :
    ¬ IsPGroup 2 (solvableRadical (MulAut.congr e b).fixedSubgroup) := by
  intro hf
  let K := Nonabelian.Setup.star H c.K
  let : IsSimpleGroup K := S.original_selectedComponent_simple D hZ z hz hTV hTz
    hbound hH hn c a hTI hns
  let := c.component.2
  have hzK : center K = ⊥ := center_eq_bot_of_simple_perfect
  let t : a.action.range := ⟨b,(map_le_range _ _) hb⟩
  let U := ((V.subgroupOf c.localActor).map a.action).subgroupOf a.action.range
  have hU : Nat.card U = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (map_le_range _ _)).toEquiv]
    exact a.module_card
  have ht : orderOf t = 2 := (Subgroup.orderOf_coe t).symm.trans hb2
  have hgen : zpowers t = U :=
    eq_of_le_of_card_ge (zpowers_le.mpr hb) (by rw [Nat.card_zpowers,ht,hU])
  have hC : centralizer (U : Set a.action.range) = centralizer ({t} : Set a.action.range) := by
    rw [←hgen,zpowers_eq_closure,centralizer_closure]
  let j := MulAut.fixedSubgroupCongr e b
  let jR := (j.subgroupMap (solvableRadical b.fixedSubgroup)).trans
    (MulEquiv.subgroupCongr (map_solvableRadical_equiv j))
  have hfixed := hf.of_equiv jR.symm
  have hinner : MulAut.innerSubgroup K ≤ a.action.range := by
    rw [←a.component_image]
    exact map_le_range _ _
  have htwo := MulAut.centralizer_radical_isTwoGroup_of_fixed hzK
    (ho.of_equiv (MulAut.outerCongr e).symm) a.action.range hinner t hfixed
  have hd := S.original_action_centralizer_radical_three_dvd D hZ z hz hTV hTz
    hbound hH hn c a
  change 3 ∣ Nat.card (solvableRadical (centralizer (U : Set a.action.range))) at hd
  rw [hC] at hd
  obtain ⟨k,hk⟩ := htwo.exists_card_eq
  rw [hk] at hd
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)

end CFSG.Quasithin.Chapter12.Section06
