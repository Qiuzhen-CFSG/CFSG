module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.Actions
public import Theory.GroupTheory.PGroup.CharacteristicPairReduction
public import Theory.GroupAction.CoprimeHall
public import Theory.GroupTheory.Fitting.PrimeComplementCentralizer
public import Theory.GroupTheory.CComponent.QuotientLifting


/-!
# The coprime part of the generalized-Fitting centralization

An abelian normal two-subgroup splits under an action of odd order into
its fixed subgroup and its commutator subgroup. If the Sylow central
involutions are fixed, the commutator subgroup is disjoint from them.
Every nontrivial normal two-subgroup meets those involutions, so the
commutator subgroup is trivial.

For the inverse image of F(G/O₂(G)), conjugation factors through an
odd-order group because O₂(G/O₂(G)) = 1. This proves the Fitting part
of 15.3.49(a). Only the fixed core C is assumed abelian, not U or V_H.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), p.1142.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.FittingFaithfulness

open Subgroup
open scoped commutatorElement
open CFSG.Quasithin.Chapter15.Section03

theorem normal_disjoint_centralOmega {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (K : Subgroup G) [K.Normal]
    (hp : IsPGroup 2 K) (hd : Disjoint K (centralInvolutions T)) : K = ⊥ := by
  have hKT : K ≤ T := hp.le_sylow_of_normal T
  let D := K.subgroupOf (T : Subgroup G)
  let : D.Normal := inferInstance
  by_contra hk
  have hdne : D ≠ ⊥ := by
    intro hb
    apply hk
    simpa [D, map_subgroupOf_eq_of_le hKT] using congrArg (map (T : Subgroup G).subtype) hb
  have hi := center_inf_ne_bot_of_normal T.isPGroup' D hdne
  let I := center T ⊓ D
  let : Nontrivial I := (nontrivial_iff_ne_bot I).mpr hi
  have hpI : IsPGroup 2 I := T.isPGroup'.to_subgroup I
  obtain ⟨n, hn, he⟩ := hpI.nontrivial_iff_card.mp inferInstance
  have hc : 2 ∣ Nat.card I := he.symm ▸ dvd_pow_self 2 (ne_of_gt hn)
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 2 hc (G := I)
  have hz : ((a : T) : G) ∈ centralInvolutions T := by
    apply mem_map_of_mem (T : Subgroup G).subtype
    refine ⟨⟨(a : T), a.property.1⟩, Subgroup.subset_closure ?_, rfl⟩
    change (⟨(a : T), a.property.1⟩ : center T) ^ (2 ^ 1) = 1
    apply Subtype.ext
    have he := congrArg (fun x : I => (x : T)) (pow_orderOf_eq_one a)
    simpa [ha] using he
  have hk' : ((a : T) : G) ∈ K := a.property.2
  have ha1 : a = 1 := Subtype.ext (Subtype.ext (hd.le_bot ⟨hk', hz⟩))
  simp [ha1] at ha

private noncomputable def action {G : Type*} [Group G] (C : Subgroup G) [C.Normal] : G →* MulAut C :=
  C.normalizerMonoidHom.comp ((MonoidHom.id G).codRestrict _
    (fun g => by rw [C.normalizer_eq_top]; trivial))

private theorem action_apply {G : Type*} [Group G] (C : Subgroup G) [C.Normal] (g : G) (c : C) :
    (action C g c : G) = g * c * g⁻¹ := rfl

private theorem comm_image {G : Type*} [Group G] (C R : Subgroup G) [C.Normal] :
    (commutatorAction (R.map (action C)) C).map C.subtype = ⁅C,R⁆ := by
  rw [commutatorAction_eq_closure, MonoidHom.map_closure]
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro _ ⟨_, ⟨a, c, rfl⟩, rfl⟩
    obtain ⟨r, hr, he⟩ := a.property
    change (c : G)⁻¹ * ((a : MulAut C) c : G) ∈ ⁅C,R⁆
    rw [← he, action_apply]
    simpa [commutatorElement_def, mul_assoc] using
      commutator_mem_commutator (C.inv_mem c.property) hr
  · apply commutator_le.mpr
    intro c hc r hr
    apply Subgroup.subset_closure
    refine ⟨(⟨c, hc⟩ : C) *
      ((⟨action C r, mem_map_of_mem _ hr⟩ : R.map (action C)) • (⟨c, hc⟩ : C)⁻¹),
      ⟨⟨action C r, mem_map_of_mem _ hr⟩, (⟨c, hc⟩ : C)⁻¹, by simp⟩, ?_⟩
    change c * (r * c⁻¹ * r⁻¹) = ⁅c,r⁆
    simp [commutatorElement_def, mul_assoc]

private theorem coprime_normal_centralization {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (C R : Subgroup G) [C.Normal] [R.Normal]
    [IsMulCommutative C] (hp : IsPGroup 2 C)
    (hcop : Nat.Coprime (Nat.card (R.map (action C))) (Nat.card C))
    (hZ : centralInvolutions T ≤ centralizer (R : Set G)) :
    R ≤ centralizer (C : Set G) := by
  have hcompl := isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
    (G := C) (A := R.map (action C))
    (Group.isSolvable_of_comm (fun a b : C => IsMulCommutative.is_comm.comm a b))
    hcop inferInstance
  have hb : ⁅C,R⁆ = ⊥ := by
    apply normal_disjoint_centralOmega T _ (hp.to_le (commutator_le_left C R))
    apply disjoint_iff.mpr
    apply le_bot_iff.mp
    intro x hx
    obtain ⟨c, hc, he⟩ := (comm_image C R).symm.le hx.1
    have hfixed : c ∈ fixedPointSubgroup (R.map (action C)) C := by
      intro a
      obtain ⟨r, hr, he'⟩ := a.property
      apply Subtype.ext
      change ((a : MulAut C) c : G) = c
      rw [← he', action_apply]
      have hz := (hZ hx.2) r hr
      rw [← he] at hz
      change r * (c : G) = (c : G) * r at hz
      rw [hz, mul_assoc, mul_inv_cancel, mul_one]
    have hc1 : c = 1 := hcompl.disjoint.le_bot ⟨hfixed, hc⟩
    change x = 1
    rw [← he, hc1]
    rfl
  exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hb)

/-- The Fitting subgroup of the two-core quotient centralizes an abelian
normal two-subgroup centralized by the two-core, when the Sylow central
involutions are central in the whole group. -/
theorem fitting_preimage_centralizes
    {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (C : Subgroup G) [C.Normal] [IsMulCommutative C]
    (hC : IsPGroup 2 C) (hQ : pCore 2 G ≤ centralizer (C : Set G))
    (hZ : centralInvolutions T ≤ center G) :
    (fittingSubgroup (G ⧸ pCore 2 G)).comap (QuotientGroup.mk' (pCore 2 G)) ≤
      centralizer (C : Set G) := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let F := fittingSubgroup (G ⧸ pCore 2 G)
  let R := F.comap q
  have hker : pCore 2 G ≤ (action C).ker := by
    intro g hg
    apply MulEquiv.ext
    intro c
    apply Subtype.ext
    change g * (c : G) * g⁻¹ = c
    rw [← (mem_centralizer_iff.mp (hQ hg)) c c.property]
    simp [mul_assoc]
  let f := QuotientGroup.lift (pCore 2 G) (action C) hker
  have he : R.map (action C) = F.map f := by
    have hq : f.comp q = action C := rfl
    rw [← hq, ← map_map, map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  have hfodd : Nat.Coprime 2 (Nat.card F) :=
    (pPrimeCore_coprime_card (p := 2) (G := G ⧸ pCore 2 G)).of_dvd_right
      (card_dvd_of_le (fitting_le_pPrimeCore_of_pCore_eq_bot 2
        (pCore_quotient_pCore_eq_bot 2)))
  have himg : Nat.Coprime 2 (Nat.card (R.map (action C))) := by
    rw [he]
    exact hfodd.of_dvd_right (card_map_dvd F f)
  obtain ⟨n, hn⟩ := hC.exists_card_eq
  apply coprime_normal_centralization T C R hC
  · rw [hn]
    exact himg.symm.pow_right n
  · exact hZ.trans (center_le_centralizer (R : Set G))

end CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.FittingFaithfulness
end
