module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.SuzukiRankOne
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.JointKernels
public import Theory.SpecificGroups.Suzuki.SmallAutomorphisms
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.Sections

/-!
# Effective sections for the binary Suzuki actor

Every nontrivial normal subgroup of Sz(2) contains its order-five elements:
a normal subgroup without a factor five would be a two-group, contradicting
the trivial two-core. Distinct involutions have product of order five, as
checked in the existing faithful C₅:C₄ coordinates and transported through
the actual Suzuki matrix isomorphism. No simplicity is used.

Consequently an order-five source element moving a literal invariant
section makes its effective action faithful, by coprime Frattini faithfulness.
The source Frattini-radical consumer constructs that moving element from
the actual reflection and central root involution and discharges movement.
Source: Fong--Seitz I (1973), (5D), pp.26--27, and (6H), pp.52--53.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open RootCoordinates HexagonStructure

private theorem binary_suzuki_twoCore : pCore 2 (SuzukiMatrixGroup 0) = ⊥ := by
  let e := FiveFour.suzukiZeroEquiv
  have htwo : IsPGroup 2 ((pCore 2 (SuzukiMatrixGroup 0)).comap e.toMonoidHom) :=
    pCore_isPGroup.comap_of_injective e.toMonoidHom e.injective
  have hle : (pCore 2 (SuzukiMatrixGroup 0)).comap e.toMonoidHom ≤ pCore 2 FiveFour.Group :=
    le_sSup ⟨inferInstance,htwo⟩
  rw [FiveFour.twoCore_eq_bot] at hle
  apply eq_bot_iff.mpr
  intro x hx
  have hh := hle (show e.symm x ∈ (pCore 2 (SuzukiMatrixGroup 0)).comap e.toMonoidHom by
    change e (e.symm x) ∈ pCore 2 (SuzukiMatrixGroup 0)
    rwa [e.apply_symm_apply])
  exact mem_bot.mpr (e.symm.injective ((mem_bot.mp hh).trans (map_one e.symm).symm))

/-- Every nontrivial normal subgroup of Sz(2) contains its elements of order five. -/
theorem binary_suzuki_normal_contains_fifth (N : Subgroup (SuzukiMatrixGroup 0)) [N.Normal]
    (hne : N ≠ ⊥) (c : SuzukiMatrixGroup 0) (hc : c^5 = 1) : c ∈ N := by
  have hd : Nat.card N ∣ 5*4 := by simpa only [suzukiZero_card] using N.card_subgroup_dvd_card
  have hfive : 5 ∣ Nat.card N := by
    by_contra hn
    have hcop : Nat.Coprime (Nat.card N) 5 := (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 5)).mpr hn |>.symm
    have htwo : IsPGroup 2 N := IsPGroup.of_card_dvd_pow (n := 2) (hcop.dvd_of_dvd_mul_left hd)
    have hle : N ≤ pCore 2 (SuzukiMatrixGroup 0) := le_sSup ⟨inferInstance,htwo⟩
    rw [binary_suzuki_twoCore] at hle
    exact hne (bot_unique hle)
  have hi : N.index ∣ 4 := by
    obtain ⟨k,hk⟩ := hfive
    have he := N.index_mul_card
    rw [suzukiZero_card,hk] at he
    refine ⟨k,?_⟩
    nlinarith
  apply (QuotientGroup.eq_one_iff c).mp
  apply orderOf_eq_one_iff.mp
  apply Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 4 5)
  · exact (orderOf_dvd_natCard (QuotientGroup.mk' N c)).trans hi
  · apply orderOf_dvd_of_pow_eq_one
    change (QuotientGroup.mk' N c)^5 = 1
    rw [←map_pow,hc,map_one]

private instance fiveFour_decEq : DecidableEq FiveFour.Group := fun a b =>
  decidable_of_iff (a.left = b.left ∧ a.right = b.right) SemidirectProduct.ext_iff.symm

private theorem fiveFour_involution_product :
    ∀ a b : FiveFour.Group, a^2 = 1 → a ≠ 1 → b^2 = 1 → b ≠ 1 → a ≠ b →
      (a*b)^5 = 1 ∧ a*b ≠ 1 := by
  decide +kernel

/-- The order-five law for any distinct pair of binary Suzuki involutions. -/
theorem binary_suzuki_involution_product_order (s t : SuzukiMatrixGroup 0)
    (hs : s^2 = 1) (hsn : s ≠ 1) (ht : t^2 = 1) (htn : t ≠ 1) (hst : s ≠ t) :
    orderOf (s*t) = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let e := FiveFour.suzukiZeroEquiv
  have hh := fiveFour_involution_product (e.symm s) (e.symm t)
    (by rw [←map_pow,hs,map_one]) (e.symm.map_ne_one_iff.mpr hsn)
    (by rw [←map_pow,ht,map_one]) (e.symm.map_ne_one_iff.mpr htn)
    (fun h => hst (e.symm.injective h))
  apply orderOf_eq_prime
  · apply e.symm.injective
    simpa only [map_pow,map_mul,map_one] using hh.1
  · intro he
    apply hh.2
    rw [←map_mul,he,map_one]

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)
  (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup 0)
  (hB : (quotientBorel Q i).map μ.toMonoidHom = normalizer (SuzukiRootSubgroup 0 : Set (SuzukiMatrixGroup 0)))

include μ hB in
/-- A moving order-five source element detects the whole effective action, without simplicity. -/
theorem binary_suzuki_section_effectiveAction_injective (d : RootSection Q split i)
    (c : rankOne Q split i) (hc : orderOf c = 5) (hm : d.action c ≠ 1) :
    Function.Injective d.effectiveAction := by
  let e := suzukiActorEquiv Q split i 0 μ hB
  apply (MonoidHom.ker_eq_bot_iff _).mp
  by_contra hn
  let K := d.effectiveAction.ker
  have hk : K.comap e.symm.toMonoidHom ≠ ⊥ := by
    intro hz
    have he := congrArg (Subgroup.map e.symm.toMonoidHom) hz
    rw [map_comap_eq_self_of_surjective e.symm.surjective,Subgroup.map_bot] at he
    exact hn he
  have hmemb := binary_suzuki_normal_contains_fifth (K.comap e.symm.toMonoidHom) hk (e c)
    (by rw [←map_pow,←hc,pow_orderOf_eq_one,map_one])
  have hmemb' : c ∈ K := by
    change e.symm (e c) ∈ K at hmemb
    simpa only [e.symm_apply_apply] using hmemb
  exact hm (d.action_eq_one_of_odd c (by rw [hc]; decide) hmemb')

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
