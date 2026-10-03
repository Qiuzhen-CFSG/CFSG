module

public import Theory.GroupTheory.PPrimeCoreNormalComplement
public import Theory.GroupAction.Lemmas
public import Theory.GroupAction.Quotient

/-!
# Normal complements in extensions

A normal subgroup with a normal p-complement extends to a normal p-complement
of the whole group when its quotient is a p-group. Use the characteristic
p′-core of the subgroup and the third isomorphism theorem. If the ambient
p′-core is trivial, having a normal p-complement means being a p-group.

These are the extension and core-free bridges used in Suzuki,
*Group Theory II*, V.2.27(v) and VI, §2.2, Example 3. Extracted from
`BenderSuzuki/External/Huppert/IV/ComplementTransfer.lean`; historical names
are retained and re-exported there.
-/

namespace BenderSuzuki.External

universe u

public theorem hkt_isPGroup_quotient_map_subtype_of_extension
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (H : Subgroup G) [H.Normal] (K : Subgroup H) [K.Characteristic]
    (hHKp : IsPGroup p (H ⧸ K)) (hGHp : IsPGroup p (G ⧸ H)) :
    IsPGroup p (G ⧸ K.map H.subtype) := by
  classical
  let N : Subgroup G := K.map H.subtype
  have hN_le_H : N ≤ H := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨k, _hk, rfl⟩
    exact k.property
  have : N.Normal := by
    dsimp [N]
    infer_instance
  let qN : G →* G ⧸ N := QuotientGroup.mk' N
  let Hbar : Subgroup (G ⧸ N) := H.map qN
  have : Hbar.Normal := by
    exact Subgroup.Normal.map (inferInstance : H.Normal) qN (QuotientGroup.mk'_surjective N)
  have hHbar_p : IsPGroup p Hbar := by
    let eHN : H ⧸ N.subgroupOf H ≃* H ⧸ K :=
      QuotientGroup.quotientMulEquivOfEq (by
        simpa [N] using (subgroupOf_map_subtype_eq (K := H) K))
    let eRange : H ⧸ N.subgroupOf H ≃* Hbar := quotientSubgroupRangeEquiv H N
    exact hHKp.of_equiv (eHN.symm.trans eRange)
  have hquot_p : IsPGroup p ((G ⧸ N) ⧸ Hbar) := by
    let e : (G ⧸ N) ⧸ Hbar ≃* G ⧸ H :=
      QuotientGroup.quotientQuotientEquivQuotient (N := N) (M := H) hN_le_H
    exact hGHp.of_equiv e.symm
  obtain ⟨a, ha⟩ := hquot_p.exists_card_eq
  obtain ⟨b, hb⟩ := hHbar_p.exists_card_eq
  have hcard :
      Nat.card (G ⧸ N) = Nat.card ((G ⧸ N) ⧸ Hbar) * Nat.card Hbar := by
    simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := Hbar))
  refine IsPGroup.of_card (p := p) (G := G ⧸ N) (n := a + b) ?_
  rw [hcard, ha, hb, Nat.pow_add]

public theorem hkt_hasNormalPComplement_of_normal_subgroup_and_pgroup_quotient
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (H : Subgroup G) [H.Normal]
    (hGHp : IsPGroup p (G ⧸ H))
    (hHcomp : HasNormalPComplement p H) :
    HasNormalPComplement p G := by
  classical
  let K : Subgroup H := pPrimeCore p H
  let N : Subgroup G := K.map H.subtype
  have : K.Characteristic := pPrimeCore_characteristic (p := p) (G := H)
  have hNnorm : N.Normal := by
    dsimp [N, K]
    infer_instance
  have hNcop : Nat.Coprime p (Nat.card N) := by
    have hcard : Nat.card N = Nat.card K := by
      simpa [N] using
        (Subgroup.card_map_of_injective (K := K) (f := H.subtype) H.subtype_injective)
    rw [hcard]
    exact pPrimeCore_coprime_card (G := H) (p := p)
  have hHKp : IsPGroup p (H ⧸ K) :=
    isPGroup_quotient_pPrimeCore_of_hasNormalPComplement (p := p) (H := H) hHcomp
  have hGNp : IsPGroup p (G ⧸ N) :=
    hkt_isPGroup_quotient_map_subtype_of_extension (G := G) (p := p)
      H K hHKp hGHp
  exact ⟨N, hNnorm, hNcop, hGNp⟩

/-- If the canonical `p'`-core has vanished, the canonical quotient criterion
is just `Q` itself being a `p`-group. -/
public theorem hkt_isPGroup_of_quotient_pPrimeCore_isPGroup_of_pPrimeCore_eq_bot
    {Q : Type u} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (hcore : pPrimeCore p Q = ⊥)
    (hquot : IsPGroup p (Q ⧸ pPrimeCore p Q)) :
    IsPGroup p Q := by
  let e : Q ⧸ pPrimeCore p Q ≃* Q ⧸ (⊥ : Subgroup Q) :=
    QuotientGroup.quotientMulEquivOfEq hcore
  have hbot : IsPGroup p (Q ⧸ (⊥ : Subgroup Q)) := hquot.of_equiv e
  exact hbot.of_equiv (QuotientGroup.quotientBot (G := Q))

public theorem hkt_isPGroup_of_hasNormalPComplement_of_pPrimeCore_eq_bot
    {Q : Type u} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (hcore : pPrimeCore p Q = ⊥) (hcomp : HasNormalPComplement p Q) :
    IsPGroup p Q :=
  hkt_isPGroup_of_quotient_pPrimeCore_isPGroup_of_pPrimeCore_eq_bot
    (Q := Q) (p := p) hcore
    (isPGroup_quotient_pPrimeCore_of_hasNormalPComplement
      (p := p) (H := Q) hcomp)

/-- If `p` does not divide the group order, the whole group is a normal
`p`-complement and the quotient is trivial. -/
public theorem hkt_hasNormalPComplement_of_not_dvd_card
    {Q : Type u} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (hnot : ¬ p ∣ Nat.card Q) : HasNormalPComplement p Q := by
  classical
  refine ⟨⊤, inferInstance, ?_, ?_⟩
  · simpa using (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr hnot
  · have : Subsingleton (Q ⧸ (⊤ : Subgroup Q)) :=
      QuotientGroup.subsingleton_quotient_top
    refine IsPGroup.of_card (p := p) (G := Q ⧸ (⊤ : Subgroup Q)) (n := 0) ?_
    simp

end BenderSuzuki.External
