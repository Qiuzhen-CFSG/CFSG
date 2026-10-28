module

public import Theory.GroupTheory.PResidual.Defs
public import Theory.GroupTheory.PPrimeCoreNormalComplement
public import Theory.GroupTheory.CyclicSylowNormalComplement

/-!
# Prime residuals in groups with a normal complement

In a finite group with a normal p-complement, the p-residual is the p′-core.
Every p′-element dies in every p-group quotient, giving one containment;
the quotient by the p′-core is itself a p-group, giving the other.
Burnside transfer specializes this to any cyclic Sylow two-subgroup, including
the trivial Sylow subgroup in an odd-order group.

Application: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma 14.2.21, printed p.989, and the cyclic-Sylow theorem A.1.38.
-/

public section

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- The prime-complement core is contained in the prime residual. -/
theorem pPrimeCore_le_pResidual : pPrimeCore p G ≤ pResidual p G := by
  apply le_sInf
  rintro N ⟨hN, hQ⟩ x hx
  let := hN
  let q := QuotientGroup.mk' N
  have hxord : Nat.Coprime p (orderOf x) :=
    (pPrimeCore_coprime_card (p := p) (G := G)).of_dvd_right
      ((pPrimeCore p G).orderOf_dvd_natCard hx)
  obtain ⟨k, hk⟩ := hQ.exists_orderOf_eq_pow (q x)
  apply (QuotientGroup.eq_one_iff x).mp
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes (hxord.pow_left k)
    (hk ▸ dvd_refl _) (orderOf_map_dvd q x)

/-- A normal complement identifies the residual with the prime-complement core. -/
theorem pResidual_eq_pPrimeCore_of_hasNormalPComplement
    (h : HasNormalPComplement p G) : pResidual p G = pPrimeCore p G := by
  apply le_antisymm ?_ pPrimeCore_le_pResidual
  exact sInf_le ⟨inferInstance,
    isPGroup_quotient_pPrimeCore_of_hasNormalPComplement p G h⟩

/-- The cyclic-Sylow-two normal-complement theorem without an even-order hypothesis. -/
theorem Sylow.hasNormalTwoComplement_of_isCyclic
    (T : Sylow 2 G) (hT : IsCyclic T) : HasNormalPComplement 2 G := by
  by_cases heven : 2 ∣ Nat.card G
  · exact BenderSuzuki.External.Suzuki.V.suzuki_ch5_theorem_2_10_corollary_1
      T ((Nat.minFac_eq_two_iff _).mpr heven) hT
  · refine ⟨⊤, inferInstance, ?_, ?_⟩
    · simpa using Nat.prime_two.coprime_iff_not_dvd.mpr heven
    · let : Subsingleton (G ⧸ (⊤ : Subgroup G)) :=
        QuotientGroup.subsingleton_quotient_top
      exact IsPGroup.of_card (n := 0) (by simp)

/-- With cyclic Sylow two-subgroups, the two-residual is the odd core. -/
theorem Sylow.twoResidual_eq_oddCore_of_isCyclic
    (T : Sylow 2 G) (hT : IsCyclic T) : pResidual 2 G = pPrimeCore 2 G :=
  pResidual_eq_pPrimeCore_of_hasNormalPComplement
    (T.hasNormalTwoComplement_of_isCyclic hT)

/-- The two-residual has odd order in the cyclic-Sylow case. -/
theorem Sylow.odd_card_twoResidual_of_isCyclic
    (T : Sylow 2 G) (hT : IsCyclic T) : Odd (Nat.card (pResidual 2 G)) := by
  rw [T.twoResidual_eq_oddCore_of_isCyclic hT]
  exact Nat.coprime_two_left.mp pPrimeCore_coprime_card

/-- The residual itself is the normal odd complement, with two-group quotient. -/
theorem Sylow.twoResidual_normal_complement_of_isCyclic
    (T : Sylow 2 G) (hT : IsCyclic T) :
    ∃ hN : (pResidual 2 G).Normal,
      Odd (Nat.card (pResidual 2 G)) ∧
      @IsPGroup 2 (G ⧸ pResidual 2 G)
        (@QuotientGroup.Quotient.group G _ (pResidual 2 G) hN) := by
  have he := T.twoResidual_eq_oddCore_of_isCyclic hT
  have hn : (pResidual 2 G).Normal := by rw [he]; infer_instance
  refine ⟨hn, T.odd_card_twoResidual_of_isCyclic hT, ?_⟩
  exact (isPGroup_quotient_pPrimeCore_of_hasNormalPComplement 2 G
    (T.hasNormalTwoComplement_of_isCyclic hT)).of_equiv
      (QuotientGroup.quotientMulEquivOfEq he).symm

end
