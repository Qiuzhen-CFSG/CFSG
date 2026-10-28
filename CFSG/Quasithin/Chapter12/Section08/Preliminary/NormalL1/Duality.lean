module

public import CFSG.Quasithin.Chapter12.Section08.Actions.Comparison
public import Theory.GroupTheory.CentralBinaryCommutatorDuality

/-!
# The source commutator duality on U/C_U(V)

The central point and the elementary tilded quotient give a binary commutator
pairing on U × V. Its kernels are C_U(V) and C_V(U). The previously proved
12.8.8(3) identifies the latter with V₁ in the nonabelian branch. Finite binary
duality supplies a genuine linear equivalence, with its commutator evaluation
and simultaneous L₁-conjugation equation. No self-centralizing hypothesis on U
is used. `seed_commutator_le_point` supplies the commutator premise directly
from the literal quotient in 12.8.4.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
Lemma 12.8.8(5), printed p.852 (PDF p.869). Natural-module irreducibility is
an explicit earlier input. Homogeneity and the final dimension bound are
separate obligations.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G]
variable {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}
variable [IsElementaryAbelian 2 V]

noncomputable def pointCoordinates (F : InvariantFlag T V n) (hn : 1 ≤ n) :
    F.Vi 1 ≃* Multiplicative (ZMod 2) :=
  mulEquivOfPrimeCardEq (p := 2) (by simpa using F.card 1 hn) (by simp)

noncomputable def seedCommutatorCharacters (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (hc : ⁅F.U, V⁆ ≤ F.Vi 1) : F.U →* (V →* Multiplicative (ZMod 2)) := by
  have hbot : (⊥ : Subgroup G).subgroupOf (F.Vi 1) = ⊥ := by ext x; simp
  let e0 : (F.Vi 1 ⧸ (⊥ : Subgroup G).subgroupOf (F.Vi 1)) ≃* F.Vi 1 :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  let : IsMulCommutative (F.Vi 1 ⧸ (⊥ : Subgroup G).subgroupOf (F.Vi 1)) :=
    ⟨⟨fun a b => (e0.trans (F.pointCoordinates hn)).injective (by
      rw [map_mul, map_mul, mul_comm])⟩⟩
  have hcent : F.U ≤ centralizer (F.Vi 1 : Set G) :=
    le_centralizer_iff.mp ((F.point_le_ZU hn).trans (centerIn_le_centralizer F.U))
  have hcomm : ⁅F.Vi 1, V⁆ ≤ ⊥ := by
    apply le_bot_iff.mpr
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact (F.le_seed 1).trans (le_centralizer V)
  exact (centralQuotientCommutatorPairing F.U V (F.Vi 1) ⊥
    ((F.le_seed 1).trans (le_conjugateSpanBy V F.H)) hcent hc hcomm).compr₂
      (e0.trans (F.pointCoordinates hn)).toMonoidHom

theorem seedCommutatorCharacters_apply (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (hc : ⁅F.U, V⁆ ≤ F.Vi 1) (u : F.U) (v : V) :
    F.seedCommutatorCharacters hn hc u v =
      F.pointCoordinates hn ⟨⁅(u : G), (v : G)⁆,
        hc (commutator_mem_commutator u.property v.property)⟩ := by
  let : IsMulCommutative (F.Vi 1) := le_centralizer_iff_isMulCommutative.mp
    (((F.le_seed 1).trans (le_centralizer V)).trans (centralizer_le (F.le_seed 1)))
  unfold seedCommutatorCharacters
  rw [MonoidHom.compr₂_apply, centralQuotientCommutatorPairing_apply]
  rfl

theorem seedCommutatorCharacters_eq_one_iff (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (hc : ⁅F.U, V⁆ ≤ F.Vi 1) (u : F.U) (v : V) :
    F.seedCommutatorCharacters hn hc u v = 1 ↔ Commute (u : G) (v : G) := by
  rw [seedCommutatorCharacters_apply, ← (F.pointCoordinates hn).map_one,
    (F.pointCoordinates hn).injective.eq_iff, Subtype.ext_iff]
  exact commutatorElement_eq_one_iff_mul_comm

theorem seedCommutatorCharacters_ker (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (hc : ⁅F.U, V⁆ ≤ F.Vi 1) :
    (F.seedCommutatorCharacters hn hc).ker = (centralizer (V : Set G)).subgroupOf F.U := by
  ext u
  change F.seedCommutatorCharacters hn hc u = 1 ↔ (u : G) ∈ centralizer (V : Set G)
  constructor
  · intro h v hv
    exact ((F.seedCommutatorCharacters_eq_one_iff hn hc u ⟨v, hv⟩).mp
      (congrArg (fun k : V →* Multiplicative (ZMod 2) => k ⟨v, hv⟩) h)).symm.eq
  · intro h
    ext v
    exact (F.seedCommutatorCharacters_eq_one_iff hn hc u v).mpr ((h v v.property).symm)

theorem seedCentralizer_normal (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (hc : ⁅F.U, V⁆ ≤ F.Vi 1) : ((centralizer (V : Set G)).subgroupOf F.U).Normal :=
  F.seedCommutatorCharacters_ker hn hc ▸ inferInstance

theorem seedCommutatorCharacters_flip_ker (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (hc : ⁅F.U, V⁆ ≤ F.Vi 1) (hz : V ⊓ F.ZU = F.Vi 1) :
    (F.seedCommutatorCharacters hn hc).flip.ker = (F.Vi 1).subgroupOf V := by
  ext v
  change (F.seedCommutatorCharacters hn hc).flip v = 1 ↔ (v : G) ∈ F.Vi 1
  rw [← hz]
  rw [ZU, centerIn_eq_inf_centralizer]
  constructor
  · intro h
    refine ⟨v.property, le_conjugateSpanBy V F.H v.property, ?_⟩
    intro u hu
    exact ((F.seedCommutatorCharacters_eq_one_iff hn hc ⟨u, hu⟩ v).mp
      (congrArg (fun k : F.U →* Multiplicative (ZMod 2) => k ⟨u, hu⟩) h)).eq
  · intro h
    ext u
    exact (F.seedCommutatorCharacters_eq_one_iff hn hc u v).mpr (h.2.2 u u.property)

/-- The actual quotient by the relative centralizer is dual to V/V₁. -/
theorem exists_seed_commutator_duality [Finite G] (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (hc : ⁅F.U, V⁆ ≤ F.Vi 1) (hz : V ⊓ F.ZU = F.Vi 1) :
    letI := F.seedCentralizer_normal hn hc
    ∃ e : (F.U ⧸ (centralizer (V : Set G)).subgroupOf F.U) ≃*
        ((V ⧸ (F.Vi 1).subgroupOf V) →* Multiplicative (ZMod 2)),
      ∀ (u : F.U) (v : V),
        e (QuotientGroup.mk' ((centralizer (V : Set G)).subgroupOf F.U) u)
          (QuotientGroup.mk' ((F.Vi 1).subgroupOf V) v) =
            F.seedCommutatorCharacters hn hc u v := by
  let := F.seedCentralizer_normal hn hc
  let f := F.seedCommutatorCharacters hn hc
  obtain ⟨e, he⟩ := MonoidHom.exists_binary_pairing_quotient_duality f.flip
  let qV := QuotientGroup.quotientMulEquivOfEq (F.seedCommutatorCharacters_flip_ker hn hc hz).symm
  let dualTransport : ((V ⧸ f.flip.ker) →* Multiplicative (ZMod 2)) ≃*
      ((V ⧸ (F.Vi 1).subgroupOf V) →* Multiplicative (ZMod 2)) := {
    toFun k := k.comp qV.toMonoidHom
    invFun k := k.comp qV.symm.toMonoidHom
    left_inv k := by ext v; simp
    right_inv k := by ext v; simp
    map_mul' _ _ := rfl }
  refine ⟨(QuotientGroup.quotientMulEquivOfEq
    (F.seedCommutatorCharacters_ker hn hc).symm).trans (e.trans dualTransport), ?_⟩
  exact fun u v => he v u

/-- Simultaneous conjugation by the actual point/seed stabilizer fixes the pairing. -/
theorem seedCommutatorCharacters_equivariant (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (hc : ⁅F.U, V⁆ ≤ F.Vi 1) (j : F.H)
    (hjV : (j : G) ∈ normalizer (V : Set G)) (u : F.U) (v : V) :
    F.seedCommutatorCharacters hn hc (F.uAction j u)
      ⟨(j : G) * v * (j : G)⁻¹, (mem_normalizer_iff.mp hjV v).mp v.property⟩ =
        F.seedCommutatorCharacters hn hc u v := by
  rw [seedCommutatorCharacters_apply, seedCommutatorCharacters_apply]
  apply congrArg (F.pointCoordinates hn)
  apply Subtype.ext
  change ⁅(j : G) * u * (j : G)⁻¹, (j : G) * v * (j : G)⁻¹⁆ = ⁅(u : G), (v : G)⁆
  rw [← conjugate_commutatorElement]
  have hjC := normalizer_le_centralizer_of_card_two (F.Vi 1)
    (by simpa using F.card 1 hn) j.property
  rw [← hjC _ (hc (commutator_mem_commutator u.property v.property)),
    mul_inv_cancel_right]

/-- The source nonabelian application discharges the right radical by 12.8.8(3).
The only commutator input is supplied by the elementary quotient of 12.8.4. -/
theorem exists_seed_commutator_duality_of_nonabelian [Finite G] (F : InvariantFlag T V n)
    (L : Subgroup G) (hn : 1 ≤ n) (hLV : L ≤ normalizer (V : Set G))
    (hirr : ∀ A : Subgroup G, F.Vi 1 ≤ A → A ≤ V →
      F.Li L 1 ≤ normalizer (A : Set G) → A = F.Vi 1 ∨ A = V)
    (hnonab : ¬ IsMulCommutative F.U) (hc : ⁅F.U, V⁆ ≤ F.Vi 1) :
    letI := F.seedCentralizer_normal hn hc
    ∃ e : (F.U ⧸ (centralizer (V : Set G)).subgroupOf F.U) ≃*
        ((V ⧸ (F.Vi 1).subgroupOf V) →* Multiplicative (ZMod 2)),
      (∀ (u : F.U) (v : V),
        e (QuotientGroup.mk' ((centralizer (V : Set G)).subgroupOf F.U) u)
          (QuotientGroup.mk' ((F.Vi 1).subgroupOf V) v) =
            F.seedCommutatorCharacters hn hc u v) ∧
      (∀ (j : F.Li L 1) (u : F.U) (v : V),
        e (QuotientGroup.mk' ((centralizer (V : Set G)).subgroupOf F.U)
            (F.uAction ⟨j, (F.Li_le L 1 j.property).2⟩ u))
          (QuotientGroup.mk' ((F.Vi 1).subgroupOf V)
            ⟨(j : G) * v * (j : G)⁻¹,
              (mem_normalizer_iff.mp (hLV (F.Li_le L 1 j.property).1) v).mp v.property⟩) =
        e (QuotientGroup.mk' ((centralizer (V : Set G)).subgroupOf F.U) u)
          (QuotientGroup.mk' ((F.Vi 1).subgroupOf V) v)) := by
  let := F.seedCentralizer_normal hn hc
  obtain ⟨e, he⟩ := F.exists_seed_commutator_duality hn hc
    (F.seed_inf_center_eq_point L hn hLV hirr hnonab)
  refine ⟨e, he, ?_⟩
  intro j u v
  rw [he, he]
  exact F.seedCommutatorCharacters_equivariant hn hc
    ⟨j, (F.Li_le L 1 j.property).2⟩ (hLV (F.Li_le L 1 j.property).1) u v

/-- The commutator hypothesis follows from the literal elementary quotient. -/
theorem seed_commutator_le_point (F : InvariantFlag T V n)
    [IsMulCommutative (F.tilde F.U)] : ⁅F.U, V⁆ ≤ F.Vi 1 := by
  apply commutator_le.mpr
  intro u hu v hv
  let u' : F.U := ⟨u, hu⟩
  let v' : F.U := ⟨v, le_conjugateSpanBy V F.H hv⟩
  have he : F.tildeMap F.U F.U_le_H ⁅u', v'⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have hk : ⁅u', v'⁆ ∈ (F.tildeMap F.U F.U_le_H).ker := he
  rw [F.tildeMap_U_ker] at hk
  exact hk

/-- The centralizer quotient is elementary abelian, as a consequence of duality. -/
theorem seedCentralizerQuotient_elementary [Finite G]
    (F : InvariantFlag T V n) (hn : 1 ≤ n) (hc : ⁅F.U, V⁆ ≤ F.Vi 1)
    (hz : V ⊓ F.ZU = F.Vi 1) :
    letI := F.seedCentralizer_normal hn hc
    IsElementaryAbelian 2 (F.U ⧸ (centralizer (V : Set G)).subgroupOf F.U) := by
  let := F.seedCentralizer_normal hn hc
  obtain ⟨e, _⟩ := F.exists_seed_commutator_duality hn hc hz
  refine {
    toIsMulCommutative := ⟨⟨fun a b => e.injective (by rw [map_mul, map_mul, mul_comm])⟩⟩
    exponent_dvd_p := ?_ }
  rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
  intro q
  apply e.injective
  ext v
  change e (q ^ 2) v = e 1 v
  rw [map_pow, map_one]
  change (e q v) ^ 2 = 1
  apply Multiplicative.toAdd.injective
  change 2 • (e q v).toAdd = 0
  simp only [nsmul_eq_mul, Nat.cast_ofNat, show (2 : ZMod 2) = 0 by decide, zero_mul]

/-- The commutator duality is a genuine binary linear equivalence. Its evaluation
and simultaneous-conjugation identity specify the actual contragredient action. -/
theorem exists_seed_commutator_linear_duality [Finite G]
    (F : InvariantFlag T V n) (L : Subgroup G) (hn : 1 ≤ n)
    (hLV : L ≤ normalizer (V : Set G))
    (hirr : ∀ A : Subgroup G, F.Vi 1 ≤ A → A ≤ V →
      F.Li L 1 ≤ normalizer (A : Set G) → A = F.Vi 1 ∨ A = V)
    (hnonab : ¬ IsMulCommutative F.U) (hc : ⁅F.U, V⁆ ≤ F.Vi 1) :
    letI := F.seedCentralizer_normal hn hc
    letI := F.seedCentralizerQuotient_elementary hn hc
      (F.seed_inf_center_eq_point L hn hLV hirr hnonab)
    ∃ e : Additive (F.U ⧸ (centralizer (V : Set G)).subgroupOf F.U) ≃ₗ[ZMod 2]
        Module.Dual (ZMod 2) (Additive (V ⧸ (F.Vi 1).subgroupOf V)),
      (∀ (u : F.U) (v : V),
        e (Additive.ofMul (QuotientGroup.mk' ((centralizer (V : Set G)).subgroupOf F.U) u))
          (Additive.ofMul (QuotientGroup.mk' ((F.Vi 1).subgroupOf V) v)) =
            (F.seedCommutatorCharacters hn hc u v).toAdd) ∧
      (∀ (j : F.Li L 1) (u : F.U) (v : V),
        e (Additive.ofMul (QuotientGroup.mk' ((centralizer (V : Set G)).subgroupOf F.U)
            (F.uAction ⟨j, (F.Li_le L 1 j.property).2⟩ u)))
          (Additive.ofMul (QuotientGroup.mk' ((F.Vi 1).subgroupOf V)
            ⟨(j : G) * v * (j : G)⁻¹,
              (mem_normalizer_iff.mp (hLV (F.Li_le L 1 j.property).1) v).mp v.property⟩)) =
        e (Additive.ofMul (QuotientGroup.mk' ((centralizer (V : Set G)).subgroupOf F.U) u))
          (Additive.ofMul (QuotientGroup.mk' ((F.Vi 1).subgroupOf V) v))) := by
  let := F.seedCentralizer_normal hn hc
  let := F.seedCentralizerQuotient_elementary hn hc
    (F.seed_inf_center_eq_point L hn hLV hirr hnonab)
  obtain ⟨e, he, hi⟩ := F.exists_seed_commutator_duality_of_nonabelian L hn hLV hirr hnonab hc
  let a := (e.trans MonoidHom.binaryCharacterEquivLinearDual).toAdditiveLeft
  let l := a.toLinearEquiv (ZMod.map_smul (n := 2) a)
  refine ⟨l, ?_, ?_⟩
  · intro u v
    exact congrArg Multiplicative.toAdd (he u v)
  · intro j u v
    exact congrArg Multiplicative.toAdd (hi j u v)

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
