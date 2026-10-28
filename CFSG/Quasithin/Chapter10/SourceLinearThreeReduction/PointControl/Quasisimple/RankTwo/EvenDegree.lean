module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.CentralQuotient
public import Theory.SpecificGroups.Triality.BinaryLocalSections
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.TwoLocalOrders

/-!
# Exceptional rank-two exclusions for even-degree binary quotients

A central quotient preserves the original L/O₂(L). A factor five in
that quotient excludes ³D₄(2), whose actual carrier is five-free. The
noncentral two-core center in a Ree image supplies a nonidentity local
two-subgroup; its normalizer is fifteen-free. Every even-degree PSL₂(2ⁿ)
quotient has order divisible by fifteen, so both exceptions are excluded.

Source: Aschbacher--Smith A.3.12 and 10.2.9, printed pp.47--48,750--751.
RankTwo.Source applies these results to the complete rank-two catalogue,
without an A₅ marking or a module irreducibility hypothesis.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple.RankTwo
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)
include D c

/-- Binary triality has no factor five; central passage preserves the
original two-core quotient and hence its factor five. -/
theorem not_binary_triality_of_five
    (h5 : 5 ∣ Nat.card (L ⧸ pCore 2 L))
    (eI : (I ⧸ center I) ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) : False := by
  let A := (L.subgroupOf I).map (eI.toMonoidHom.comp (QuotientGroup.mk' (center I)))
  have hd := card_quotient_dvd_card (pCore 2 A)
  have hc := Nat.card_congr (markedCoreQuotientEquiv D c.strict.le eI).toEquiv
  have h5A : 5 ∣ Nat.card A := (hc ▸ h5).trans hd
  have hh := h5A.trans A.card_subgroup_dvd_card
  change 5 ∣ Nat.card (Triality.Standard.Carrier
    (Triality.Standard.binaryParameters 1 Nat.zero_lt_one)) at hh
  rw [Triality.Standard.ConcreteBruhat.FixedCellCount.card_carrier,
    Triality.Standard.ConcreteBruhat.FixedCellCount.card_borel] at hh
  norm_num [Triality.Standard.Parameters.q,Triality.Standard.binaryParameters] at hh

/-- Three and five cannot both divide the original quotient in a Ree
containing component: its nonzero core has a fifteen-free normalizer. -/
theorem not_ree_of_fifteen
    (h15 : 15 ∣ Nat.card (L ⧸ pCore 2 L))
    {m : ℕ} (hm : 1 ≤ m) (eI : (I ⧸ center I) ≃* ReeF4.Model m) : False := by
  let A := (L.subgroupOf I).map (eI.toMonoidHom.comp (QuotientGroup.mk' (center I)))
  have hcore : pCore 2 A ≠ ⊥ := by
    intro hz
    apply marked_core_center_not_central D c.strict.le eI
    rintro _ ⟨z,_,rfl⟩
    have he : (z : A) = 1 := mem_bot.mp (hz ▸ z.property)
    change (z : A) ∈ center A
    rw [he]
    exact one_mem _
  let R := (pCore 2 A).map A.subtype
  have hR : R ≠ ⊥ := fun hz => hcore
    ((map_eq_bot_iff_of_injective _ A.subtype_injective).mp hz)
  have hAN : A ≤ normalizer (R : Set (ReeF4.Model m)) := A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (pCore 2 A))
  apply ReeF4.ConverseParabolics.normalizer_fifteen_free hm R hR (pCore_isPGroup.map A.subtype)
  have hc := Nat.card_congr (markedCoreQuotientEquiv D c.strict.le eI).toEquiv
  exact (hc ▸ h15).trans ((card_quotient_dvd_card (pCore 2 A)).trans (card_dvd_of_le hAN))

omit D c in
private theorem even_binary_fifteen {H : Type*} [Group H]
    {n : ℕ} (hn : 0 < n) (he : Even n)
    (hm : ClassicalGroup.IsPSL H 2 (2 ^ n)) : 15 ∣ Nat.card H := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let d := e.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm
  rw [Nat.card_congr d.toEquiv,GorensteinWalter.sl2_card_formula,hF]
  have hpos : 1 ≤ (2 ^ n) ^ 2 := one_le_pow₀ (one_le_pow₀ (by decide : (1 : ℕ) ≤ 2))
  have hthree : (2 ^ n) ^ 2 % 3 = 1 := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
    norm_num [Nat.pow_mod]
  have hfive : (2 ^ n) ^ 2 % 5 = 1 := by
    obtain ⟨k,rfl⟩ := he
    rw [← pow_mul, show (k + k) * 2 = 4 * k by omega, pow_mul]
    norm_num [Nat.pow_mod]
  have hsub := Nat.sub_add_cancel hpos
  have h3 : 3 ∣ (2 ^ n) ^ 2 - 1 := by omega
  have h5 : 5 ∣ (2 ^ n) ^ 2 - 1 := by omega
  exact dvd_mul_of_dvd_right ((by decide : Nat.Coprime 3 5).mul_dvd_of_dvd_of_dvd h3 h5) _

/-- Every even-degree rank-one quotient excludes the binary triality endpoint. -/
theorem not_binary_triality_of_even_binary_quotient {n : ℕ} (hn : 0 < n) (he : Even n)
    (hm : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (eI : (I ⧸ center I) ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) : False :=
  not_binary_triality_of_five D c ((by decide : 5 ∣ 15).trans (even_binary_fifteen hn he hm)) eI

/-- Every even-degree rank-one quotient excludes every large Ree component. -/
theorem not_ree_of_even_binary_quotient {n : ℕ} (hn : 0 < n) (he : Even n)
    (hm : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {m : ℕ} (hmpos : 1 ≤ m) (eI : (I ⧸ center I) ≃* ReeF4.Model m) : False :=
  not_ree_of_fifteen D c (even_binary_fifteen hn he hm) hmpos eI

end CFSG.Quasithin.Chapter10.PointControl.Quasisimple.RankTwo
