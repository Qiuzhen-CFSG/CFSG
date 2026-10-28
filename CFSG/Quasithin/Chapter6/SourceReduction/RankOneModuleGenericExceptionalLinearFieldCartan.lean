module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearField
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLocalCartan
public import Theory.NumberTheory.BinaryTorusParity

/-!
# The actual split Cartan and its cubic subgroup

An odd Hall subgroup of N_L(T∩L) is a complement to the prescribed Sylow
intersection. The literal PSL₂(2ⁿ) quotient identifies this complement
with the multiplicative group of its field. It is therefore cyclic of
order 2ⁿ−1. Once the independent parity argument supplies even n,
Cauchy's theorem constructs an order-three subgroup inside that same
Cartan, without changing the compatible right Hall subgroup.

The right Hall order remains explicit: it is the earlier PSL₃(4) Borel
calculation in 5.1.10, not a consequence of odd Hall membership alone.
The final equalities connect the source conclusions C=B and n=2 to the
Cartan equality consumed by the field-four/Borel assembly.

Source: Aschbacher--Smith, Notation 5.1.9 and 5.1.14--20,
printed pp.634,638--644 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L H A B C : Subgroup G} {n : ℕ}

/-- The original left Hall subgroup has the order and cyclic structure of the split torus. -/
theorem CartanPair.left_cyclic_and_card
    (c : CartanPair T L H A B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) :
    IsCyclic A ∧ Nat.card A = 2 ^ n - 1 := by
  obtain ⟨P, hP⟩ := exists_sylow_component hTL
  have hPL : (P : Subgroup L) = (T : Subgroup G).subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [hP, subgroupOf_map_subtype]
  have hAL : A ≤ L := c.left_le.trans inf_le_left
  have hN : (normalizer (P : Set L)).map L.subtype = localBorel T L := by
    change (normalizer ((P : Subgroup L) : Set L)).map L.subtype = _
    rw [hPL, ← localBorel_eq_map]
  have hAN : A.subgroupOf L ≤ normalizer (P : Set L) := by
    apply (map_le_map_iff_of_injective L.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hAL, hN]
    exact c.left_le
  have hOdd : Odd (Nat.card A) := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    intro hd
    apply c.left_hall.p_in_pi_of_p_dvd_card ⟨2, Nat.prime_two⟩ _ rfl
    rwa [Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv]
  have hdis : Disjoint (P : Subgroup L) (A.subgroupOf L) := by
    obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hk, Nat.card_congr (subgroupOfEquivOfLe hAL).toEquiv]
    exact (Nat.prime_two.coprime_iff_not_dvd.mpr hOdd.not_two_dvd_nat).pow_left k
  have hgen : (P : Subgroup L) ⊔ A.subgroupOf L = normalizer (P : Set L) := by
    apply map_injective L.subtype_injective
    rw [Subgroup.map_sup, hP, map_subgroupOf_eq_of_le hAL, hN,
      c.left_sup_intersection hTL]
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hpsl
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  let e' := e.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm
  let q := e'.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 L := by
    ext x
    exact e'.map_eq_one_iff.trans (QuotientGroup.eq_one_iff _)
  obtain ⟨f⟩ := Matrix.SpecialLinearGroup.sylow_normalizer_complement_equiv_units
    q hq P (hk ▸ pCore_isPGroup.le_sylow_of_normal P)
    (A.subgroupOf L) hAN hdis hgen
  let a := (subgroupOfEquivOfLe hAL).symm.trans f
  exact ⟨isCyclic_of_injective a.toMonoidHom a.injective,
    (Nat.card_congr a.toEquiv).trans (by rw [Nat.card_units, hF])⟩

/-- Parity supplies the cubic inside the actual compatible Cartan pair. -/
theorem CartanPair.exists_linearFieldCartan_of_even
    (c : CartanPair T L H A B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (heven : Even n) (hB : Nat.card B = 3) :
    ∃ C : Subgroup G, LinearFieldCartan T L H A B C n := by
  obtain ⟨hcyc, hcard⟩ := c.left_cyclic_and_card hTL hpsl
  have hd : 3 ∣ Nat.card A := hcard ▸
    (Nat.BinaryTorusParity.three_dvd_sub_one_iff n).mpr heven
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := A) 3 hd
  let C := (zpowers x).map A.subtype
  have hC : Nat.card C = 3 := by
    rw [card_map_of_injective A.subtype_injective, Nat.card_zpowers, hx]
  exact ⟨C, c, hcyc, hcard, hB, map_subtype_le _, hC⟩

/-- At field order four the cubic is the entire left Cartan. -/
theorem LinearFieldCartan.left_eq_cubic_of_exponent_eq_two
    (c : LinearFieldCartan T L H A B C n) (hn : n = 2) : A = C := by
  apply (eq_of_le_of_card_ge c.cubic_le _).symm
  rw [c.left_card, c.cubic_card, hn]
  norm_num

/-- The separate numerical and cubic-equality source conclusions imply full Cartan equality. -/
theorem LinearFieldCartan.left_eq_right_of_cubic_eq
    (c : LinearFieldCartan T L H A B C n) (hn : n = 2) (hCB : C = B) : A = B :=
  (c.left_eq_cubic_of_exponent_eq_two hn).trans hCB

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
