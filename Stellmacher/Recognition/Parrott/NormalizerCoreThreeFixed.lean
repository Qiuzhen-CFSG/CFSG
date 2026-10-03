module

public import Stellmacher.Recognition.Parrott.NormalizerCoreThreeCenters
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The fixed line in the second elementary subgroup

An order-three group acting on F has two, eight, or 32 fixed points. The
last case fixes z. In the eight-point case, the fixed subgroup intersects
E∩F in at least four points, supplying a fixed e outside Z(U). Then
Z(U) and e generate E∩F, so Q normalizes E∩F, its centralizer E∨F,
and the derived line ⟨z⟩. This again fixes z, a contradiction.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
p.677, the calculation C_F(Q)=⟨v⟩.
-/

open Subgroup
open scoped IsMulCommutative

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The fixed subgroup of F equals the fixed subgroup of the actual omega
center, for every Sylow three-subgroup Q of the supplied normalizer. -/
public theorem normalizer_three_fixed_elementary (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let U := omega₁ K (p := 2)
    let A := (Q : Subgroup N).map N.subtype
    let Z := (center U).map ((N.subtype.comp K.subtype).comp U.subtype)
    d.F ⊓ centralizer (A : Set G) = Z ⊓ centralizer (A : Set G) := by
  intro N K U A Z
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  let B := E ⊓ d.F
  let C := d.F ⊓ centralizer (A : Set G)
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : IsElementaryAbelian 2 d.F := d.elementary
  have hAN : A ≤ N := map_subtype_le _
  have hAcard : Nat.card A = 3 :=
    (card_map_of_injective N.subtype_injective).trans (d.normalizer_three_card h hN hproper Q)
  have hA : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by simpa using hAcard)
  have hZB : Z ≤ B := (d.normalizer_core_omega_structure h hN hproper).2.2.1
  have hZcard : Nat.card Z = 8 :=
    (card_map_of_injective ((N.subtype_injective.comp K.subtype_injective).comp
      U.subtype_injective)).trans (d.normalizer_core_omega_structure h hN hproper).2.1
  have hZfix : Nat.card (Z ⊓ centralizer (A : Set G) : Subgroup G) = 2 :=
    (d.normalizer_three_center_fixed_cards h hN hproper Q).2
  have hnot32 : Nat.card C ≠ 32 := by
    intro hc
    have heq : C = d.F := eq_of_le_of_card_ge inf_le_left (by rw [hc, d.card])
    have hzC : z ∈ C := heq.symm ▸ d.z_mem_inf.2
    apply d.normalizer_three_not_centralizes h hN hproper Q
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (hzC.2 a ha)
  have hnot8 : Nat.card C ≠ 8 := by
    intro hc
    have hCB : C ≤ normalizer (B : Set G) := by
      apply le_trans (show C ≤ centralizer (B : Set G) from ?_) (Subgroup.centralizer_le_normalizer _)
      intro c hc b hb
      exact congrArg d.F.subtype (mul_comm (⟨b, hb.2⟩ : d.F) ⟨c, hc.1⟩)
    have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes B C hCB
    have hsup : Nat.card (B ⊔ C : Subgroup G) ≤ 32 := by
      have hh := card_le_of_le (sup_le (show B ≤ d.F from inf_le_right)
        (show C ≤ d.F from inf_le_left))
      rwa [d.card] at hh
    have hBcard : Nat.card B = 16 := d.inf_card
    rw [hBcard, hc] at hprod
    have hlarge : 4 ≤ Nat.card (B ⊓ C : Subgroup G) := by nlinarith
    have hnot : ¬ B ⊓ C ≤ Z := by
      intro hh
      have hh' : B ⊓ C ≤ Z ⊓ centralizer (A : Set G) :=
        le_inf hh (inf_le_right.trans inf_le_right)
      have hsmall := card_le_of_le hh'
      rw [hZfix] at hsmall
      omega
    obtain ⟨e, he, heZ⟩ := SetLike.not_le_iff_exists.mp hnot
    have hepow : e ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian e he.1.2
    have heN : e ∈ N := d.sylow_le_normalizer (d.le_sylow he.1.2)
    have hspan : Z ⊔ zpowers e = B := by
      apply eq_of_le_of_card_ge (sup_le hZB (zpowers_le.mpr he.1))
      rw [card_sup_zpowers_of_normalizing_involution Z e hepow heZ
        (d.normalizer_core_centers_normalized.2 heN), hZcard, hBcard]
    have hAe : A ≤ normalizer (zpowers e : Set G) := by
      apply le_trans (show A ≤ centralizer (zpowers e : Set G) from ?_) (Subgroup.centralizer_le_normalizer _)
      rw [zpowers_eq_closure, centralizer_closure]
      intro a ha
      exact mem_centralizer_singleton_iff.mpr (he.2.2 a ha)
    have hAB : A ≤ normalizer (B : Set G) := by
      rw [← hspan]
      exact (le_inf (hAN.trans d.normalizer_core_centers_normalized.2) hAe).trans
        (normalizer_inf_normalizer_le_normalizer_sup Z (zpowers e))
    have hAjoin : A ≤ normalizer ((E ⊔ d.F : Subgroup G) : Set G) := by
      rw [← d.elementary_inf_centralizer h]
      exact hAB.trans (normalizer_le_normalizer_centralizer B)
    exact d.normalizer_three_not_centralizes h hN hproper Q
      (hAjoin.trans (normalizer_le_centralizer_of_characteristic_involution
        (E ⊔ d.F) (commutator (E ⊔ d.F : Subgroup G)) z h.involution (d.elementary_join_commutator h)))
  have hCcard : Nat.card C = 2 := by
    have hmod := A.card_modEq_card_inf_centralizer d.F hA hAN
    have hd : Nat.card C ∣ 2 ^ 5 := by
      simpa only [d.card, show 2 ^ 5 = (32 : ℕ) from rfl] using
        card_dvd_of_le (show C ≤ d.F from inf_le_left)
    obtain ⟨n, hn, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    rw [d.card] at hmod
    change 32 % 3 = Nat.card C % 3 at hmod
    rw [hcard] at hmod hnot8 hnot32 ⊢
    interval_cases n <;> norm_num at *
  apply (eq_of_le_of_card_ge (inf_le_inf_right _ (hZB.trans inf_le_right)) ?_).symm
  change Nat.card C ≤ Nat.card (Z ⊓ centralizer (A : Set G) : Subgroup G)
  rw [hCcard, hZfix]

/-- A reusable compatible witness package, including both fixed-line
identifications, for an arbitrary supplied Sylow three-subgroup. -/
public theorem exists_normalizer_three_fixed_generators (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let U := omega₁ K (p := 2)
    let A := (Q : Subgroup N).map N.subtype
    let ZK := (center K).map (N.subtype.comp K.subtype)
    let ZU := (center U).map ((N.subtype.comp K.subtype).comp U.subtype)
    ∃ t v : G, t ∈ E ⊓ d.F ∧ v ∈ E ⊓ d.F ∧
      orderOf t = 2 ∧ orderOf v = 2 ∧ t ∉ zpowers z ∧ v ∉ ZK ∧
      ZK = zpowers z ⊔ zpowers t ∧ ZU = (zpowers z ⊔ zpowers t) ⊔ zpowers v ∧
      (∃ q : Q, ((q : N) : G) * z * ((q : N) : G)⁻¹ = t) ∧
      v ∈ centralizer (A : Set G) ∧ ZU ⊓ centralizer (A : Set G) = zpowers v ∧
      d.F ⊓ centralizer (A : Set G) = zpowers v ∧ ¬ IsConj z v := by
  intro H J E N K U A ZK ZU
  obtain ⟨t, v, ht, hv, ht2, hv2, htz, hvZ, hZK, hZU, hq, hvC, hfix, hnc⟩ :=
    d.exists_normalizer_three_center_generators h hN hproper Q
  exact ⟨t, v, ht, hv, ht2, hv2, htz, hvZ, hZK, hZU, hq, hvC, hfix,
    (d.normalizer_three_fixed_elementary h hN hproper Q).trans hfix, hnc⟩

end Stellmacher.Recognition.ParrottSecondElementaryData
