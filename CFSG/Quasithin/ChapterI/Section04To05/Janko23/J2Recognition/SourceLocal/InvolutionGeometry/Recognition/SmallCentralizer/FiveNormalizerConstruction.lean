module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer.FiveNormalizerConsequences
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer.FiveNormalizerConstruction.LocalDihedral
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer.FiveNormalizerConstruction.TwoPart
public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Constructing the Sylow-five normalizer data

The seed and local census give an actual dihedral isomorphism for N_H(P).
The centralizer and Frattini arguments give the ambient normalizer two-part
four, and Sylow congruence with |G| = 51840 then forces |N_G(P)| = 540.

For a normalizer of order 540 acting nontrivially on its subgroup of order
five, the action kernel has order 135 or 270. In the latter case Burnside
transfer produces a normal odd complement of order 135. Sylow counting at
order 135 gives a unique Sylow three-subgroup of order 27. Its characteristic
three-core is normal at each required step, and comparison with an ambient
Sylow subgroup identifies the full three-core. All images use the literal
normalizer subtype map.

A reflection in the local dihedral normalizer gives the required inverting
involution. Combining these constructions proves `exists_fiveNormalizerData`
from the seed, local census and ambient order 51840, with no further premise
about the normalizer. The conditional assembly is retained for callers with
explicit local normalizer calculations.

Source: Aschbacher, *Sporadic Groups* (1994), proof of 47.1, printed p.260.
-/

open Subgroup

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer

variable {G : Type*} [Group G] [Finite G]
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem threeCore_card_of_card135 {K : Type*} [Group K] [Finite K] (hK : Nat.card K = 135) :
    Nat.card (pCore 3 K) = 27 := by
  let T : Sylow 3 K := Classical.choice inferInstance
  have hT : Nat.card T = 27 := by
    rw [T.card_eq_multiplicity, hK]
    decide +kernel
  have hi : (T : Subgroup K).index = 5 := by
    have := (T : Subgroup K).card_mul_index
    rw [hT, hK] at this
    omega
  have hcount : Nat.card (Sylow 3 K) = 1 := by
    have hd := T.card_dvd_index
    rw [hi] at hd
    rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd with h | h
    · exact h
    · have hm := card_sylow_modEq_one 3 K
      rw [h] at hm
      norm_num [Nat.ModEq] at hm
  let _ : Subsingleton (Sylow 3 K) := (Nat.card_eq_one_iff_unique.mp hcount).1
  let _ : (T : Subgroup K).Normal := T.normal_of_subsingleton
  have he : pCore 3 K = (T : Subgroup K) := by
    exact le_antisymm (pCore_isPGroup.le_sylow_of_normal T)
      (le_sSup ⟨inferInstance, T.isPGroup'⟩)
  rw [he]
  exact hT

private theorem threeCore_card_of_normal_subgroup {K : Type*} [Group K] [Finite K]
    (M : Subgroup K) [M.Normal]
    (hK : (Nat.card K).factorization 3 = 3)
    (hM : Nat.card (pCore 3 M) = 27) : Nat.card (pCore 3 K) = 27 := by
  let T : Sylow 3 K := Classical.choice inferInstance
  have hT : Nat.card T = 27 := by rw [T.card_eq_multiplicity, hK]; rfl
  have hle : (pCore 3 M).map M.subtype ≤ pCore 3 K :=
    le_sSup ⟨inferInstance, pCore_isPGroup.map M.subtype⟩
  apply Nat.le_antisymm
  · exact hT ▸ Nat.le_of_dvd Nat.card_pos (card_dvd_of_le (pCore_isPGroup.le_sylow_of_normal T))
  · have hm : Nat.card ((pCore 3 M).map M.subtype) = 27 := by
      rw [card_map_of_injective M.subtype_injective, hM]
    exact hm ▸ Nat.le_of_dvd Nat.card_pos (card_dvd_of_le hle)

private theorem threeCore_card_of_card270 {K : Type*} [Group K] [Finite K] (hK : Nat.card K = 270) :
    Nat.card (pCore 3 K) = 27 := by
  let T : Sylow 2 K := Classical.choice inferInstance
  have hT : Nat.card T = 2 := by
    rw [T.card_eq_multiplicity, hK]
    decide +kernel
  have hcyc : IsCyclic T := isCyclic_of_prime_card hT
  have hmin : (Nat.card K).minFac = 2 := by rw [hK]; decide
  let f := MonoidHom.transferSylow T (hcyc.normalizer_le_centralizer hmin)
  have hcomp : f.ker.IsComplement' (T : Subgroup K) := by
    simpa [f] using hcyc.isComplement' hmin
  have hk : Nat.card f.ker = 135 := by
    have hc : Nat.card f.ker = (T : Subgroup K).index := hcomp.card_left
    rw [hc]
    have := (T : Subgroup K).card_mul_index
    rw [hT, hK] at this
    omega
  exact threeCore_card_of_normal_subgroup f.ker (by rw [hK]; decide +kernel) (threeCore_card_of_card135 hk)


private theorem threeCore_card_of_nontrivial_five_action {K A : Type*} [Group K] [Finite K] [Group A] [Finite A]
    (hK : Nat.card K = 540) (hA : Nat.card A = 5)
    (f : K →* MulAut A) (hf : ∃ k : K, f k ≠ 1) : Nat.card (pCore 3 K) = 27 := by
  let _ : IsCyclic A := isCyclic_of_prime_card hA
  have hAut : Nat.card (MulAut A) = 4 := by rw [IsCyclic.card_mulAut, hA]; decide
  have hd : Nat.card f.range ∣ 2 ^ 2 := by
    simpa only [hAut, Nat.reducePow] using f.range.card_subgroup_dvd_card
  have hne : Nat.card f.range ≠ 1 := by
    intro hh
    have he : f.range = ⊥ := card_eq_one.mp hh
    obtain ⟨k, hk⟩ := hf
    have ht : f k ∈ (⊥ : Subgroup (MulAut A)) := he ▸ (show f k ∈ f.range from ⟨k, rfl⟩)
    exact hk ht
  obtain ⟨j, hj, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hprod := f.ker.card_mul_index
  rw [index_ker] at hprod
  change Nat.card f.ker * Nat.card f.range = Nat.card K at hprod
  rw [hK, he] at hprod
  apply threeCore_card_of_normal_subgroup f.ker (by rw [hK]; decide +kernel)
  interval_cases j
  · exact (hne he).elim
  · exact threeCore_card_of_card270 (K := f.ker) (by norm_num only [Nat.reducePow] at hprod; omega)
  · exact threeCore_card_of_card135 (K := f.ker) (by norm_num only [Nat.reducePow] at hprod; omega)


/-- The actual ambient image of the normalizer three-core has order 27.
The inverting action supplies a proper centralizer, and transfer supplies
its normal odd complement before the three-core is identified. -/
public theorem normalizerThreeCore_card_of_card540_and_inverter (D : Seed G)
    (P : Sylow 5 (involutionCentralizer D.z))
    (hN : Nat.card (fiveNormalizer D P) = 540)
    (s : normalizer ((P : Subgroup (involutionCentralizer D.z)) : Set (involutionCentralizer D.z)))
    (hs : ∀ p ∈ ambientFive D P,
      ((s : involutionCentralizer D.z) : G) * p *
        ((s : involutionCentralizer D.z) : G)⁻¹ = p⁻¹) :
    Nat.card (normalizerThreeCore D P) = 27 := by
  let H := involutionCentralizer D.z
  let A := ambientFive D P
  have hsN : ((s : H) : G) ∈ fiveNormalizer D P := by
    apply (P : Subgroup H).le_normalizer_map H.subtype
    exact mem_map.mpr ⟨s, s.property, rfl⟩
  let sN : fiveNormalizer D P := ⟨s, hsN⟩
  let f := A.normalizerMonoidHom
  have hA : Nat.card A = 5 := ambientFive_card D P
  have hnontriv : ∃ k : fiveNormalizer D P, f k ≠ 1 := by
    refine ⟨sN, ?_⟩
    intro he
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := A) 5 (by rw [hA])
    have hfix : ((s : H) : G) * (a : G) * ((s : H) : G)⁻¹ = a :=
      congrArg Subtype.val (congrArg (fun α : MulAut A => α a) he)
    have hinv : (a : G) = (a : G)⁻¹ := hfix.symm.trans (hs a a.property)
    have hsq : a ^ 2 = 1 := Subtype.ext (by
      change (a : G) ^ 2 = 1
      simpa only [pow_two] using (mul_eq_one_iff_eq_inv.mpr hinv))
    have hd := orderOf_dvd_of_pow_eq_one hsq
    rw [ha] at hd
    norm_num at hd
  change Nat.card ((pCore 3 (fiveNormalizer D P)).map (fiveNormalizer D P).subtype) = 27
  rw [card_map_of_injective (fiveNormalizer D P).subtype_injective]
  exact threeCore_card_of_nontrivial_five_action hN hA f hnontriv




private theorem reflection_inverts_five (a : DihedralGroup 10) (ha : orderOf a ∣ 5) :
    DihedralGroup.sr 0 * a * (DihedralGroup.sr 0)⁻¹ = a⁻¹ := by
  cases a with
  | r i => simp
  | sr i => simp only [DihedralGroup.orderOf_sr] at ha; norm_num at ha

/-- A reflection in the local dihedral group inverts the literal embedded
Sylow five-subgroup and is distinct from the distinguished central involution. -/
public theorem exists_local_inverter_of_dihedral (D : Seed G)
    (P : Sylow 5 (involutionCentralizer D.z))
    (e : normalizer ((P : Subgroup (involutionCentralizer D.z)) : Set (involutionCentralizer D.z)) ≃*
      DihedralGroup 10) :
    ∃ s : normalizer ((P : Subgroup (involutionCentralizer D.z)) : Set (involutionCentralizer D.z)),
      orderOf s = 2 ∧ ((s : involutionCentralizer D.z) : G) ≠ D.z ∧
      ∀ p ∈ ambientFive D P,
        ((s : involutionCentralizer D.z) : G) * p *
          ((s : involutionCentralizer D.z) : G)⁻¹ = p⁻¹ := by
  let H := involutionCentralizer D.z
  let N := normalizer ((P : Subgroup H) : Set H)
  let s : N := e.symm (DihedralGroup.sr 0)
  have hs : orderOf s = 2 :=
    (e.symm.orderOf_eq (DihedralGroup.sr 0)).trans (DihedralGroup.orderOf_sr 0)
  have hP : Nat.card P = 5 := by
    rw [P.card_eq_multiplicity, D.localType.centralizer_card]
    decide +kernel
  have hi : ∀ p ∈ ambientFive D P,
      ((s : H) : G) * p * ((s : H) : G)⁻¹ = p⁻¹ := by
    rintro p ⟨a, ha, rfl⟩
    let aN : N := ⟨a, le_normalizer ha⟩
    have hd : orderOf (e aN) ∣ 5 := by
      rw [e.orderOf_eq, ← orderOf_coe aN]
      exact hP ▸ (P : Subgroup H).orderOf_dvd_natCard ha
    have he : s * aN * s⁻¹ = aN⁻¹ := by
      apply e.injective
      simpa only [map_mul, map_inv, s, e.apply_symm_apply] using
        reflection_inverts_five (e aN) hd
    exact congrArg (fun n : N => ((n : H) : G)) he
  refine ⟨s, hs, ?_, hi⟩
  intro he
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := P) 5 (by rw [hP])
  have ham : ((a : H) : G) ∈ ambientFive D P := mem_map_of_mem H.subtype a.property
  have hc : D.z * ((a : H) : G) * D.z⁻¹ = ((a : H) : G) :=
    mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp (a : H).property).symm
  have heq : ((a : H) : G) = ((a : H) : G)⁻¹ := by
    simpa only [he, hc] using hi _ ham
  have hsq : a ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change ((a : H) : G) ^ 2 = 1
    simpa only [pow_two] using (mul_eq_one_iff_eq_inv.mpr heq)
  have hd := orderOf_dvd_of_pow_eq_one hsq
  rw [ha] at hd
  norm_num at hd

/-- Construct the complete literal normalizer data from the two local
normalizer calculations. In particular no three-core order or inverter is
assumed. The order 51840 is the separate Thompson-formula input. -/
public theorem fiveNormalizerData_of_local_equiv_and_twoPart (D : Seed G)
    (P : Sylow 5 (involutionCentralizer D.z))
    (e : normalizer ((P : Subgroup (involutionCentralizer D.z)) : Set (involutionCentralizer D.z)) ≃*
      DihedralGroup 10)
    (h2 : (Nat.card (fiveNormalizer D P)).factorization 2 = 2)
    (hG : Nat.card G = 51840) : Nonempty (FiveNormalizerData D) := by
  obtain ⟨s, hs, hsz, hi⟩ := exists_local_inverter_of_dihedral D P e
  exact ⟨{
    P := P
    localEquiv := e
    twoPart := h2
    core_card := normalizerThreeCore_card_of_card540_and_inverter D P
      (fiveNormalizer_card_of_twoPart D P hG h2) s hi
    s := s
    s_order := hs
    s_ne_z := hsz
    s_inverts_five := hi }⟩

/-- Construct the literal Sylow-five normalizer data in the hypothetical
small-centralizer branch of 47.1. The source census supplies the local
dihedral isomorphism, and the ambient two-part, three-core order and inverting
involution are all proved. The ambient order is supplied by Thompson's formula
in the source-theorem assembly. -/
public theorem exists_fiveNormalizerData (D : Seed G) (L : LocalCensus D)
    (hG : Nat.card G = 51840) : Nonempty (FiveNormalizerData D) := by
  let P : Sylow 5 (involutionCentralizer D.z) := Classical.choice inferInstance
  obtain ⟨e⟩ := exists_local_dihedral_equiv D L P
  exact fiveNormalizerData_of_local_equiv_and_twoPart D P e
    (fiveNormalizer_twoPart_of_local_dihedral D P e) hG

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer
