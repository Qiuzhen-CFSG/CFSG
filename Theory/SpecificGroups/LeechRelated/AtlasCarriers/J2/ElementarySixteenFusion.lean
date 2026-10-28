module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ElementarySixteenFusion.Checks
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RankOneFourNormalizer
import Mathlib.Tactic.FinCases

/-!
# Fusion distinguishes a four inside every Hall–Janko elementary sixteen

In the fixed Sylow, an elementary sixteen contains the distinguished four.
The latter consists exactly of the elements of the sixteen having a fixed
point in the native degree-100 action. Its normalizer therefore normalizes
that four and lies in the previously computed radical normalizer of order
1152. Sylow conjugacy gives the resulting factor-five obstruction for every
elementary sixteen in the actual J₂ carrier.

This is the J₂ model calculation used in Aschbacher–Smith 13.5.15, p.921.
The finite input uses the original ATLAS J2G1-p100B0 permutation tables.
-/

public section
namespace Sporadic.LeechRelated.J2.ElementarySixteenFusion
open Theory.GroupTheory Subgroup ExceptionalParabolics GeneratorPair Seed PairNormalizer
open PairNormalizer.SylowData RankOneFourNormalizer Checks

private theorem sElement_mem_four_iff (i : Fin 128) :
    sElement i ∈ four ↔ i ∈ fourIndices := by
  constructor
  · intro hi
    obtain ⟨j, hj⟩ := exists_fourElement hi
    have he : sElement
        (Fin.castLE (by decide : 64 ≤ 128) (RankOneFourNormalizer.Checks.fourIndex j)) =
        sElement i := by
      convert hj using 1
      fin_cases j <;> rfl
    have he' := sElement_injective he
    rw [← he']
    fin_cases j <;> decide
  · intro hi
    simp only [fourIndices, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact fourElement_mem 0
    · exact fourElement_mem 1
    · exact fourElement_mem 2
    · exact fourElement_mem 3

private theorem involutionIndex_of_mem (W : Subgroup Carrier)
    [IsElementaryAbelian 2 W] {i : Fin 128} (hi : sElement i ∈ W) :
    involutionIndex i := by
  have hs : inclusion (sElement i) * inclusion (sElement i) = 1 := by
    rw [← map_mul, ← pow_two, elemPow_eq_one_of_isElementaryAbelian _ hi, map_one]
  rw [sElement_inclusion] at hs
  exact ⟨congrArg (fun p : Equiv.Perm (Fin 100) => p 0) hs,
    congrArg (fun p : Equiv.Perm (Fin 100) => p 1) hs⟩

/-- The distinguished four is precisely the fixed-point-bearing part of an
elementary sixteen in the fixed Sylow. -/
theorem four_iff_mem_and_fixedPoint (W : Subgroup Carrier) (hWs : W ≤ s)
    [IsElementaryAbelian 2 W] (hc : Nat.card W = 16) (x : Carrier) :
    x ∈ four ↔ x ∈ W ∧ (inclusion x).support.card < 100 := by
  classical
  have hnot : ¬ W ≤ four := by
    intro h
    have hh := card_le_of_le h
    rw [hc, card_four] at hh
    omega
  obtain ⟨a, ha, hafour⟩ := Set.not_subset.mp hnot
  obtain ⟨i, hi⟩ := exists_sElement (hWs ha)
  have hiW : sElement i ∈ W := hi.symm ▸ ha
  have hinot : i ∉ fourIndices := by
    intro h
    exact hafour (hi ▸ (sElement_mem_four_iff i).mpr h)
  let idx : W → Fin 128 := fun y => Classical.choose (exists_sElement (hWs y.property))
  have hidx (y : W) : sElement (idx y) = (y : Carrier) :=
    Classical.choose_spec (exists_sElement (hWs y.property))
  have hidxinj : Function.Injective idx := by
    intro y z hyz
    apply Subtype.ext
    exact (hidx y).symm.trans ((congrArg sElement hyz).trans (hidx z))
  have hidxmem (y : W) : idx y ∈ commutingInvolutions i := by
    have hyW : sElement (idx y) ∈ W := (hidx y).symm ▸ y.property
    have hh := congrArg (fun z : W => inclusion (z : Carrier))
      (mul_comm' (⟨sElement i, hiW⟩ : W) ⟨sElement (idx y), hyW⟩)
    change inclusion (sElement i * sElement (idx y)) =
      inclusion (sElement (idx y) * sElement i) at hh
    simp only [map_mul, sElement_inclusion] at hh
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, involutionIndex_of_mem W hyW,
      congrArg (fun p : Equiv.Perm (Fin 100) => p 0) hh,
      congrArg (fun p : Equiv.Perm (Fin 100) => p 1) hh⟩
  let f : W → ↥(commutingInvolutions i) := fun y => ⟨idx y, hidxmem y⟩
  have hfinj : Function.Injective f := fun y z h => hidxinj (congrArg Subtype.val h)
  have hbound := Nat.card_le_card_of_injective f hfinj
  have hcard : Nat.card ↥(commutingInvolutions i) = (commutingInvolutions i).card := by
    simp
  rw [hc, hcard] at hbound
  obtain hsmall | ⟨hlarge, hfour, hrad⟩ :=
    commuting_involutions_check i (involutionIndex_of_mem W hiW) hinot
  · omega
  have hsurj : Function.Surjective f :=
    (hfinj.bijective_of_nat_card_le (by rw [hc, hcard, hlarge])).2
  have hfourW : four ≤ W := by
    intro y hy
    have hys : y ∈ s := by
      obtain ⟨k, rfl⟩ := exists_fourElement hy
      exact q₂_le_s (qElement_mem (RankOneFourNormalizer.Checks.fourIndex k))
    obtain ⟨j, hj⟩ := exists_sElement hys
    have hjfour : j ∈ fourIndices := (sElement_mem_four_iff j).mp (hj.symm ▸ hy)
    obtain ⟨z, hz⟩ := hsurj ⟨j, hfour hjfour⟩
    have hzj : idx z = j := congrArg Subtype.val hz
    have hzy : (z : Carrier) = y := (hidx z).symm.trans ((congrArg sElement hzj).trans hj)
    exact hzy ▸ z.property
  have hfixed (y : W) : (inclusion (y : Carrier)).support.card < 100 ↔ (y : Carrier) ∈ four := by
    rw [← hidx y, sElement_inclusion]
    exact (fixed_point_check (idx y) (hrad _ (hidxmem y))
      (involutionIndex_of_mem W ((hidx y).symm ▸ y.property))).trans
      (sElement_mem_four_iff (idx y)).symm
  constructor
  · intro hx
    exact ⟨hfourW hx, (hfixed ⟨x, hfourW hx⟩).mpr hx⟩
  · rintro ⟨hx, hf⟩
    exact (hfixed ⟨x, hx⟩).mp hf

/-- The full normalizer of an elementary sixteen in the fixed Sylow lies in
the intrinsic radical normalizer. -/
theorem normalizer_le_p₂ (W : Subgroup Carrier) (hWs : W ≤ s)
    [IsElementaryAbelian 2 W] (hc : Nat.card W = 16) :
    normalizer (W : Set Carrier) ≤ p₂ := by
  apply le_trans _ RankOneFourNormalizer.normalizer_four_le_p₂
  intro g hg
  apply mem_normalizer_iff.mpr
  intro x
  rw [four_iff_mem_and_fixedPoint W hWs hc x,
    four_iff_mem_and_fixedPoint W hWs hc (g * x * g⁻¹)]
  simp only [map_mul, map_inv, Equiv.Perm.card_support_conj]
  exact and_congr (mem_normalizer_iff.mp hg x) Iff.rfl

/-- No elementary sixteen in the literal Hall–Janko carrier has a normalizer
whose order is divisible by five. -/
theorem five_not_dvd_card_normalizer (W : Subgroup Carrier)
    [IsElementaryAbelian 2 W] (hc : Nat.card W = 16) :
    ¬ 5 ∣ Nat.card (normalizer (W : Set Carrier)) := by
  obtain ⟨P, hWP⟩ := (IsElementaryAbelian.isPGroup 2 W).exists_le_sylow
  let S : Sylow 2 Carrier := SecondParabolic.sylow FirstParabolic.card_l₁
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Carrier P S
  let e : Carrier ≃* Carrier := MulAut.conj g
  let W' := W.map e.toMonoidHom
  have hP : (P : Subgroup Carrier).map e.toMonoidHom = s :=
    congrArg (fun Q : Sylow 2 Carrier => (Q : Subgroup Carrier)) hg
  have hW's : W' ≤ s := hP ▸ map_mono hWP
  let : IsElementaryAbelian 2 W' := IsElementaryAbelian.map e.toMonoidHom
  have hc' : Nat.card W' = 16 := (card_map_of_injective e.injective).trans hc
  have hd := card_dvd_of_le (normalizer_le_p₂ W' hW's hc')
  rw [card_p₂] at hd
  have hn : Nat.card (normalizer (W' : Set Carrier)) =
      Nat.card (normalizer (W : Set Carrier)) := by
    rw [← map_equiv_normalizer_eq W e, card_map_of_injective e.injective]
  rw [hn] at hd
  intro h
  exact (by decide : ¬ 5 ∣ 1152) (h.trans hd)

end Sporadic.LeechRelated.J2.ElementarySixteenFusion
