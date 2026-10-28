module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.Basic
public import BenderSuzuki.SE.Proposition84TorusModels
public import BenderSuzuki.SE.Lemma312

/-!
# Inverted Borel tori through odd central covers

The actual quotient model supplies a cyclic inverted torus of order `2ⁿ-1`.
The odd central-kernel lifting theorem gives a unique inverted lift over
each torus element. Taking the literal inverse image of the Borel identifies
these lifts with the inverted elements of the upstairs two-point subgroup.
This applies to special unitary covers as well as the simple groups.

The final application bounds every inverted subgroup in the upstairs Borel.
It makes no claim that arbitrary automorphisms are semilinear, or that every
odd central cover is simple.
Source: GLS, Volume 4, Chapter 4, Lemma 3.2(d), used in Chapter 2, 16.2–16.5.
-/

namespace BenderSuzuki.ZD.RankOneModelGeometry
open Subgroup PFAppendixIII PFchapter1section1
variable {G : Type*} [Group G]

private theorem inverted_mem_rightConjugate (B : Subgroup G) {x t : G}
    (hx : x ∈ B) (hi : rightConjugateElem x t = x⁻¹) : x ∈ rightConjugate B t := by
  refine ⟨x⁻¹, B.inv_mem hx, ?_⟩
  change t⁻¹ * x⁻¹ * (t⁻¹)⁻¹ = x
  calc
    t⁻¹ * x⁻¹ * (t⁻¹)⁻¹ = (rightConjugateElem x t)⁻¹ := by
      simp [rightConjugateElem, mul_assoc]
    _ = x := by rw [hi, inv_inv]

variable [Finite G]

/-- The literal inverted part of an upstairs Borel pair is cyclic of order
`2ⁿ-1`, even when the group is a nontrivial odd central cover. -/
public theorem oddCentralCover_inverted_torus (Z : Subgroup G) [Z.Normal]
    (hZ : Z ≤ center G) (hodd : Odd (Nat.card Z))
    {n : ℕ} (hn : 2 ≤ n) (hmodel : IsSimpleBenderGroupAtExponent n (G ⧸ Z))
    (B : Subgroup G) (hZB : Z ≤ B)
    (hB : IsBorelSubgroup (B.map (QuotientGroup.mk' Z)))
    (t : G) (ht : IsInvolution t) (htB : t ∉ B) :
    ∃ T : Subgroup G,
      (T : Set G) = {x | x ∈ twoPoint B t ∧ rightConjugateElem x t = x⁻¹} ∧
      IsCyclic T ∧ Nat.card T = 2 ^ n - 1 := by
  let q := QuotientGroup.mk' Z
  have htq : IsInvolution (q t) := IsInvolution.quotient_mk_of_odd_kernel Z hodd ht
  have htqB : q t ∉ B.map q := fun h =>
    htB ((quotient_mk_mem_map_iff_of_le Z B hZB t).mp h)
  obtain ⟨TQ, hTQ, hcQ, hcardQ⟩ :=
    simpleBenderAtExponent_borel_invertedTorus n hn hmodel hB (q t) htq htqB
  have hiQ : ∀ x ∈ TQ, rightConjugateElem x (q t) = x⁻¹ := by
    intro x hx
    exact ((Set.ext_iff.mp hTQ x).mp hx).2.2
  obtain ⟨T, hT, hc, hcard⟩ := invertedTorus_lift_of_central_odd_kernel Z hZ hodd t TQ hcQ hiQ
  refine ⟨T, ?_, hc, hcard.trans hcardQ⟩
  ext x
  rw [hT]
  change (q x ∈ TQ ∧ rightConjugateElem x t = x⁻¹) ↔
    (x ∈ twoPoint B t ∧ rightConjugateElem x t = x⁻¹)
  constructor
  · rintro ⟨hxQ, hi⟩
    have hxB : x ∈ B := (quotient_mk_mem_map_iff_of_le Z B hZB x).mp
      (((Set.ext_iff.mp hTQ (q x)).mp hxQ).1)
    exact ⟨⟨hxB, inverted_mem_rightConjugate B hxB hi⟩, hi⟩
  · rintro ⟨hx, hi⟩
    have hqi : rightConjugateElem (q x) (q t) = (q x)⁻¹ := by
      simpa [rightConjugateElem] using congrArg q hi
    have hqxB : q x ∈ B.map q := mem_map_of_mem q hx.1
    exact ⟨(Set.ext_iff.mp hTQ (q x)).mpr
      ⟨hqxB, inverted_mem_rightConjugate (B.map q) hqxB hqi, hqi⟩, hi⟩

/-- Application to the literal inverted subgroups in the Borel of a
central cover: each is cyclic, with order dividing the source torus order. -/
public theorem oddCentralCover_inverted_subgroup (Z : Subgroup G) [Z.Normal]
    (hZ : Z ≤ center G) (hodd : Odd (Nat.card Z))
    {n : ℕ} (hn : 2 ≤ n) (hmodel : IsSimpleBenderGroupAtExponent n (G ⧸ Z))
    (B : Subgroup G) (hZB : Z ≤ B)
    (hB : IsBorelSubgroup (B.map (QuotientGroup.mk' Z)))
    (t : G) (ht : IsInvolution t) (htB : t ∉ B)
    (R : Subgroup G) (hRB : R ≤ B)
    (hinv : ∀ x ∈ R, rightConjugateElem x t = x⁻¹) :
    IsCyclic R ∧ Nat.card R ∣ 2 ^ n - 1 := by
  obtain ⟨T, hT, hc, hcard⟩ := oddCentralCover_inverted_torus Z hZ hodd hn hmodel B hZB hB t ht htB
  have hRT : R ≤ T := by
    intro x hx
    exact (Set.ext_iff.mp hT x).mpr
      ⟨⟨hRB hx, inverted_mem_rightConjugate B (hRB hx) (hinv x hx)⟩, hinv x hx⟩
  let : IsCyclic T := hc
  exact ⟨isCyclic_of_le hRT, hcard ▸ card_dvd_of_le hRT⟩

end BenderSuzuki.ZD.RankOneModelGeometry
