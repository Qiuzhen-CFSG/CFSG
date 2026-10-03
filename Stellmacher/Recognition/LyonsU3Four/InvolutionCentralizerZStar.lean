module

public import Stellmacher.Recognition.LyonsU3Four.InvolutionCentralizerQuotients
public import Glauberman.ZStar
public import Theory.GroupTheory.CentralTwoQuotientOddCore

/-!
# Z-star centrality in an involution centralizer

For a nonidentity z in Z(S), put C = C_G(z) and N = ⟨z⟩ ≤ Z(C).
The image of Z(S) in C/N has order two. A conjugate of its nonidentity
member lying in S/N lifts to a conjugate involution lying in S: the
kernel N lies in S. Every such involution lies in Z(S), so this image
is weakly closed. Glauberman's Z-star theorem makes it central modulo
the odd core of C/N. Centrality then lifts modulo the odd core of C,
since Z(S) already centralizes the Sylow subgroup S of C.

No automizer, solvability, or trivial-local-odd-core assumption is used.
Source: Lyons, A Characterization of the Group U₃(4), Trans. AMS 164
(1972), Lemma 1, pp.372–373, the paragraph beginning “Suppose |K| = 3”
and its later reuse in part (d).
-/

namespace Stellmacher.Recognition.LyonsU3Four
open Subgroup

/-- The Sylow center has central image modulo the odd core of C_G(z). -/
public theorem centralizerCenterModOddCore_le_center
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S) {z : G}
    (hz : z ∈ centerImage S) (hz1 : z ≠ 1) :
    centralizerCenterModOddCore S z ≤
      Subgroup.center (Subgroup.centralizer ({z} : Set G) ⧸
        pPrimeCore 2 (Subgroup.centralizer ({z} : Set G))) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let := centerImage_elementary S h
  let C := centralizer ({z} : Set G)
  let P : Sylow 2 C := centralizerSylow S hz
  let T : Subgroup C := (centerImage S).subgroupOf C
  let zC : C := ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩
  have hzC : zC ∈ center C := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_singleton_iff.mp g.property)
  let N : Subgroup C := zpowers zC
  have hN : N ≤ center C := zpowers_le.mpr hzC
  let hn : N.Normal := ⟨fun x hx g => by
    simpa [mem_center_iff.mp (hN hx) g] using hx⟩
  have hNcard : Nat.card N = 2 := by
    rw [Nat.card_zpowers]
    apply orderOf_eq_prime
    · exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) z hz)
    · intro he
      exact hz1 (congrArg Subtype.val he)
  have hNp : IsPGroup 2 N := IsPGroup.of_card (n := 1) (by simpa using hNcard)
  have hNT : N ≤ T := zpowers_le.mpr hz
  have hTP : T ≤ (P : Subgroup C) := fun x hx => centerImage_le S hx
  have hTC : T ≤ centralizer (P : Set C) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro s hs
    apply Subtype.ext
    exact ((mem_centralizer_iff.mp (sylow_le_centralizer_centerImage S hs)) x hx).symm
  have hTcard : Nat.card T = 4 := by
    have hle : centerImage S ≤ C := (centerImage_le S).trans (sylow_le_involutionCentralizer S hz)
    exact (Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv).trans (centerImage_card S h)
  let q : C →* C ⧸ N := QuotientGroup.mk' N
  let Pbar := P.mapSurjective (f := q) (QuotientGroup.mk'_surjective N)
  let U := T.map q
  have hUcard : Nat.card U = 2 := by
    have hc := card_eq_card_quotient_mul_card_subgroup (N.subgroupOf T)
    have hNc : Nat.card (N.subgroupOf T) = 2 :=
      (Nat.card_congr (subgroupOfEquivOfLe hNT).toEquiv).trans hNcard
    rw [hTcard, hNc, ← natCard_map_mk'_eq T N] at hc
    change 4 = Nat.card U * 2 at hc
    omega
  have hbar : ∀ x : C, (x : G) ∈ centerImage S →
      QuotientGroup.mk' (pPrimeCore 2 (C ⧸ N)) (q x) ∈
        center ((C ⧸ N) ⧸ pPrimeCore 2 (C ⧸ N)) := by
    intro x hx
    have hxT : x ∈ T := hx
    have hx2 : x ^ 2 = 1 :=
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : G) hx)
    by_cases hxq : q x = 1
    · change QuotientGroup.mk' (pPrimeCore 2 (C ⧸ N)) (q x) ∈ _
      simp [hxq]
    have hxU : q x ∈ U := mem_map_of_mem q hxT
    have hxP : q x ∈ (Pbar : Subgroup (C ⧸ N)) := mem_map_of_mem q (hTP hxT)
    apply Glauberman.ZStar.glauberman_zstar_local Pbar (q x)
      ⟨hxq, by simpa using congrArg q hx2⟩ hxP
    · intro s hs
      change s ∈ (P : Subgroup C).map q at hs
      obtain ⟨s, hs, rfl⟩ := hs
      simpa only [← map_mul] using congrArg q (mem_centralizer_iff.mp (hTC hxT) s hs)
    · refine ⟨hxP, ?_⟩
      intro g hg
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N g
      change q g * q x * (q g)⁻¹ ∈ (P : Subgroup C).map q at hg
      have hgP : g * x * g⁻¹ ∈ (P : Subgroup C) := by
        have hm : g * x * g⁻¹ ∈ ((P : Subgroup C).map q).comap q := by
          simpa only [mem_comap, map_mul, map_inv] using hg
        rw [comap_map_eq, show q.ker = N from QuotientGroup.ker_mk' N,
          sup_eq_left.mpr (hNT.trans hTP)] at hm
        exact hm
      have hg2 : (g * x * g⁻¹) ^ 2 = 1 := by
        simpa only [map_pow, map_one, MulAut.conj_apply] using congrArg (MulAut.conj g) hx2
      have hgT : g * x * g⁻¹ ∈ T :=
        involution_mem_centerImage S h hgP (congrArg C.subtype hg2)
      have hgU : q g * q x * (q g)⁻¹ ∈ U := by
        simpa only [map_mul, map_inv] using mem_map_of_mem q hgT
      have hgne : q g * q x * (q g)⁻¹ ≠ 1 := by
        intro he
        apply hxq
        have he' := congrArg (MulAut.conj (q g)⁻¹) he
        simpa only [map_one, MulAut.conj_apply, inv_inv, inv_mul_cancel_left,
          mul_assoc, inv_mul_cancel, mul_one] using he'
      exact congrArg Subtype.val (((Nat.card_eq_two_iff' (1 : U)).mp hUcard).unique
        (show (⟨q g * q x * (q g)⁻¹, hgU⟩ : U) ≠ 1 from fun he => hgne (congrArg Subtype.val he))
        (show (⟨q x, hxU⟩ : U) ≠ 1 from fun he => hxq (congrArg Subtype.val he)))
  change T.map (QuotientGroup.mk' (pPrimeCore 2 C)) ≤ center (C ⧸ pPrimeCore 2 C)
  rintro a ⟨x, hx, rfl⟩
  exact mem_center_mod_oddCore_of_central_two_quotient N hN hNp P
    (hTC hx) (hbar x hx)

end Stellmacher.Recognition.LyonsU3Four
