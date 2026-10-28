module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingImage

/-!
# The even exchange in a two-subgroup containing the marked pair swaps

A two-subgroup of S₅ containing the two disjoint transpositions preserves
their unordered pair. Its even permutations lie in the explicit four-group
of double transpositions. Thus every order-four even subgroup inside it
contains the actual pair exchange. This supplies the simultaneous marking
of the block Sylow image in the C.5.6 transvection argument.

Source: Aschbacher–Smith, B.3.2 and C.5.6, printed pp.83–84 and157.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
open ChapterB.Offenders

private def evenWord : Fin 4 → FivePerm := ![1, pairDiagonal, pairExchange, pairDiagonal * pairExchange]

private def evenPairGroup : Subgroup FivePerm where
  carrier := Set.range evenWord
  one_mem' := ⟨0, rfl⟩
  mul_mem' := by
    have h : ∀ i j, ∃ k, evenWord i * evenWord j = evenWord k := by decide +kernel
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := h i j
    exact ⟨k, hk.symm⟩
  inv_mem' := by
    have h : ∀ i, ∃ j, (evenWord i)⁻¹ = evenWord j := by decide +kernel
    rintro _ ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := h i
    exact ⟨j, hj.symm⟩

private theorem card_evenPairGroup : Nat.card evenPairGroup = 4 := by
  have hi : Function.Injective evenWord := by decide +kernel
  change Nat.card (Set.range evenWord) = 4
  rw [← Nat.card_congr (Equiv.ofInjective _ hi)]
  exact Nat.card_fin _

private theorem swap_in_D {p : FivePerm} (hp : p.IsSwap) (hD : p ∈ D 5) :
    p = pairSwap 5 0 ∨ p = pairSwap 5 1 := by
  let := Odd.elementary_disjointTranspositions (n := 5) (m := 2) (Or.inl rfl) (by decide)
  have hc : D 5 ≤ centralizer (D 5 : Set FivePerm) := le_centralizer_iff_isMulCommutative.mpr inferInstance
  have h0 := (hc hD) (pairSwap 5 0) (pairSwap_mem (n := 5) (m := 2) 0 (by decide))
  have h1 := (hc hD) (pairSwap 5 1) (pairSwap_mem (n := 5) (m := 2) 1 (by decide))
  obtain ⟨a, b, hab, rfl⟩ := hp
  have ht : ∀ a b : Fin 5, a ≠ b →
      pairSwap 5 0 * Equiv.swap a b = Equiv.swap a b * pairSwap 5 0 →
      pairSwap 5 1 * Equiv.swap a b = Equiv.swap a b * pairSwap 5 1 →
      Equiv.swap a b = pairSwap 5 0 ∨ Equiv.swap a b = pairSwap 5 1 := by decide +kernel
  exact ht a b hab h0 h1

private theorem even_mem_word (P : Subgroup FivePerm) (hP : IsPGroup 2 P)
    (hD : D 5 ≤ P) (g : FivePerm) (hg : g ∈ P)
    (hgeven : g ∈ alternatingGroup (Fin 5)) : g ∈ evenPairGroup := by
  have hs (i : Fin 2) : (MulAut.conj g (pairSwap 5 i)).IsSwap := by
    fin_cases i
    · exact ⟨g 0, g 1, g.injective.ne (by decide), Equiv.symm_trans_swap_trans 0 1 g⟩
    · exact ⟨g 2, g 3, g.injective.ne (by decide), Equiv.symm_trans_swap_trans 2 3 g⟩
  have hi (i : Fin 2) := swap_in_D (hs i)
    (Odd.isSwap_mem_D_of_isPGroup (Or.inl rfl) hP hD (hs i)
      (P.mul_mem (P.mul_mem hg (hD (pairSwap_mem (n := 5) (m := 2) i i.isLt))) (P.inv_mem hg)))
  have ht : ∀ g : FivePerm, Equiv.Perm.sign g = 1 →
      (∀ i : Fin 2, MulAut.conj g (pairSwap 5 i) = pairSwap 5 0 ∨
        MulAut.conj g (pairSwap 5 i) = pairSwap 5 1) →
      ∃ j, evenWord j = g := by decide +kernel
  exact ht g (Equiv.Perm.mem_alternatingGroup.mp hgeven) hi

/-- The actual inner order-four image contains the even pair exchange. -/
theorem pairExchange_mem_of_even_four
    (P A : Subgroup FivePerm) (hP : IsPGroup 2 P) (hD : D 5 ≤ P)
    (hAP : A ≤ P) (hAeven : A ≤ alternatingGroup (Fin 5)) (hAcard : Nat.card A = 4) :
    pairExchange ∈ A := by
  have hAW : A ≤ evenPairGroup := fun g hg => even_mem_word P hP hD g (hAP hg) (hAeven hg)
  have heq : A = evenPairGroup := eq_of_le_of_card_ge hAW (by rw [hAcard, card_evenPairGroup])
  rw [heq]
  exact ⟨2, rfl⟩

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource

namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The actual block Sylow image in the marked alternating-five quotient
has order four. -/
theorem card_blockSylow_image (N K : Subgroup G) (hKN : K ≤ N)
    (a : N →* FivePerm) (hA : (K.subgroupOf N).map a = alternatingGroup (Fin 5))
    (P : Sylow 2 K) :
    Nat.card (((P : Subgroup K).map K.subtype).subgroupOf N |>.map a) = 4 := by
  let b : K →* alternatingGroup (Fin 5) :=
    (a.comp (inclusion hKN)).codRestrict (alternatingGroup (Fin 5)) (fun k =>
      hA ▸ mem_map_of_mem a k.property)
  have hb : Function.Surjective b := by
    intro p
    have hp : (p : FivePerm) ∈ (K.subgroupOf N).map a := hA.symm ▸ p.property
    obtain ⟨k, hk, hkp⟩ := hp
    exact ⟨⟨k, hk⟩, Subtype.ext hkp⟩
  let Q := P.mapSurjective hb
  have hc : Nat.card Q = 4 := by
    rw [Q.card_eq_multiplicity, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
    decide +kernel
  have he : (((P : Subgroup K).map K.subtype).subgroupOf N).map a =
      (Q : Subgroup (alternatingGroup (Fin 5))).map (alternatingGroup (Fin 5)).subtype := by
    rw [Sylow.coe_mapSurjective, map_map]
    ext p
    constructor
    · rintro ⟨k, ⟨l, hl, hlk⟩, rfl⟩
      refine ⟨l, hl, ?_⟩
      change a (inclusion hKN l) = a k
      exact congrArg a (Subtype.ext hlk)
    · rintro ⟨k, hk, rfl⟩
      exact ⟨inclusion hKN k, ⟨k, hk, rfl⟩, rfl⟩
  rw [he, card_map_of_injective (alternatingGroup (Fin 5)).subtype_injective]
  exact hc

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource

namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The block's actual Sylow subgroup supplies the even exchange in any
marked action containing the full pair-swap Baumann image. -/
theorem pairExchange_mem_blockSylow_image
    (R S K N : Subgroup G) (hR : IsPGroup 2 R) (hSR : S ≤ R) (hKN : K ≤ N)
    (a : N →* FivePerm) (hK : (K.subgroupOf N).map a = alternatingGroup (Fin 5))
    (hS : (S.subgroupOf N).map a = ChapterB.Offenders.D 5)
    (P : Sylow 2 K) (hP : (P : Subgroup K).map K.subtype = R ⊓ K) :
    pairExchange ∈ ((R ⊓ K).subgroupOf N).map a := by
  apply pairExchange_mem_of_even_four ((R.subgroupOf N).map a)
    (((R ⊓ K).subgroupOf N).map a) (hR.comap_subtype.map a)
  · rw [← hS]
    exact map_mono (subgroupOf_mono N hSR)
  · exact map_mono (subgroupOf_mono N inf_le_left)
  · rw [← hK]
    exact map_mono (subgroupOf_mono N inf_le_right)
  · rw [← hP]
    exact card_blockSylow_image N K hKN a hK P

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
