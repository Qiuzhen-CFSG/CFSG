module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.BlockSylow
public import CFSG.Quasithin.ChapterB.Section03.Offenders.SourceSylow

/-!
# Excluding a single transposition in the two-block A₅ case

The degree-five permutation calculation uses the exact pair-swap four-group
and its even exchange. A nontrivial subgroup of that four-group normalized
by the exchange fixes the same two-dimensional plane as the full four-group.
The source application supplies the exchange from R∩K₁ and obtains its
normalization of U₁ˣ from the transvection subgroup proved previously.

Source: Aschbacher–Smith, proof of C.5.6, printed p.157.
-/

@[expose] public section
open Subgroup BinaryPermutation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource

abbrev FivePerm := Equiv.Perm (Fin 5)
def pairExchange : FivePerm := ChapterB.Offenders.kleinSecond 5 (by decide)
def pairDiagonal : FivePerm := ChapterB.Offenders.pairSwap 5 0 * ChapterB.Offenders.pairSwap 5 1

private def pairWord : Fin 4 → FivePerm :=
  ![1, ChapterB.Offenders.pairSwap 5 0, ChapterB.Offenders.pairSwap 5 1, pairDiagonal]

private theorem actor_mem_word (g : FivePerm) : g ∈ ChapterB.Offenders.D 5 ↔ ∃ i, pairWord i = g := by
  let W : Subgroup FivePerm := {
    carrier := Set.range pairWord
    one_mem' := ⟨0, rfl⟩
    mul_mem' := by
      have hc : ∀ i j, ∃ k, pairWord i * pairWord j = pairWord k := by decide +kernel
      rintro a b ⟨i, rfl⟩ ⟨j, rfl⟩
      obtain ⟨k, hk⟩ := hc i j
      exact ⟨k, hk.symm⟩
    inv_mem' := by
      have hc : ∀ i, ∃ j, (pairWord i)⁻¹ = pairWord j := by decide +kernel
      rintro a ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := hc i
      exact ⟨j, hj.symm⟩ }
  have hEq : ChapterB.Offenders.D 5 = W := by
    apply le_antisymm
    · apply (closure_le _).mpr
      rintro g ⟨i, _, rfl⟩
      fin_cases i
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    · rintro _ ⟨i, rfl⟩
      have h0 := ChapterB.Offenders.pairSwap_mem (n := 5) (m := 2) 0 (by decide)
      have h1 := ChapterB.Offenders.pairSwap_mem (n := 5) (m := 2) 1 (by decide)
      fin_cases i
      · exact one_mem _
      · exact h0
      · exact h1
      · exact mul_mem h0 h1
  change g ∈ ChapterB.Offenders.D 5 ↔ g ∈ W
  rw [hEq]

/-- Every nontrivial exchange-invariant subgroup contains the diagonal. -/
theorem diagonal_mem_of_exchange_normalized (B : Subgroup FivePerm)
    (hB : B ≤ ChapterB.Offenders.D 5) (hne : B ≠ ⊥)
    (hn : pairExchange ∈ normalizer (B : Set FivePerm)) : pairDiagonal ∈ B := by
  obtain ⟨g, hg, hgne⟩ := (B.bot_or_exists_ne_one).resolve_left hne
  obtain ⟨i, rfl⟩ := (actor_mem_word g).mp (hB hg)
  have hh := (mem_normalizer_iff.mp hn _).mp hg
  fin_cases i
  · exact (hgne rfl).elim
  · have hconj : MulAut.conj pairExchange (pairWord 1) = pairWord 2 := by decide +kernel
    change MulAut.conj pairExchange (pairWord 1) ∈ B at hh
    rw [hconj] at hh
    exact B.mul_mem hg hh
  · have hconj : MulAut.conj pairExchange (pairWord 2) = pairWord 1 := by decide +kernel
    change MulAut.conj pairExchange (pairWord 2) ∈ B at hh
    rw [hconj] at hh
    exact B.mul_mem hh hg
  · exact hg

/-- The diagonal has exactly the same fixed plane as the whole pair-swap actor. -/
theorem fixedSpace_eq_of_exchange_normalized (B : Subgroup FivePerm)
    (hB : B ≤ ChapterB.Offenders.D 5) (hne : B ≠ ⊥)
    (hn : pairExchange ∈ normalizer (B : Set FivePerm)) :
    fixedSpace (coreRepresentation (Fin 5)) B =
      fixedSpace (coreRepresentation (Fin 5)) (ChapterB.Offenders.D 5) := by
  ext v
  rw [mem_fixedSpace_iff, mem_fixedSpace_iff]
  constructor
  · intro hv g hg
    have hd := hv pairDiagonal (diagonal_mem_of_exchange_normalized B hB hne hn)
    obtain ⟨i, rfl⟩ := (actor_mem_word g).mp hg
    have hd' : (fun i => v.val (pairDiagonal.symm i)) = v.val := congrArg Subtype.val hd
    have h0 : v.val 0 = v.val 1 := (congrFun hd' 0).symm
    have h1 : v.val 2 = v.val 3 := (congrFun hd' 2).symm
    apply Subtype.ext
    change (fun j => v.val ((pairWord i).symm j)) = v.val
    fin_cases i
    · rfl
    · exact (swap_fixed_iff (0 : Fin 5) 1 v.val).mpr h0
    · exact (swap_fixed_iff (2 : Fin 5) 3 v.val).mpr h1
    · exact hd'

  · intro hv g hg
    exact hv g (hB hg)

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource

namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
open Subgroup BinaryPermutation Representation.BinaryOffender
variable {G : Type*} [Group G]

/-- An action image is normalized by the image of each actual normalizing actor. -/
private theorem image_normalized {N V : Subgroup G} (a : N →* FivePerm)
    (r : N) (hr : (r : G) ∈ normalizer (V : Set G)) :
    a r ∈ normalizer ((V.subgroupOf N).map a : Set FivePerm) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hfix : (V.subgroupOf N).map (MulAut.conj r).toMonoidHom = V.subgroupOf N := by
    apply mem_normalizer_iff_map_conj_eq.mp
    rw [mem_normalizer_iff]
    intro v
    exact mem_normalizer_iff.mp hr v
  calc
    ((V.subgroupOf N).map a).map (MulAut.conj (a r)).toMonoidHom =
        ((V.subgroupOf N).map (MulAut.conj r).toMonoidHom).map a := by
      rw [map_map, map_map]
      congr 1
      ext v
      simp [MulAut.conj_apply]
    _ = _ := by rw [hfix]

/-- The source R⁺ argument supplies the exchange normalization needed for
both fixed-plane conclusions. Here the two appearances of the exchange
use its actual lift in R ∩ K and the original action homomorphism. -/
theorem fixedSpace_conjugate_image
    {R K V N : Subgroup G}
    (hV : transvectionRadical R ≤ normalizer (V : Set G))
    (hKR : R ⊓ K ≤ transvectionRadical R)
    (a : N →* FivePerm)
    (hB : (V.subgroupOf N).map a ≤ ChapterB.Offenders.D 5)
    (hne : (V.subgroupOf N).map a ≠ ⊥)
    (hex : pairExchange ∈ ((R ⊓ K).subgroupOf N).map a) :
    fixedSpace (coreRepresentation (Fin 5)) ((V.subgroupOf N).map a) =
      fixedSpace (coreRepresentation (Fin 5)) (ChapterB.Offenders.D 5) := by
  apply fixedSpace_eq_of_exchange_normalized _ hB hne
  obtain ⟨r, hr, hrp⟩ := hex
  rw [← hrp]
  exact image_normalized a r (hV (hKR hr))

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
