module
public import CFSG.Quasithin.Chapter10.SourceA5HallGeneration
/-!
# Nontriviality of the actual H-star odd Hall subgroup

When the generation minimum exceeds one, the actual intrinsic Cartan data
contain a cyclic subgroup of order at least three. All odd Hall subgroups
of the literal maximal overlap have the same order. Thus none is trivial.
This supplies a cubic element after the original Hall placement in an
exponent-three torus; no chosen Cartan compatibility is required.

Source: Aschbacher–Smith E.2.2 and 10.2.3, pp.215 and745–746.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L H : Subgroup G}

theorem source_hstar_hall_ne_bot_of_generation_large
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (B : Subgroup H) (hBM : B ≤ D.maximalLocal.subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H))) :
    B ≠ ⊥ := by
  obtain ⟨n,_,hgn,d,hm,_⟩ := source_a5_hstar_cartan_data D e hn hH hlarge
  have hcard := d.hall.card_eq (hm.symm ▸ hHall)
  rw [Nat.card_congr (subgroupOfEquivOfLe d.hall_le).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (hm.symm ▸ hBM)).toEquiv] at hcard
  intro he
  have hcyc : Nat.card d.witness.cyclicGroup ≤ 1 := by
    calc
      Nat.card d.witness.cyclicGroup ≤ Nat.card d.witness.abelianGroup := Nat.card_le_card_of_injective (inclusion d.witness.cyclic_le)
        (inclusion_injective d.witness.cyclic_le)
      _ = 1 := by rw [hcard,he,card_bot]
  have hpow : 4 ≤ 2^n := by
    have hn2 : 2 ≤ n := by omega
    exact pow_le_pow_right₀ (by decide : 1 ≤ (2:ℕ)) hn2
  rw [d.witness.card] at hcyc
  omega
end CFSG.Quasithin.Chapter10
