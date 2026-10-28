module
public import Theory.GroupTheory.CenterFreeCubicFixedIndex
public import Stellmacher.MaxElementaryOffender
public import Stellmacher.ElementaryAbelianMaxJFixedCenter

/-!
# The Baumann subgroup in a cubic group with a large center module

Let H/O₂(H)=S₃, Z(H)=1, and let V be a normal elementary two-subgroup
centralizing O₂(H). If |V|>4, every maximum elementary subgroup of a Sylow
lies in O₂(H): otherwise its offender inequality gives fixed index at most
two, and the two-Sylow fixed-index bound forces |V|≤4. Thus J(S)≤O₂(H).
Now V centralizes J(S), hence lies in Ω₁Z(J(S)). If the Baumann subgroup
crossed O₂(H), it and O₂(H) would generate S and centralize V; the same
fixed-index bound would make V trivial. Therefore B(S)≤O₂(H).

This uses only the stated single-vertex hypotheses. It supplies the large
initial-module branch of the Baumann selection in the cubic specialization
of Stellmacher (9.3), Journal of Algebra 190 (1997), p.49; the generic
maximal-elementary offender inequality is from (2.2), p.20.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace SymmetricThreeTwoCore
variable {H : Type*} [Group H] [Finite H]

private theorem core_sup_actor_eq_sylow
    (e : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) (S : Sylow 2 H)
    (U : Subgroup H) (hUS : U ≤ (S : Subgroup H)) (hUnot : ¬ U ≤ pCore 2 H) :
    pCore 2 H ⊔ U = (S : Subgroup H) := by
  have hQS : pCore 2 H ≤ (S : Subgroup H) := pCore_isPGroup.le_sylow_of_normal S
  have hQi : (pCore 2 H).relIndex (S : Subgroup H) = 2 := by
    have hh := relIndex_mul_index hQS
    rw [core_index e, sylow_index_three e S] at hh
    omega
  have hle : pCore 2 H ⊔ U ≤ (S : Subgroup H) := sup_le hQS hUS
  have hh := relIndex_mul_relIndex (pCore 2 H) (pCore 2 H ⊔ U)
    (S : Subgroup H) le_sup_left hle
  rw [hQi] at hh
  rcases Nat.prime_mul_iff.mp (hh ▸ Nat.prime_two) with ⟨_, h1⟩ | ⟨_,h1⟩
  · exact le_antisymm hle (relIndex_eq_one.mp h1)
  · exact (hUnot (le_sup_right.trans (relIndex_eq_one.mp h1))).elim

private theorem fixed_eq_of_crossing_core
    (e : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) (S : Sylow 2 H)
    (V U : Subgroup H) (hVQ : V ≤ centralizer (pCore 2 H : Set H))
    (hUS : U ≤ (S : Subgroup H)) (hUnot : ¬ U ≤ pCore 2 H) :
    V ⊓ centralizer (S : Set H) = V ⊓ centralizer (U : Set H) := by
  apply le_antisymm (inf_le_inf_left _ (centralizer_le hUS))
  intro x hx
  refine ⟨hx.1, ?_⟩
  have hs : pCore 2 H ⊔ U ≤ centralizer ({x} : Set H) := by
    apply sup_le
    · intro q hq
      exact mem_centralizer_singleton_iff.mpr (hVQ hx.1 q hq)
    · intro y hy
      exact mem_centralizer_singleton_iff.mpr (hx.2 y hy)
  rw [core_sup_actor_eq_sylow e S U hUS hUnot] at hs
  intro y hy
  exact mem_centralizer_singleton_iff.mp (hs hy)

/-- A large normal elementary subgroup forces the elementary Thompson subgroup into O₂. -/
theorem maxJ_le_core_of_large_elementary
    (e : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) (S : Sylow 2 H)
    (V : Subgroup H) [V.Normal] [IsElementaryAbelian 2 V]
    (hVS : V ≤ (S : Subgroup H)) (hcenter : center H = ⊥)
    (hVQ : V ≤ centralizer (pCore 2 H : Set H)) (hlarge : 4 < Nat.card V) :
    elementaryAbelianMaxJ (S : Subgroup H) ≤ pCore 2 H := by
  apply sSup_le
  intro A hA
  by_contra hnot
  let C := centralizer (V : Set H)
  let q := QuotientGroup.mk' C
  have hCQ : pCore 2 H ≤ C := le_centralizer_iff.mp hVQ
  have hQS : pCore 2 H ≤ (S : Subgroup H) := pCore_isPGroup.le_sylow_of_normal S
  have hQi : (pCore 2 H).relIndex (S : Subgroup H) = 2 := by
    have hh := relIndex_mul_index hQS
    rw [core_index e, sylow_index_three e S] at hh
    omega
  have himage : Nat.card (A.map q) ≤ 2 := by
    have hcdiv : C.relIndex (S : Subgroup H) ∣ 2 :=
      by
        have hh := relIndex_dvd_of_le_left (S : Subgroup H) hCQ
        rwa [hQi] at hh
    have hcimage : Nat.card ((S : Subgroup H).map q) ≤ 2 := by
      have hh := relIndex_ker (S : Subgroup H) q
      rw [QuotientGroup.ker_mk'] at hh
      rw [← hh]
      exact Nat.le_of_dvd (by decide) hcdiv
    exact (card_le_of_le (map_mono hA.1)).trans hcimage
  have hbound := maxElementary_card_le_fixed_mul_image (S : Subgroup H) V A hVS hA q
    (QuotientGroup.ker_mk' C)
  have hle : (V ⊓ centralizer (A : Set H)).relIndex V ≤ 2 := by
    have hcount := ((V ⊓ centralizer (A : Set H)).subgroupOf V).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe
      (show V ⊓ centralizer (A : Set H) ≤ V from inf_le_left)).toEquiv] at hcount
    have hp := Nat.card_pos (α := (V ⊓ centralizer (A : Set H) : Subgroup H))
    change (V ⊓ centralizer (A : Set H)).relIndex V *
      Nat.card (V ⊓ centralizer (A : Set H) : Subgroup H) = Nat.card V at hcount
    nlinarith
  have hh := normal_card_le_fixed_index_sq e S V hcenter
  rw [fixed_eq_of_crossing_core e S V A hVQ hA.1 hnot] at hh
  have : Nat.card V ≤ 4 := hh.trans (by nlinarith [sq_nonneg ((V ⊓ centralizer (A : Set H)).relIndex V : ℤ)])
  omega

/-- A large normal elementary subgroup also forces the Baumann subgroup into O₂. -/
theorem baumann_le_core_of_large_elementary
    (e : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) (S : Sylow 2 H)
    (V : Subgroup H) [V.Normal] [IsElementaryAbelian 2 V]
    (hVS : V ≤ (S : Subgroup H)) (hcenter : center H = ⊥)
    (hVQ : V ≤ centralizer (pCore 2 H : Set H)) (hlarge : 4 < Nat.card V) :
    (S : Subgroup H) ⊓ centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup H)) : Set H) ≤ pCore 2 H := by
  let B := (S : Subgroup H) ⊓ centralizer
    (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup H)) : Set H)
  have hJ := maxJ_le_core_of_large_elementary e S V hVS hcenter hVQ hlarge
  have hVZ : V ≤ omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup H)) :=
    elementary_centralizer_maxJ_le_omegaCenter (S : Subgroup H) V hVS
      (hVQ.trans (centralizer_le hJ))
  have hBC : B ≤ centralizer (V : Set H) := inf_le_right.trans (centralizer_le hVZ)
  by_contra hnot
  have hf : V ⊓ centralizer (S : Set H) = V := by
    rw [fixed_eq_of_crossing_core e S V B hVQ inf_le_left hnot]
    exact inf_eq_left.mpr (le_centralizer_iff.mp hBC)
  have hh := normal_card_le_fixed_index_sq e S V hcenter
  rw [hf,relIndex_self] at hh
  norm_num at hh
  omega

end SymmetricThreeTwoCore
