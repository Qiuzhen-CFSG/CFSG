module
public import Theory.GroupTheory.ReducedNormal.ThreeLayers
public import Theory.GroupTheory.SylowSeedCentralizer
public import Theory.Representation.SylowFixedConjugation

/-!
# The Sylow central seed of a normal moved plane

Let U be a reduced normal elementary abelian two-subgroup containing
Ω₁Z(S), and let N be the normal span of a subgroup of the Sylow subgroup S.
If [U,N] has order four, its S-fixed subgroup has order at most two.
Otherwise the normality of its centralizer makes N fix [U,N], and the
reduced-module three-layer lemma forces N to fix U, a contradiction.

Sylow averaging splits every vector of Ω₁Z(S) into a moved vector and
an N-fixed vector. The resulting bound is |Ω₁Z(S)| ≤ 2|C_{Ω₁Z(S)}(N)|.
The solvable centralizer application uses the original N=⟨J(R₁)^H⟩.
Source: Aschbacher–Smith B.2.14 and13.4.9, printed pp.78 and906.
-/

public section
open Subgroup Stellmacher
open scoped IsMulCommutative commutatorElement
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- A normal span of Sylow elements cannot fix its nonzero moved layer in a reduced module. -/
theorem IsPReduced.moved_not_le_sylow_centralizer
    (U : Subgroup G) (hU : IsPReduced 2 U) (S : Sylow 2 G)
    (A : Subgroup G) (hAS : A ≤ S)
    (hne : (⁅U,conjugateSpanBy A ⊤⁆ : Subgroup G) ≠ ⊥) :
    ¬ (⁅U,conjugateSpanBy A ⊤⁆ : Subgroup G) ≤ centralizer (S : Set G) := by
  let := hU.normal
  let N := conjugateSpanBy A ⊤
  let W := ⁅U,N⁆
  let : N.Normal := normalizer_eq_top_iff.mp (top_unique (le_normalizer_conjugateSpanBy A ⊤))
  intro hc
  have hNC : N ≤ centralizer (W : Set G) := by
    apply conjugateSpanBy_le (hAS.trans (le_centralizer_iff.mp hc))
    exact le_normalizer_of_normal
  have hWC : ⁅W,N⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (le_centralizer_iff.mp hNC)
  have hNU := hU.centralizes_of_three_layers N W ⊥ le_rfl hWC.le (by simp)
  exact hne (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hNU))

/-- Sylow averaging splits the original central seed using the literal moved subgroup. -/
theorem omegaCenter_le_moved_sup_fixed
    (U N : Subgroup G) [U.Normal] [N.Normal] [IsElementaryAbelian 2 U]
    (S : Sylow 2 G) (hUS : U ≤ S)
    (hZU : omegaOneCenterAmbient (S : Subgroup G) ≤ U) :
    omegaOneCenterAmbient (S : Subgroup G) ≤
      (⁅U,N⁆ : Subgroup G) ⊔
        (omegaOneCenterAmbient (S : Subgroup G) ⊓ centralizer (N : Set G)) := by
  let W := ⁅U,N⁆
  let Z := omegaOneCenterAmbient (S : Subgroup G)
  let E := N ⊔ (S : Subgroup G)
  have hWE : W ≤ U := commutator_le_left _ _
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_injective (inclusion hWE) (inclusion_injective _)
  have hEZ : ⁅E,Z⁆ ≤ W := by
    apply commutator_sup_le_of_relative_normal (⊤ : Subgroup G) N (S : Subgroup G) Z W
      le_normalizer_of_normal le_top le_top
    · rw [commutator_comm N Z]
      exact commutator_mono hZU le_rfl
    · apply (commutator_eq_bot_iff_le_centralizer.mpr ?_).le.trans bot_le
      exact le_centralizer_iff.mp (fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2)
  intro z hz
  obtain ⟨w,hw,hc⟩ := fixed_coset_of_sylow E W le_normalizer_of_normal
    (fun _ hw => elemPow_eq_one_of_isElementaryAbelian _ hw)
    (S.subtype (show (S : Subgroup G) ≤ E from le_sup_right)) z
    (fun _ he => hEZ (commutator_mem_commutator he hz))
    (fun a ha => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 a.val ha)
  have hwz : w*z ∈ U := U.mul_mem (hWE hw) (hZU hz)
  have hwZ : w*z ∈ Z := (mem_omegaOneCenterAmbient_iff _ _).mpr
    ⟨hUS hwz,elemPow_eq_one_of_isElementaryAbelian _ hwz,
      fun s hs => hc s (mem_sup_right hs)⟩
  have hm := mul_mem_sup (W.inv_mem hw)
    (show w*z ∈ Z ⊓ centralizer (N : Set G) from
      ⟨hwZ,centralizer_le (show N ≤ E from le_sup_left) hc⟩)
  simpa only [inv_mul_cancel_left] using hm

/-- A normal moved plane has at most one Sylow-fixed binary dimension. -/
theorem IsPReduced.moved_plane_sylow_fixed_card_le_two
    (U : Subgroup G) (hU : IsPReduced 2 U) (S : Sylow 2 G)
    (A : Subgroup G) (hAS : A ≤ S)
    (hcard : Nat.card (⁅U,conjugateSpanBy A ⊤⁆ : Subgroup G) = 4) :
    Nat.card ((⁅U,conjugateSpanBy A ⊤⁆ : Subgroup G) ⊓
      centralizer (S : Set G) : Subgroup G) ≤ 2 := by
  let W := ⁅U,conjugateSpanBy A ⊤⁆
  let C := W ⊓ centralizer (S : Set G)
  change Nat.card W = 4 at hcard
  change Nat.card C ≤ 2
  have hne : W ≠ ⊥ := by intro he; rw [he,card_bot] at hcard; omega
  have hlt : C < W := lt_of_le_of_ne inf_le_left (by
    intro he
    exact hU.moved_not_le_sylow_centralizer U S A hAS hne
      (he ▸ inf_le_right : W ≤ centralizer (S : Set G)))
  have hsmall : Nat.card C < 4 := by
    rw [← hcard]
    exact lt_of_le_of_ne (card_le_of_le hlt.le) (fun he => hlt.ne (eq_of_le_of_card_ge hlt.le he.ge))
  have hd : Nat.card C ∣ 4 := hcard ▸ card_dvd_of_le (show C ≤ W from inf_le_left)
  have hp : 0 < Nat.card C := Nat.card_pos
  have h0 : Nat.card C = 1 ∨ Nat.card C = 2 ∨ Nat.card C = 3 := by omega
  rcases h0 with he | he | he
  · omega
  · omega
  · norm_num [he] at hd

/-- The full Sylow omega-center is bounded by the fixed seed and one moved binary dimension. -/
theorem IsPReduced.omegaCenter_card_le_twice_fixed_of_moved_plane
    (U : Subgroup G) (hU : IsPReduced 2 U) (S : Sylow 2 G)
    (hUS : U ≤ S) (hZU : omegaOneCenterAmbient (S : Subgroup G) ≤ U)
    (A : Subgroup G) (hAS : A ≤ S)
    (hcard : Nat.card (⁅U,conjugateSpanBy A ⊤⁆ : Subgroup G) = 4) :
    Nat.card (omegaOneCenterAmbient (S : Subgroup G)) ≤
      2 * Nat.card (omegaOneCenterAmbient (S : Subgroup G) ⊓
        centralizer (conjugateSpanBy A ⊤ : Set G) : Subgroup G) := by
  let := hU.normal
  let := hU.elementary
  let N := conjugateSpanBy A ⊤
  let W := ⁅U,N⁆
  let Z := omegaOneCenterAmbient (S : Subgroup G)
  let C := Z ⊓ centralizer (N : Set G)
  let : N.Normal := normalizer_eq_top_iff.mp (top_unique (le_normalizer_conjugateSpanBy A ⊤))
  have hWU : W ≤ U := commutator_le_left _ _
  have hCU : C ≤ U := inf_le_left.trans hZU
  have hZC : Z ≤ centralizer (S : Set G) :=
    fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2
  have hsplit := omegaCenter_le_moved_sup_fixed U N S hUS hZU
  have hCW : C ≤ centralizer (W : Set G) :=
    hCU.trans ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_le hWU))
  have hb := card_fixed_sup_le_mul_of_centralizes W (S : Subgroup G) C hCW
    (inf_le_left.trans hZC)
  have hsmall := hU.moved_plane_sylow_fixed_card_le_two U S A hAS hcard
  exact (card_le_of_le (le_inf hsplit hZC)).trans
    (hb.trans (Nat.mul_le_mul_right (Nat.card C) hsmall))

end Theory.GroupTheory
