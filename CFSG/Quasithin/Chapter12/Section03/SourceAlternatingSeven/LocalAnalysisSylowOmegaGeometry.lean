module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowOmegaCore
public import Theory.GroupAction.OddFourGroupLine
public import Theory.GroupTheory.NormalizingInvolutionCard
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The hyperplane and odd-action steps on the actual Sylow center

Write Z = Ω₁Z(T), F = C_Z(L), and A = ⟨F,e₆⟩. If |Z| ≤ 4|F| and
F is nontrivial, every conjugate of A under N(T) meets A nontrivially.
Residual control then forces N(T) ≤ N(L), contrary to escape. Thus F is
trivial. The two marked involutions give |Z| ≥ 4, so the bound gives |Z|=4.

The N(T)-action on Z has odd image because T lies in its kernel. Escape
makes this image nontrivial, hence transitive on the three nonidentity
points. This supplies the literal transport prohibited by `no_transport`.
The final consumer retains the omega-cardinality bound as an explicit
premise. Proving it from the actual omega-span and the original Setup is
still required for the source theorem; this file does not assert 3.3.22.

Source: Aschbacher–Smith, 3.3.22, printed pp.597–598, refs/quasithin.pdf.
-/

@[expose] public noncomputable section

open Subgroup
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}
variable {E : S.NaturalCoordinates}
namespace SylowNormalizer.Points
variable (P : Points E)

include P in
/-- The two marked points span a four-group in the actual omega center. -/
lemma omega_card_ge_four : 4 ≤ Nat.card (omegaCenterIn (T : Subgroup G)) := by
  classical
  have ht : orderOf (P.two : G) = 2 := orderOf_eq_prime
    ((mem_omegaCenterIn_iff _ _).mp P.two_mem_omega).2.2 P.two_ne_one
  have hf : IsOfFinOrder (P.two : G) := isOfFinOrder_iff_pow_eq_one.mpr
    ⟨2, by decide, ((mem_omegaCenterIn_iff _ _).mp P.two_mem_omega).2.2⟩
  have hout : (P.six : G) ∉ zpowers (P.two : G) := by
    intro hm
    rw [hf.mem_zpowers_iff_mem_range_orderOf, ht] at hm
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hm
    have hi2 := Finset.mem_range.mp hi
    have hi' : i = 0 ∨ i = 1 := by omega
    rcases hi' with rfl | rfl
    · exact P.six_ne_one (by simpa using he.symm)
    · exact P.two_ne_six (by simpa using he)
  have hn : (P.six : G) ∈ normalizer (zpowers (P.two : G) : Set G) := by
    apply Subgroup.centralizer_le_normalizer
    intro z hz
    exact P.six_central z ((zpowers_le.mpr (S.chosen.le_sylow P.two.property)) hz)
  have hc := card_sup_zpowers_of_normalizing_involution (zpowers (P.two : G))
    (P.six : G) ((mem_omegaCenterIn_iff _ _).mp P.six_mem_omega).2.2 hout hn
  rw [Nat.card_zpowers, ht] at hc
  calc
    4 = Nat.card (zpowers (P.two : G) ⊔ zpowers (P.six : G) : Subgroup G) := by
      simpa using hc.symm
    _ ≤ _ := card_le_of_le (sup_le (zpowers_le.mpr P.two_mem_omega)
      (zpowers_le.mpr P.six_mem_omega))

def slice : Subgroup G := P.fixed ⊔ zpowers (P.six : G)

lemma slice_le_omega : P.slice ≤ omegaCenterIn (T : Subgroup G) :=
  sup_le inf_le_left (zpowers_le.mpr P.six_mem_omega)

lemma six_normalizes_fixed : (P.six : G) ∈ normalizer (P.fixed : Set G) := by
  apply Subgroup.centralizer_le_normalizer
  intro c hc
  exact P.six_central c ((mem_omegaCenterIn_iff _ _).mp hc.1).1

lemma six_not_mem_fixed : (P.six : G) ∉ P.fixed := by
  intro h
  exact P.six_ne_one (congrArg Subtype.val (natural_fixed_eq_one (E := E) h.2))

lemma slice_card : Nat.card P.slice = 2 * Nat.card P.fixed :=
  card_sup_zpowers_of_normalizing_involution P.fixed P.six
    ((mem_omegaCenterIn_iff _ _).mp P.six_mem_omega).2.2 P.six_not_mem_fixed
    P.six_normalizes_fixed

lemma slice_cases {z : G} (hz : z ∈ P.slice) :
    z ∈ P.fixed ∨ ∃ c ∈ P.fixed, z = c * (P.six : G) := by
  classical
  have hs : z ∈ (P.fixed : Set G) * (zpowers (P.six : G) : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _
      (zpowers_le.mpr P.six_normalizes_fixed)]
    exact hz
  obtain ⟨c, hc, d, hd, rfl⟩ := hs
  change c ∈ P.fixed at hc
  have ho : orderOf (P.six : G) = 2 := orderOf_eq_prime
    ((mem_omegaCenterIn_iff _ _).mp P.six_mem_omega).2.2 P.six_ne_one
  have hf : IsOfFinOrder (P.six : G) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide,
      ((mem_omegaCenterIn_iff _ _).mp P.six_mem_omega).2.2⟩
  change d ∈ zpowers (P.six : G) at hd
  rw [hf.mem_zpowers_iff_mem_range_orderOf, ho] at hd
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hd
  have hi2 := Finset.mem_range.mp hi
  have hi' : i = 0 ∨ i = 1 := by omega
  rcases hi' with rfl | rfl
  · exact Or.inl (by simpa only [pow_zero, mul_one] using hc)
  · exact Or.inr ⟨c, hc, by rw [pow_one]⟩

/-- Counting the intersection of two hyperplanes of the actual omega group. -/
lemma slice_intersection_ne_bot
    (hcard : Nat.card (omegaCenterIn (T : Subgroup G)) ≤ 4 * Nat.card P.fixed)
    (hfix : P.fixed ≠ ⊥) {g : G} (hg : g ∈ normalizer (T : Set G)) :
    P.slice ⊓ P.slice.map (MulAut.conj g).toMonoidHom ≠ ⊥ := by
  let Z := omegaCenterIn (T : Subgroup G)
  let : IsElementaryAbelian 2 Z := omegaCenterIn_elementary _
  let A := P.slice
  let B := P.slice.map (MulAut.conj g).toMonoidHom
  have hAZ : A ≤ Z := P.slice_le_omega
  have hBZ : B ≤ Z := by
    have he : Z.map (MulAut.conj g).toMonoidHom = Z :=
      mem_normalizer_iff_map_conj_eq.mp (normalizer_le_normalizer_omegaCenterIn _ hg)
    exact (map_mono hAZ).trans_eq he
  have hn : B ≤ normalizer (A : Set G) := by
    intro b hb
    apply Subgroup.centralizer_le_normalizer
    intro a ha
    exact setLike_mul_comm (hAZ ha) (hBZ hb)
  intro he
  have hp := card_mul_eq_card_inf_mul_card_sup_of_normalizes A B hn
  have ha : Nat.card A = 2 * Nat.card P.fixed := P.slice_card
  have hb : Nat.card B = 2 * Nat.card P.fixed := by
    rw [card_map_of_injective (MulAut.conj g).injective]
    exact P.slice_card
  have hj : Nat.card (A ⊔ B : Subgroup G) ≤ 4 * Nat.card P.fixed :=
    (card_le_of_le (sup_le hAZ hBZ)).trans hcard
  have hf : 1 < Nat.card P.fixed := (one_lt_card_iff_ne_bot _).mpr hfix
  rw [he, card_bot, one_mul, ha, hb] at hp
  nlinarith

/-- The two ambient residual identities eliminate the extra central summand. -/
lemma fixed_eq_bot_of_omega_card_bound (M : P.Models) (R : P.AmbientResiduals)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hcard : Nat.card (omegaCenterIn (T : Subgroup G)) ≤ 4 * Nat.card P.fixed) :
    P.fixed = ⊥ := by
  by_contra hfix
  apply hescape
  intro g hg
  obtain ⟨x, hx, hx1⟩ := (P.slice ⊓ P.slice.map (MulAut.conj g).toMonoidHom).bot_or_exists_ne_one.resolve_left
    (P.slice_intersection_ne_bot hcard hfix hg)
  obtain ⟨z, hz, he⟩ := hx.2
  have hz1 : z ≠ 1 := by
    intro h
    apply hx1
    rw [← he, h, map_one]
  apply P.residual_slice_transport M R hg hz1 (P.slice_cases hz)
  apply P.slice_cases
  change (MulAut.conj g).toMonoidHom z ∈ P.slice
  rw [he]
  exact hx.1

/-- A nontrivial odd image on the actual four-group supplies the marked transport. -/
lemma transport_of_omega_card_four (M : P.Models) (R : P.AmbientResiduals)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hcard : Nat.card (omegaCenterIn (T : Subgroup G)) = 4) :
    ∃ g ∈ normalizer (T : Set G), g * (P.two : G) * g⁻¹ = P.six := by
  classical
  let Z := omegaCenterIn (T : Subgroup G)
  let : IsElementaryAbelian 2 Z := omegaCenterIn_elementary _
  have hNZ : normalizer (T : Set G) ≤ normalizer (Z : Set G) :=
    normalizer_le_normalizer_omegaCenterIn _
  have hTZ : (T : Subgroup G) ≤ centralizer (Z : Set G) := by
    intro t ht z hz
    exact (((mem_omegaCenterIn_iff _ _).mp hz).2.1 t ht).symm
  let f : normalizer (T : Set G) →* MulAut Z :=
    Z.normalizerMonoidHom.comp (inclusion hNZ)
  obtain ⟨g, hg, hout⟩ := SetLike.not_le_iff_exists.mp hescape
  have ho : Odd (orderOf (f ⟨g, hg⟩)) :=
    Theory.GroupAction.normalizer_action_order_odd T Z hNZ hTZ ⟨g, hg⟩
  have hn : f ⟨g, hg⟩ ≠ 1 := by
    intro he
    apply hout
    apply P.six_fixed_normalizes_component M R hg
    exact congrArg (fun a : MulAut Z => ((a ⟨P.six, P.six_mem_omega⟩ : Z) : G)) he
  have hl : 2 < orderOf (f ⟨g, hg⟩) := by
    have hone : orderOf (f ⟨g, hg⟩) ≠ 1 := fun h => hn (orderOf_eq_one_iff.mp h)
    obtain ⟨k, hk⟩ := ho
    omega
  have hr : 2 < Nat.card f.range := by
    apply hl.trans_le
    rw [← Nat.card_zpowers]
    exact card_le_of_le (zpowers_le.mpr ⟨⟨g, hg⟩, rfl⟩)
  obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.mp
    (MulAction.nonidentity_mem_orbit_of_four_automorphism_subgroup hcard f.range hr
      ⟨P.two, P.two_mem_omega⟩ (fun h => P.two_ne_one (congrArg Subtype.val h))
      ⟨P.six, P.six_mem_omega⟩ (fun h => P.six_ne_one (congrArg Subtype.val h)))
  obtain ⟨n, hn⟩ := a.property
  refine ⟨n, n.property, ?_⟩
  have hh := congrArg (fun z : Z => (z : G)) ha
  change ((a : MulAut Z) ⟨P.two, P.two_mem_omega⟩ : G) = P.six at hh
  rw [← hn] at hh
  exact hh

/-- Conditional assembly, retaining the unproved omega-span bound. -/
lemma transport_of_omega_card_bound (M : P.Models) (R : P.AmbientResiduals)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hcard : Nat.card (omegaCenterIn (T : Subgroup G)) ≤ 4 * Nat.card P.fixed) :
    ∃ g ∈ normalizer (T : Set G), g * (P.two : G) * g⁻¹ = P.six := by
  have he := P.fixed_eq_bot_of_omega_card_bound M R hescape hcard
  apply P.transport_of_omega_card_four M R hescape
  apply le_antisymm _ P.omega_card_ge_four
  simpa only [he, card_bot, mul_one] using hcard

lemma normalizer_le_of_omega_card_bound (M : P.Models) (R : P.AmbientResiduals)
    (hcard : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G) →
      Nat.card (omegaCenterIn (T : Subgroup G)) ≤ 4 * Nat.card P.fixed) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  by_contra hn
  obtain ⟨g, hg, he⟩ := P.transport_of_omega_card_bound M R hn (hcard hn)
  exact no_transport M R S.chosen.sylow_normalizes_component hg he

end SylowNormalizer.Points
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
