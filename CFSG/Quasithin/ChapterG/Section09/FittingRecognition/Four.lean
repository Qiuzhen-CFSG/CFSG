module

public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four.Reduction
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four.OrthogonalOrder
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four.NormalizerModel
import Mathlib.Tactic

/-!
# Assembly of the degree-four alternatives in G.9.4

A faithful four-dimensional action has a three-core of order three or nine.
The order-nine normalizer model gives the required orthogonal action and
lower containment. At actor rank two, the core order and actor order make
36 divide the group order; the full orthogonal group has order 72, proving
the source index bound without further overgroup assumptions.

The final theorem here is conditional: the cyclic-three overgroup recognition
and the order-nine normalizer construction remain explicit obligations.
Their proofs must be supplied before this is the degree-four source theorem.
Source: Aschbacher--Smith, G.9.4(3--4), printed pp.354--355/PDF pp.365--366.
-/

public section
namespace CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {A : Subgroup G} {m : ℕ}

/-- The full split orthogonal carrier bounds the index of a faithful
rank-two actor over a core of order nine. -/
theorem orthogonal_index_le_two (h : Setup ρ A 2)
    (hcore : Nat.card (pCore 3 G) = 9) {H : Subgroup OrthogonalFour}
    (hr : OrthogonalRealization ρ H) : H.index ≤ 2 := by
  obtain ⟨e, f, hf⟩ := hr
  have hfour : 4 ∣ Nat.card G := by
    simpa [h.card_actor] using A.card_subgroup_dvd_card
  have hnine : 9 ∣ Nat.card G := hcore ▸ (pCore 3 G).card_subgroup_dvd_card
  have hdiv : 36 ∣ Nat.card G :=
    (show Nat.Coprime 4 9 by decide).mul_dvd_of_dvd_of_dvd hfour hnine
  have hle : 36 ≤ Nat.card G := Nat.le_of_dvd Nat.card_pos hdiv
  have hc : Nat.card H = Nat.card G := (Nat.card_congr e.toEquiv).symm
  have he := H.card_mul_index
  rw [hc, card_orthogonalFour] at he
  nlinarith

omit [FiniteDimensional (ZMod 2) V] in
/-- The order-three branch has actor rank one. -/
theorem rank_one_of_threeCore_card_three (hm : 0 < m)
    (data : ThreeCoreData ρ A m) (hc : Nat.card (pCore 3 G) = 3) : m = 1 := by
  have hr : primeRank 3 (pCore 3 G) ≤ 1 := by
    apply (primeRank_le_iff_elementary_card_le _).mpr
    intro E _
    simpa only [hc, pow_one] using E.card_le_card_group
  have := data.core_rank_ge
  omega

/-- The elementary-nine normalizer calculation supplies exactly the lower
containment and natural action in G.9.4(3). -/
theorem caseThree_of_orthogonalNormalizer (h : Setup ρ A 1)
    (hd : Module.finrank (ZMod 2) V = 4)
    (d : OrthogonalNormalizerModel ρ (pCore 3 G)) : CaseThree ρ 1 := by
  exact ⟨rfl, hd, Or.inr (d.realization h.faithful)⟩

/-- At rank two the same normalizer calculation, together with the actual
actor and core orders, gives the source index bound without another
subgroup classification. -/
theorem caseFour_of_orthogonalNormalizer (h : Setup ρ A 2)
    (data : ThreeCoreData ρ A 2) (hd : Module.finrank (ZMod 2) V = 4)
    (d : OrthogonalNormalizerModel ρ (pCore 3 G)) : CaseFour ρ 2 := by
  obtain ⟨H, _, hreal⟩ := d.realization h.faithful
  exact ⟨rfl, hd, H, orthogonal_index_le_two h
    (threeCore_card_nine_of_rank_two h data hd) hreal, hreal⟩

/-- Conditional assembly for the two independent normalizer branches.
The order-three recognition and order-nine normalizer premises remain
explicit until proved; this is not the unconditional G.9.4 conclusion. -/
theorem degree_four_cases_of_normalizers {K : GroupClass.{u}}
    (h : FittingHypothesis K ρ A m) (hm : 0 < m)
    (hcubic : IsPGroup 3 (⁅fittingSubgroup G, A⁆ : Subgroup G))
    (data : ThreeCoreData ρ A m) (hd : Module.finrank (ZMod 2) V = 4)
    (hcyclic : m = 1 → Nat.card (pCore 3 G) = 3 →
      A ≤ Subgroup.centralizer (pCore 5 G : Set G) → SemilinearRealization ρ)
    (hnine : Nat.card (pCore 3 G) = 9 →
      Nonempty (OrthogonalNormalizerModel ρ (pCore 3 G))) :
    CaseThree ρ m ∨ CaseFour ρ m := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  rcases threeCore_card_cases h.toSetup hm data hd with hc | hc
  · exact Or.inl ⟨rank_one_of_threeCore_card_three hm data hc, hd, Or.inl (hcyclic (rank_one_of_threeCore_card_three hm data hc) hc
      (centralizes_primeCore_of_cubic_commutator hcubic 5 (by decide)))⟩
  · obtain ⟨d⟩ := hnine hc
    have hrank := data.actor_rank_le
    have hm12 : m = 1 ∨ m = 2 := by omega
    rcases hm12 with rfl | rfl
    · exact Or.inl (caseThree_of_orthogonalNormalizer h.toSetup hd d)
    · exact Or.inr (caseFour_of_orthogonalNormalizer h.toSetup data hd d)
end CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four
