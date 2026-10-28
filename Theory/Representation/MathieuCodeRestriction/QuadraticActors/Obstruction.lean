module
public import Theory.Representation.BinaryOffender.Replacement
public import Theory.Representation.BinaryOffender.EquivariantOffender
/-!
# Quadratic actors too small to offend

Thompson replacement reduces an offender to a quadratic elementary actor.
If such actors have order at most four, while involutions displace more than
two dimensions, the offender inequality is impossible. The finite clique lemma
provides the combinatorial cardinality argument used by the Mathieu certificates.
Source: Aschbacher--Smith B.1.4 and K.4, printed pp.68--69,458--459.
-/
public section
open scoped IsMulCommutative
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)
theorem quadratic_conj {A : Subgroup G} (hq : IsQuadratic ρ A) (g : G) :
    IsQuadratic ρ (A.map (MulAut.conj g).toMonoidHom) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ v
  change ρ (g * a * g⁻¹) (ρ (g * b * g⁻¹) v - v) = ρ (g * b * g⁻¹) v - v
  have hh := congrArg (ρ g) (hq a ha b hb (ρ g⁻¹ v))
  simpa only [map_mul, Module.End.mul_apply, map_sub, ρ.inv_self_apply,
    ρ.self_inv_apply] using hh

theorem not_isFFModule_of_quadratic_card_le_four [Finite G]
    [FiniteDimensional (ZMod 2) V]
    (hcard : ∀ A : Subgroup G, IsElementaryAbelian 2 A → IsQuadratic ρ A → Nat.card A ≤ 4)
    (hdisp : ∀ a : G, orderOf a = 2 → 2 < fixedCodim ρ (Subgroup.zpowers a)) :
    ¬ IsFFModule ρ := by
  rintro ⟨A, hA⟩
  obtain ⟨B, _, hB, hq, _⟩ := hA.exists_quadratic_minimalBestOffender ρ
  let : IsElementaryAbelian 2 B := hB.1.1.2
  have hc := hcard B inferInstance hq
  have hr : rank B ≤ 2 := by
    exact (Nat.log_mono_right hc : Nat.log 2 (Nat.card B) ≤ Nat.log 2 4)
  obtain ⟨a, ha, ha1⟩ := B.bot_or_exists_ne_one.resolve_left hB.1.1.1
  have ho : orderOf a = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian a ha) ha1
  have hd := hdisp a ho
  have hle : fixedSpace ρ B ≤ fixedSpace ρ (Subgroup.zpowers a) :=
    fixedSpace_antitone ρ (Subgroup.zpowers_le.mpr ha)
  have hf := Submodule.finrank_mono hle
  have hdimB := fixedCodim_add_finrank ρ B
  have hdima := fixedCodim_add_finrank ρ (Subgroup.zpowers a)
  have hb := (hB.1.isOffender ρ).2
  omega
end Representation.BinaryOffender

namespace MathieuCode.QuadraticActors
lemma clique_card_le_four {α : Type*} [Fintype α] [DecidableEq α]
    (z : α) (adj : α → α → Bool)
    (hb : ∀ v w, v ≠ z → w ≠ z → w ≠ v → adj v w = true →
      (Finset.univ.filter (fun k => adj v k && adj w k)).card ≤ 4)
    (s : Finset α) (hs : ∀ v ∈ s, ∀ w ∈ s, adj v w = true) : s.card ≤ 4 := by
  classical
  by_contra hc
  have hnot (t : Finset α) (ht : t.card ≤ 2) (hst : s ⊆ t) : False := by
    have := Finset.card_le_card hst
    omega
  obtain ⟨v, hv, hvz⟩ : ∃ v ∈ s, v ≠ z := by
    by_contra h
    push Not at h
    exact hnot {z} (by simp) (by intro x hx; simpa using h x hx)
  obtain ⟨w, hw, hwz, hwv⟩ : ∃ w ∈ s, w ≠ z ∧ w ≠ v := by
    by_contra h
    push Not at h
    apply hnot {z,v} (Finset.card_le_two)
    intro x hx
    by_cases he : x = z
    · simp [he]
    · simp [h x hx he]
  have hsub : s ⊆ Finset.univ.filter (fun k => adj v k && adj w k) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, Bool.and_eq_true, true_and]
    exact ⟨hs v hv k hk, hs w hw k hk⟩
  exact hc ((Finset.card_le_card hsub).trans (hb v w hvz hwz hwv (hs v hv w hw)))
end MathieuCode.QuadraticActors
