module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.SourceBounds

/-!
# Rank-one size reduction for K.2

Work over the original binary space, so that coefficient-field automorphisms
retain their actual displacement. If a small elementary actor meets F*(G),
three conjugates of an inner involution bound the degree by twelve over a
prime field and eighteen over a quadratic field. Otherwise the actor embeds
in the diagonal--field outer group: its rank is at most the field exponent,
and four conjugates bound the degree by eight or sixteen.

The projective lower bound q - 1 ≤ 2 dim(V) therefore gives q ≤ 25 for a
prime field and q ≤ 37 for a quadratic field. An odd square at most 37 is
at most 25. This uses the exact exponent domain of K.2; it is not a bound
for unrestricted field extensions.

The two definitions below specify independent missing model results. The
conditional assembly proves all intervening representation and arithmetic
steps, but does not assert either model result or the unconditional K.2 bound.
Their discharge remains with the RankOneSize owner.

Source: Aschbacher--Smith, K.2, printed p.453; Guralnick--Malle,
Classification of 2F-modules I, (2.5)--(2.6) and Proposition 4.1, pp.4,8--9.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

universe u v

/-- The needed projective-degree minimum, with arbitrary central covers and
no offender hypothesis. The exceptional small parameters are not requested. -/
def ProjectiveDegreeBound : Prop :=
  ∀ {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V), SourceAction ρ →
    ∀ {p e : ℕ}, p.Prime → Odd p → (e = 1 ∨ e = 2) → 25 < p ^ e →
      ClassicalGroup.IsPSL
        ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 (p ^ e) →
      p ^ e - 1 ≤ 2 * Module.finrank (ZMod 2) V

/-- Generation in the actual ambient group, together with the outer actor's
rank bound. Inner, diagonal and field involutions must all be accounted for.
No ratio or representation-degree bound is among these hypotheses. -/
def SourceGenerationBounds : Prop :=
  ∀ {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V), SourceAction ρ →
    ∀ {p e : ℕ}, p.Prime → Odd p → (e = 1 ∨ e = 2) → 25 < p ^ e →
      ClassicalGroup.IsPSL
        ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 (p ^ e) →
      (∀ t : G, t ∈ generalizedFitting G → t ≠ 1 → t ^ 2 = 1 →
        ∃ g : Fin 3 → G, generalizedFitting G ≤
          closure (Set.range fun i => g i * t * (g i)⁻¹)) ∧
      (∀ t : G, t ∉ generalizedFitting G → t ^ 2 = 1 →
        ∃ g : Fin 4 → G, generalizedFitting G ≤
          closure (Set.range fun i => g i * t * (g i)⁻¹)) ∧
      (∀ A : Subgroup G, IsElementaryTwo A →
        A ⊓ generalizedFitting G = ⊥ → rank A ≤ e)

variable {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (h : SourceAction ρ)
include h

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- The actual quasisimple component has zero fixed space on the source module. -/
theorem source_fixedSpace_eq_bot : fixedSpace ρ (generalizedFitting G) = ⊥ := by
  let : IsQuasisimple (generalizedFitting G) := h.quasisimple
  let : IsSimpleGroup ((generalizedFitting G) ⧸ center (generalizedFitting G)) :=
    h.quasisimple.simple
  let : Nontrivial (generalizedFitting G) :=
    (QuotientGroup.mk'_surjective (center (generalizedFitting G))).nontrivial
  exact fixedSpace_eq_bot_of_faithful_irreducible_on ρ _ h.faithful h.irreducible

omit [Finite G] in
/-- Use the original actor's rank when its involution has specified conjugate
 generators. In particular the outer branch does not use ambient rank three. -/
theorem degree_le_of_actor_conjugates {A : Subgroup G} {k r : ℕ}
    (hsmall : fixedCodim ρ A ≤ 2 * rank A) (hrank : rank A ≤ r)
    {t : G} (ht : t ∈ A) (g : Fin k → G)
    (hgen : generalizedFitting G ≤
      closure (Set.range fun i => g i * t * (g i)⁻¹)) :
    Module.finrank (ZMod 2) V ≤ k * (2 * r) := by
  have hle : fixedSpace ρ A ≤ fixedSpace ρ (zpowers t) := by
    intro v hv a
    exact hv ⟨a, (zpowers_le.mpr ht) a.property⟩
  have hdim := Submodule.finrank_mono hle
  have hdimA := fixedCodim_add_finrank ρ A
  have hdimt := fixedCodim_add_finrank ρ (zpowers t)
  have htbound : fixedCodim ρ (zpowers t) ≤ 2 * r := by omega
  exact (finrank_le_mul_fixedCodim_of_conjugate_generation ρ _
    (source_fixedSpace_eq_bot ρ h) t g hgen).trans (Nat.mul_le_mul_left k htbound)

/-- The inner/outer split improves the quadratic-field binary bound to eighteen.
The generation and outer-rank calculation remain explicit model inputs. -/
theorem source_degree_le_of_generation
    (hgenerators : SourceGenerationBounds.{u, v})
    {p e : ℕ} (hp : p.Prime) (ho : Odd p) (he : e = 1 ∨ e = 2)
    (hlarge : 25 < p ^ e)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 (p ^ e))
    (hq : cubicRatio ρ ≤ 2) :
    Module.finrank (ZMod 2) V ≤ if e = 1 then 12 else 18 := by
  obtain ⟨hinner, houter, hrank⟩ := hgenerators ρ h hp ho he hlarge hm
  obtain ⟨A, hA, _, hsmall⟩ := (cubicRatio_le_nat_iff ρ 2).mp hq
  let : IsElementaryAbelian 2 A := hA.2
  by_cases hmeet : A ⊓ generalizedFitting G = ⊥
  · obtain ⟨t, ht, ht1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
    have htL : t ∉ generalizedFitting G := by
      intro htL
      have htbot : t ∈ (⊥ : Subgroup G) := hmeet ▸ (show t ∈ A ⊓ generalizedFitting G from ⟨ht, htL⟩)
      exact ht1 htbot
    obtain ⟨g, hg⟩ := houter t htL (elemPow_eq_one_of_isElementaryAbelian t ht)
    have hd := degree_le_of_actor_conjugates ρ h hsmall (hrank A hA hmeet) ht g hg
    rcases he with rfl | rfl <;> norm_num at hd ⊢ <;> omega
  · obtain ⟨t, ht, ht1⟩ := (A ⊓ generalizedFitting G).bot_or_exists_ne_one.resolve_left hmeet
    obtain ⟨g, hg⟩ := hinner t ht.2 ht1 (elemPow_eq_one_of_isElementaryAbelian t ht.1)
    have hr := rank_le_of_primeRank_le hA
      (source_two_rank_pslTwo ρ h hp ho he (by omega) hm)
    have hd := degree_le_of_actor_conjugates ρ h hsmall hr ht.1 g hg
    rcases he with rfl | rfl <;> norm_num at hd ⊢ <;> exact hd

omit ρ h in
/-- An odd quadratic-field order cannot lie strictly between 25 and 37. -/
theorem field_order_le_twentyFive_of_degree {p e d : ℕ} (ho : Odd p)
    (he : e = 1 ∨ e = 2) (hlo : 1 ≤ p ^ e)
    (hlower : p ^ e - 1 ≤ 2 * d) (hupper : d ≤ if e = 1 then 12 else 18) :
    p ^ e ≤ 25 := by
  rcases he with rfl | rfl
  · simp only [pow_one, ite_true] at *
    omega
  · norm_num at hupper
    have hq : p ^ 2 ≤ 37 := by omega
    have hp6 : p ≤ 6 := by nlinarith
    obtain ⟨k, hk⟩ := ho
    have hp5 : p ≤ 5 := by omega
    nlinarith

/-- This supplies the exact `hsize` contract once both independent model
calculations have been proved. It does not discharge those calculations. -/
theorem source_field_order_le_twentyFive_of_bounds
    (hdegree : ProjectiveDegreeBound.{u, v})
    (hgenerators : SourceGenerationBounds.{u, v})
    {p e : ℕ} (hp : p.Prime) (ho : Odd p) (he : e = 1 ∨ e = 2)
    (_hlo : 4 ≤ p ^ e)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 (p ^ e))
    (hq : cubicRatio ρ ≤ 2) : p ^ e ≤ 25 := by
  by_cases hsmall : p ^ e ≤ 25
  · exact hsmall
  have hlarge : 25 < p ^ e := Nat.lt_of_not_ge hsmall
  exact field_order_le_twentyFive_of_degree ho he (by omega)
    (hdegree ρ h hp ho he hlarge hm)
    (source_degree_le_of_generation ρ h hgenerators hp ho he hlarge hm hq)

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize
