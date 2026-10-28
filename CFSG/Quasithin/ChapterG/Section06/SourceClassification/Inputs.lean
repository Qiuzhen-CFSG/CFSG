module

public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.CubicComparison

/-!
# The explicit remaining transvection source implications

These predicates state the outstanding source theorems, rather than claiming
them. The rank-one predicate is the full G.6.4 conclusion under the original
G.6.1 hypotheses. The normalized-cubic predicate retains the extra original
C.5.12 data and asks only for the acting group's S3-or-S7 isomorphism. The
proved comparison converts the former universal input to the latter.

Source: Aschbacher–Smith, G.6.4, printed pp.345–346, and C.5.12, p.163.
The finite SQTK cover is the literal map appearing in `Hypotheses`; no
SQTK condition is imposed on an original ambient simple group.
-/

public section
namespace CFSG.Quasithin.ChapterG.Section06
open Subgroup
universe u v

def RankOneSourceInput (κ : GroupClass.{u}) : Prop :=
  ∀ (G : Type u) [Group G] (V : Type v) [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (a : G)
    (Cover : Type u) [Group Cover] (q : Cover →* G),
    Hypotheses κ ρ a q →
    Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1 →
    Conclusion ρ a

def NormalizedCubicSourceInput (κ : GroupClass.{u}) : Prop :=
  ∀ (G : Type u) [Group G] (V : Type v) [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (a : G)
    (Cover : Type u) [Group Cover] (q : Cover →* G),
    Hypotheses κ ρ a q →
    Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1 →
    ∀ (S : Sylow 2 G) (c : G), c ^ 3 = 1 → c ≠ 1 →
      (S : Subgroup G) ≤ normalizer (zpowers c : Set G) → a * c = c ^ 2 * a →
      Nonempty (G ≃* Equiv.Perm (Fin 3)) ∨ Nonempty (G ≃* Equiv.Perm (Fin 7))

/-- Construct the specialized source input through its public boundary. -/
theorem NormalizedCubicSourceInput.of_forall {κ : GroupClass.{u}}
    (hG : ∀ (G : Type u) [Group G] (V : Type v) [AddCommGroup V] [Module (ZMod 2) V]
      (ρ : Representation (ZMod 2) G V) (a : G)
      (Cover : Type u) [Group Cover] (q : Cover →* G),
      Hypotheses κ ρ a q →
      Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1 →
      ∀ (S : Sylow 2 G) (c : G), c ^ 3 = 1 → c ≠ 1 →
        (S : Subgroup G) ≤ normalizer (zpowers c : Set G) → a * c = c ^ 2 * a →
        Nonempty (G ≃* Equiv.Perm (Fin 3)) ∨ Nonempty (G ≃* Equiv.Perm (Fin 7))) :
    NormalizedCubicSourceInput.{u,v} κ := hG

/-- Apply the full source implication without exposing its implementation. -/
theorem RankOneSourceInput.apply {κ : GroupClass.{u}}
    (hG : RankOneSourceInput.{u,v} κ)
    {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {a : G}
    {Cover : Type u} [Group Cover] {q : Cover →* G}
    (h : Hypotheses κ ρ a q)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1) :
    Conclusion ρ a := hG G V ρ a Cover q h hr

/-- Apply the original normalized-cubic source implication through its public API. -/
theorem NormalizedCubicSourceInput.apply {κ : GroupClass.{u}}
    (hG : NormalizedCubicSourceInput.{u,v} κ)
    {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {a : G}
    {Cover : Type u} [Group Cover] {q : Cover →* G}
    (h : Hypotheses κ ρ a q)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    (S : Sylow 2 G) (c : G) (hc : c ^ 3 = 1) (hne : c ≠ 1)
    (hn : (S : Subgroup G) ≤ normalizer (zpowers c : Set G))
    (hi : a * c = c ^ 2 * a) :
    Nonempty (G ≃* Equiv.Perm (Fin 3)) ∨ Nonempty (G ≃* Equiv.Perm (Fin 7)) :=
  hG G V ρ a Cover q h hr S c hc hne hn hi

/-- The complete G.6.4 theorem would discharge the narrower original C.5 input. -/
theorem RankOneSourceInput.normalizedCubic {κ : GroupClass.{u}}
    (hG : RankOneSourceInput.{u,v} κ) : NormalizedCubicSourceInput.{u,v} κ := by
  intro G _ V _ _ ρ a Cover _ q h hr S c hc hne hn hi
  let := h.finite_group
  exact conclusion_models_of_normalized_inverted_cubic
    (hG G V ρ a Cover q h hr) S c hc hne hn h.involution hi hr
end CFSG.Quasithin.ChapterG.Section06
