module
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover
public import Theory.AtlasPort.LinearGroups.G2.PerfectSubgroups
public import Theory.SpecificGroups.Alternating.SixSectionNormalizerBound
public import Theory.SpecificGroups.Alternating.TwoThreeCycles
public import Theory.Quasithin.CoprimeRank

/-!
# Alternating-six sections and small Sylow-normalizer index in binary G₂

A perfect subgroup with three-rank at least two cannot normalize a nontrivial
two-subgroup: the actual two-local parabolic cover would embed it in a
perfect subgroup of three-rank at most one. An A₆ two-core quotient supplies
that rank. The faithful normalizer bound then makes a Sylow meeting the
normalizer in index at most four have order at most128. Its actual order
q^6, for q at least four, contradicts this bound.

The consumer maps the original L_v into K_v/O₂(K_v), retaining its perfect
image, A₆ section and actual index-four Sylow geometry. No full-Sylow
normalization or model-family tag is substituted.
Source: Aschbacher--Smith, 12.6.17, printed p.827, with A.2.10--11, p.35,
and the defining-characteristic two-local geometry, pp.3--4.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Atlas.G2
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The corresponding normalizer obstruction in the actual binary G₂ model. -/
theorem two_subgroup_eq_bot_of_perfect_odd_rank_two
    (hq : 2 < Nat.card F) (A R : Subgroup (Model F)) [Group.IsPerfect A]
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hr : 2 ≤ primeRank p A)
    (hp : IsPGroup 2 R) (hn : A ≤ normalizer (R : Set (Model F))) : R = ⊥ := by
  by_contra hR
  obtain ⟨g,hg⟩ := EvenLocal.NormalizerCover.normalizer_conjugate_le_parabolic R hR hp
  let j := (MulAut.conj g).toMonoidHom.comp A.subtype
  have hj : j.range ≤ (normalizer (R : Set _)).map (MulAut.conj g).toMonoidHom := by
    rintro _ ⟨a,rfl⟩
    exact mem_map_of_mem _ (hn a.property)
  exact PerfectSubgroups.no_perfect_odd_rank_two_in_parabolic ho hr hq j
    ((MulAut.conj g).injective.comp A.subtype_injective) (hg.imp hj.trans hj.trans)
end Atlas.G2

namespace Atlas.G2
open Subgroup Theory.GroupTheory
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem no_six_section_of_small_sylow_normalizer_index {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (A : Subgroup (Model F)) [Group.IsPerfect A]
    (e : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 6))
    (S : Sylow 2 (Model F)) (hi : (normalizer (A : Set (Model F))).relIndex S ≤ 4) : False := by
  have hr : 2 ≤ primeRank 3 A := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 A) pCore_isPGroup,
      primeRank_equiv 3 e]
    exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)
  have hq : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ n)
  have hb := Theory.SpecificGroups.Alternating.six_section_sylow_card_le A e
    (fun R hp hR => two_subgroup_eq_bot_of_perfect_odd_rank_two (by omega) A R (by decide : Odd 3) hr hp hR)
    (S : Subgroup (Model F)) S.isPGroup' hi
  have hc : Nat.card S = (Nat.card F)^6 := by
    rw [Nat.card_congr (S.equiv (LieParabolicSetup.sylow (F := F))).toEquiv]
    exact card_unipotent
  have hh := Nat.pow_le_pow_left hq 6
  rw [hc] at hb
  norm_num at hh
  omega
end Atlas.G2
