module

public import CFSG.Quasithin.ChapterI.Section06To08.TightNormalizer.Structure.Reduction
public import CFSG.Quasithin.ChapterI.Section06To08.TightNormalizer.Structure.Special.Construction
public import CFSG.Quasithin.ChapterI.Section06To08.TightNormalizer.Structure.Special.LocalStructure
public import CFSG.Quasithin.ChapterI.Section06To08.TightNormalizer.Structure.Special.Closure

/-!
# The special normal closure in I.7.7

The elementary reduction supplies the actual binary model of `R` and an
escaping conjugate `Rʸ`. The construction below gives `U = N_S(R) Rʸ` of
order `2^(3n)`, contained in the normal closure inside `S`, and identifies
`U` with `N_S(N_S(R))`.

The fixed-point and commutator calculations identify the center, derived
subgroup and Frattini subgroup of `U` with `S₁`, and prove the two elementary
subgroup facts needed for closure exhaustion. Discharging those premises
gives `U = W` and `|S : W| = 2`. Since `S` normalizes `W`, it preserves its
derived subgroup `S₁`; in particular, `S₁` is normal in `S₀`.

The final theorem uses only the original branch hypotheses and the earlier
comparison isomorphism `S₁ ≃* R`. Elementary abelianness of `R`, the escaping
conjugate, specialness and exhaustion are all proved, not additional inputs.
As in `Reduction`, the conjugator is in `S`; the escaping conjugate lies in
`N_S(N_S(R))`. Requiring the conjugator itself to normalize `N_S(R)` would
prevent that conjugate from escaping `N_S(R)`.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, I.7.7(5c,6), printed p.428 (PDF p.439).
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterI.Section06To08
namespace TightNormalizerSetup
variable {G : Type*} [Group G] [Finite G]
variable {K : Subgroup G} {g : G} {R S : Subgroup G}

/-- Construct the subgroup used in the large elementary branch, including
its binary parameter, its actual order, and its position in the normalizer tower. -/
theorem exists_specialJoin (h : TightNormalizerSetup K g R S)
    (e : ↥((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)) ≃* R)
    (hp : (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) < S ⊓ conjSubgroup K g)
    (hR2 : Nat.card R ≠ 2)
    (hW : tightNormalClosure R S ≠
      R ⊔ ((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G))) :
    ∃ n : ℕ, 2 ≤ n ∧ Nonempty (R ≃* Multiplicative (Fin n → ZMod 2)) ∧
      ∃ y : G, y ∈ S ∧
        conjSubgroup R y ≤ S ⊓ normalizer (↑(S ⊓ normalizer (R : Set G)) : Set G) ∧
        ¬ conjSubgroup R y ≤ S ⊓ normalizer (R : Set G) ∧
        conjSubgroup R y ⊓ normalizer (R : Set G) = ⊥ ∧
        Nat.card ↥((S ⊓ normalizer (R : Set G)) ⊔ conjSubgroup R y) = 2 ^ (3 * n) ∧
        (S ⊓ normalizer (R : Set G)) ⊔ conjSubgroup R y ≤ tightNormalClosure R S ∧
        (S ⊓ normalizer (R : Set G)) ⊔ conjSubgroup R y =
          S ⊓ normalizer (↑(S ⊓ normalizer (R : Set G)) : Set G) := by
  let : IsElementaryAbelian 2 R := h.elementary_of_normalClosure_ne_product e hp hW
  obtain ⟨n, hn, f, hc⟩ := h.elementaryModel_of_normalClosure_ne_product e hp hR2 hW
  obtain ⟨y, hy, hyN, hnot, htriv⟩ := h.exists_conjugate_with_trivial_normalizer e hp hW
  refine ⟨n, hn, f, y, hy, hyN, hnot, htriv, ?_,
    h.specialJoin_le_normalClosure e hp hy, h.specialJoin_eq_secondNormalizer e hyN htriv⟩
  rw [h.specialJoin_card e hyN htriv, hc, ← pow_mul, Nat.mul_comm n 3]

/-- I.7.7(5c,6), in the large non-product branch. All local-structure and
closure-exhaustion premises are discharged using the constructed conjugate.
The center is identified through the literal inclusion into `G`, and the
index and normality conclusions are relative to `S` and `S₀`, respectively. -/
theorem specialBranch (h : TightNormalizerSetup K g R S)
    (e : ↥((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)) ≃* R)
    (hp : (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) < S ⊓ conjSubgroup K g)
    (hR2 : Nat.card R ≠ 2)
    (hW : tightNormalClosure R S ≠
      R ⊔ ((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G))) :
    let S0 := S ⊓ conjSubgroup K g
    let S1 := S0 ⊓ normalizer (R : Set G)
    let W := tightNormalClosure R S
    ∃ n : ℕ, 2 ≤ n ∧ Nonempty (R ≃* Multiplicative (Fin n → ZMod 2)) ∧
      Nat.card W = 2 ^ (3 * n) ∧
      center W = _root_.commutator W ∧
      _root_.commutator W = frattini W ∧
      IsElementaryAbelian 2 (center W) ∧
      (center W).map W.subtype = S1 ∧
      W.relIndex S = 2 ∧ (S1.subgroupOf S0).Normal := by
  dsimp only
  let : IsElementaryAbelian 2 R := h.elementary_of_normalClosure_ne_product e hp hW
  obtain ⟨n, hn, f, y, hy, hyN, _, htriv, hcard, _, _⟩ :=
    h.exists_specialJoin e hp hR2 hW
  have hP := h.specialJoin_second_elementary e hyN htriv
  have hcover := h.specialJoin_elementary_subgroup_le e hyN htriv
  obtain ⟨_, hUW, hindex⟩ := h.specialJoin_closure_exhaustion e hp hR2 hW hy hyN htriv hP hcover
  have hcenter := h.specialJoin_center_eq_commutator e hyN htriv
  have hfrattini := h.specialJoin_commutator_eq_frattini e hyN htriv
  have helem := h.specialJoin_center_elementary e hyN htriv
  have hmap := h.specialJoin_center_map e hyN htriv
  rw [hUW] at hcard hcenter hfrattini helem hmap
  refine ⟨n, hn, f, hcard, hcenter, hfrattini, helem, hmap, hindex, ?_⟩
  -- `S₁ = Z(W) = W′` is invariant under the conjugation action of `S`.
  have hderived : ⁅tightNormalClosure R S, tightNormalClosure R S⁆ =
      (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) := by
    rw [hcenter, map_subtype_commutator] at hmap
    exact hmap
  have hnW : S ≤ normalizer (tightNormalClosure R S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (normalClosure_le R S)).mp
      (normalClosure_normal R S)
  apply (normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
  rw [← hderived]
  intro s hs
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator, mem_normalizer_iff_map_conj_eq.mp (hnW hs.1)]

end TightNormalizerSetup
end CFSG.Quasithin.ChapterI.Section06To08
