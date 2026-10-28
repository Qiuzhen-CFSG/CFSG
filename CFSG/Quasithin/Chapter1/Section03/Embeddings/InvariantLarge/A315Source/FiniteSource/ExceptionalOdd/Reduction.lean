module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.Normalization
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.SourceTransport.Action

/-!
# Restricting the odd-prime Sylow pair to its actual simple component

Permutability restricts through the original component inclusion and transports
through its supplied model equivalence. The odd complement retains its actual
order, and its square-prime divisor forces the same divisor in any overgroup.
Burnside solvability makes the full Sylow product proper in a nonsolvable
model, so a maximal overgroup has odd index and this same prime-square divisor.

Source: Aschbacher--Smith, Proposition 1.3.4, printed pp.510--511, using the
original full Sylow hypothesis in A.3.15.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source.ExceptionalOdd
variable {J : Type*} [Group J]

theorem permuting_restrict (B S D : Subgroup J) (hBD : B ≤ D)
    (hperm : (B : Set J) * (S : Set J) = (S : Set J) * (B : Set J)) :
    (B.subgroupOf D : Set D) * (S.subgroupOf D : Set D) =
      (S.subgroupOf D : Set D) * (B.subgroupOf D : Set D) := by
  apply Set.Subset.antisymm
  · rintro x ⟨b, hb, s, hs, rfl⟩
    have hx : (b : J) * (s : J) ∈ (S : Set J) * (B : Set J) :=
      hperm ▸ Set.mul_mem_mul hb hs
    obtain ⟨s', hs', b', hb', he⟩ := hx
    change s' * b' = (b : J) * (s : J) at he
    have hsD : s' ∈ D := by
      have hh : s' * b' ∈ D := by rw [he]; exact D.mul_mem b.property s.property
      simpa only [mul_inv_cancel_right] using D.mul_mem hh (D.inv_mem (hBD hb'))
    exact ⟨⟨s', hsD⟩, hs', ⟨b', hBD hb'⟩, hb', Subtype.ext he⟩
  · rintro x ⟨s, hs, b, hb, rfl⟩
    have hx : (s : J) * (b : J) ∈ (B : Set J) * (S : Set J) :=
      hperm.symm ▸ Set.mul_mem_mul hs hb
    obtain ⟨b', hb', s', hs', he⟩ := hx
    change b' * s' = (s : J) * (b : J) at he
    have hsD : s' ∈ D := by
      have hh : b' * s' ∈ D := by rw [he]; exact D.mul_mem s.property b.property
      simpa only [inv_mul_cancel_left] using D.mul_mem (D.inv_mem (hBD hb')) hh
    exact ⟨⟨b', hBD hb'⟩, hb', ⟨s', hsD⟩, hs', Subtype.ext he⟩

variable [Finite J]

omit [Finite J] in
theorem prime_square_dvd_complement {p : ℕ} {B : Subgroup J} (hB : XiOddQuotient p B) :
    p^2 ∣ Nat.card B := by
  rcases hB with ⟨_,hc⟩ | ⟨_,hc,_⟩
  · exact hc ▸ dvd_rfl
  · rw [hc]
    exact pow_dvd_pow p (by decide : 2 ≤ 3)

theorem exists_oddIndex_maximal_with_prime_square {p : ℕ} [Fact p.Prime]
    (B : Subgroup J) (S : Sylow 2 J)
    (hB : IsPGroup p B) (hp : p ≠ 2) (hcard : p^2 ∣ Nat.card B)
    (hperm : (B : Set J) * (S : Set J) = (S : Set J) * (B : Set J))
    (hns : ¬ Group.IsSolvable J) :
    ∃ M : Subgroup J, IsCoatom M ∧ ¬ 2 ∣ M.index ∧ B ≤ M ∧
      (S : Subgroup J) ≤ M ∧ p^2 ∣ Nat.card M := by
  have hproper : B ⊔ (S : Subgroup J) ≠ ⊤ := by
    intro hh
    have hs := solvable_product B S hB S.isPGroup' hp hperm
    rw [hh] at hs
    let := hs
    exact hns (Group.isSolvable_of_surjective (f := (Subgroup.topEquiv : (⊤ : Subgroup J) ≃* J).toMonoidHom)
      (Subgroup.topEquiv : (⊤ : Subgroup J) ≃* J).surjective)
  obtain ⟨M,hM,hle⟩ := (eq_top_or_exists_le_coatom (B ⊔ (S : Subgroup J))).resolve_left hproper
  have hBM : B ≤ M := le_sup_left.trans hle
  have hSM : (S : Subgroup J) ≤ M := le_sup_right.trans hle
  exact ⟨M,hM,fun hd => S.not_dvd_index (hd.trans (index_dvd_of_le hSM)),hBM,hSM,
    hcard.trans (card_dvd_of_le hBM)⟩

theorem exists_model_sylow_pair {D B : Subgroup J} [D.Normal]
    (S : Sylow 2 J) {p : ℕ} (hBD : B ≤ D)
    (hB : XiOddQuotient p B)
    (hperm : (B : Set J) * (S : Set J) = (S : Set J) * (B : Set J))
    {K : Type*} [Group K] (e : D ≃* K) :
    ∃ U : Sylow 2 K,
      (U : Subgroup K) = ((S : Subgroup J).subgroupOf D).map e.toMonoidHom ∧
      XiOddQuotient p ((B.subgroupOf D).map e.toMonoidHom) ∧
      (((B.subgroupOf D).map e.toMonoidHom : Set K) * (U : Set K) =
        (U : Set K) * ((B.subgroupOf D).map e.toMonoidHom : Set K)) := by
  obtain ⟨U,hU⟩ := S.exists_subgroupOf_eq_of_normal D
  refine ⟨U.mapSurjective e.surjective, congrArg (map e.toMonoidHom) hU, ?_, ?_⟩
  · exact (hB.of_mulEquiv (subgroupOfEquivOfLe hBD).symm).of_mulEquiv
      (Subgroup.equivMapOfInjective (B.subgroupOf D) e.toMonoidHom e.injective)
  · change ((B.subgroupOf D).map e.toMonoidHom : Set K) *
      ((U : Subgroup D).map e.toMonoidHom : Set K) =
        ((U : Subgroup D).map e.toMonoidHom : Set K) * ((B.subgroupOf D).map e.toMonoidHom : Set K)
    rw [hU]
    simpa only [Set.image_mul, ← Subgroup.coe_map] using
      congrArg (Set.image e.toMonoidHom) (permuting_restrict B S D hBD hperm)
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source.ExceptionalOdd
