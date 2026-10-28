module

public import Theory.GroupTheory.BaerSuzukiLocal

/-!
# The final local contradiction in Lemma 7.6.1

Write `H = C_G(Z₁)`. A hyperplane `A₁` of `V` contained in `O₂(H)` must
equal `V ∩ O₂(H)` when `V` is not contained in that core. Normality inside
`H` preserves this index for every `H`-conjugate of `V`. Relative
Baer–Suzuki then supplies a noncommuting conjugate pair whose join is not
a two-group, contradicting the preceding pair-generation argument.

These are conditional assembly lemmas for the last paragraph on printed
p.703 of Aschbacher–Smith, combined manuscript of 1 March 2004. The
hyperplane inclusion, failure of core containment, and generation of the
noncommuting pairs are explicit inputs. They remain to be constructed
from §§7.6–7.7 and Proposition 3.2.10(6); this module does not claim the
complete source exclusion.
-/

namespace CFSG.Quasithin.Chapter7.Section06To07

open Subgroup

variable {G : Type*} [Group G]

private theorem eq_inf_of_prime_relIndex
    (A V N : Subgroup G) (hAV : A ≤ V) (hAN : A ≤ N)
    (hindex : (A.relIndex V).Prime) (hVN : ¬ V ≤ N) : A = V ⊓ N := by
  have hAI : A ≤ V ⊓ N := le_inf hAV hAN
  have hprod := relIndex_mul_relIndex A (V ⊓ N) V hAI inf_le_left
  have hone : A.relIndex (V ⊓ N) = 1 := by
    rcases (Nat.dvd_prime hindex).mp (show (V ⊓ N).relIndex V ∣ A.relIndex V from
      ⟨A.relIndex (V ⊓ N), by rw [Nat.mul_comm]; exact hprod.symm⟩) with h | h
    · exact (hVN ((relIndex_eq_one.mp h).trans inf_le_right)).elim
    · rw [h] at hprod
      exact Nat.eq_of_mul_eq_mul_right hindex.pos (by simpa using hprod)
  exact le_antisymm hAI (relIndex_eq_one.mp hone)

private theorem core_relIndex_conjugate
    (H V : Subgroup G) (g : G) (hg : g ∈ H) :
    (H.pCoreIn 2).relIndex (V.map (MulAut.conj g).toMonoidHom) =
      (H.pCoreIn 2).relIndex V := by
  have hn : ((H.pCoreIn 2).subgroupOf H).Normal := by
    change (((pCore 2 H).map H.subtype).comap H.subtype).Normal
    rw [comap_map_eq_self_of_injective H.subtype_injective]
    infer_instance
  have hnorm := (normal_subgroupOf_iff_le_normalizer (pCoreIn_le 2 H)).mp hn
  have he : (H.pCoreIn 2).map (MulAut.conj g).toMonoidHom = H.pCoreIn 2 :=
    mem_normalizer_iff_map_conj_eq.mp (hnorm hg)
  calc
    _ = ((H.pCoreIn 2).map (MulAut.conj g).toMonoidHom).relIndex
        (V.map (MulAut.conj g).toMonoidHom) := by rw [he]
    _ = _ := relIndex_map_map_of_injective _ _ (MulAut.conj g).injective

/-- The hyperplane is the exact core intersection, and every local conjugate
has the same index-two image modulo that core. -/
public theorem centralizer_core_intersection_and_conjugate_index
    (Z V A : Subgroup G) (hAV : A ≤ V)
    (hAcore : A ≤ (centralizer (Z : Set G)).pCoreIn 2)
    (hindex : A.relIndex V = 2)
    (hVcore : ¬ V ≤ (centralizer (Z : Set G)).pCoreIn 2) :
    A = V ⊓ (centralizer (Z : Set G)).pCoreIn 2 ∧
      ∀ g ∈ centralizer (Z : Set G),
        ((centralizer (Z : Set G)).pCoreIn 2).relIndex
          (V.map (MulAut.conj g).toMonoidHom) = 2 := by
  have he := eq_inf_of_prime_relIndex A V _ hAV hAcore
    (hindex ▸ Nat.prime_two) hVcore
  refine ⟨he, ?_⟩
  intro g hg
  rw [core_relIndex_conjugate _ _ g hg, ← inf_relIndex_left V _, ← he, hindex]

/-- An escaping two-subgroup with a hyperplane in the local core has a
noncommuting conjugate of core index two whose join is not a two-group. -/
public theorem noncentralizing_pair_obstruction [Finite G]
    (Z V A : Subgroup G) (hV : IsPGroup 2 V)
    (hVZ : V ≤ centralizer (Z : Set G)) (hAV : A ≤ V)
    (hAcore : A ≤ (centralizer (Z : Set G)).pCoreIn 2)
    (hindex : A.relIndex V = 2)
    (hVcore : ¬ V ≤ (centralizer (Z : Set G)).pCoreIn 2) :
    ∃ g ∈ centralizer (Z : Set G),
      ((centralizer (Z : Set G)).pCoreIn 2).relIndex
        (V.map (MulAut.conj g).toMonoidHom) = 2 ∧
      ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G) ∧
      ¬ IsPGroup 2 (V ⊔ V.map (MulAut.conj g).toMonoidHom : Subgroup G) := by
  obtain ⟨g, hg, hc, hp⟩ := exists_noncentralizing_conjugate_sup_not_isPGroup
    (centralizer (Z : Set G)) V hVZ hV hVcore
  exact ⟨g, hg,
    (centralizer_core_intersection_and_conjugate_index Z V A hAV hAcore hindex hVcore).2
      g hg, hc, hp⟩

/-- The terminal assembly consumes the source pair-generation result only
for the index-two noncommuting pairs; commuting pairs are discharged by
the relative Baer–Suzuki argument. -/
public theorem false_of_hyperplane_pair_generation [Finite G]
    (Z V A : Subgroup G) (hV : IsPGroup 2 V)
    (hVZ : V ≤ centralizer (Z : Set G)) (hAV : A ≤ V)
    (hAcore : A ≤ (centralizer (Z : Set G)).pCoreIn 2)
    (hindex : A.relIndex V = 2)
    (hVcore : ¬ V ≤ (centralizer (Z : Set G)).pCoreIn 2)
    (hpair : ∀ g ∈ centralizer (Z : Set G),
      ((centralizer (Z : Set G)).pCoreIn 2).relIndex
        (V.map (MulAut.conj g).toMonoidHom) = 2 →
      ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G) →
      IsPGroup 2 (V ⊔ V.map (MulAut.conj g).toMonoidHom : Subgroup G)) : False := by
  obtain ⟨g, hg, hi, hc, hp⟩ :=
    noncentralizing_pair_obstruction Z V A hV hVZ hAV hAcore hindex hVcore
  exact hp (hpair g hg hi hc)

end CFSG.Quasithin.Chapter7.Section06To07
