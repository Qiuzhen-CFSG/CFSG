module

public import Theory.GroupTheory.IndexTwoIntersection
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Fixed index from conjugate centralizers

Let E be abelian in a finite group, with centralizer T of index two in
a normal subgroup C. An element of a conjugate of E centralizes the
corresponding conjugate of T. If it lies in C but not in T, its action
on T has fixed subgroup of index two: the conjugate centralizer gives
the upper bound, while E inside T witnesses nontriviality.

Source: Janko–Thompson, Math. Z. 113 (1970), Lemma 3.1, printed p.388.
-/

namespace Subgroup
variable {G : Type*} [Group G]

private theorem map_centralizer_equiv (E : Subgroup G) (f : G ≃* G) :
    (centralizer (E : Set G)).map f.toMonoidHom =
      centralizer (E.map f.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨f.symm x, ?_, f.apply_symm_apply x⟩
    intro y hy
    apply f.injective
    simpa only [map_mul, f.apply_symm_apply] using hx (f y) (mem_map_of_mem _ hy)

/-- An outside element of a conjugate abelian subgroup induces an automorphism
with fixed subgroup of index two on its original centralizer. -/
public theorem fixed_index_two_of_mem_conjugate
    (E C : Subgroup G) [C.Normal]
    (hET : E ≤ centralizer (E : Set G))
    (hTC : centralizer (E : Set G) ≤ C)
    (hindex : (centralizer (E : Set G)).relIndex C = 2)
    (t x : G) (hx : x ∈ E.map (MulAut.conj t).toMonoidHom)
    (hxC : x ∈ C) (hxT : x ∉ centralizer (E : Set G)) :
    ∃ hn : x ∈ normalizer (centralizer (E : Set G) : Set G),
      (MulAut.fixedSubgroup
        ((centralizer (E : Set G)).normalizerMonoidHom ⟨x, hn⟩)).index = 2 := by
  let T := centralizer (E : Set G)
  let T' := T.map (MulAut.conj t).toMonoidHom
  let : (T.subgroupOf C).Normal := normal_of_index_eq_two hindex
  have hCN : C ≤ normalizer (T : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hTC).mp inferInstance
  have hn : x ∈ normalizer (T : Set G) := hCN hxC
  refine ⟨hn, ?_⟩
  let F := MulAut.fixedSubgroup (T.normalizerMonoidHom ⟨x, hn⟩)
  have hCmap : C.map (MulAut.conj t).toMonoidHom = C :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [C.normalizer_eq_top]; trivial)
  have hT'C : T' ≤ C := by
    rw [← hCmap]
    exact map_mono hTC
  have hT'index : T'.relIndex C = 2 := by
    change (T.map (MulAut.conj t).toMonoidHom).relIndex C = 2
    rw [← hCmap, relIndex_map_map_of_injective _ _ (MulAut.conj t).injective]
    exact hindex
  let : (T'.subgroupOf C).Normal := normal_of_index_eq_two hT'index
  have hd : T'.relIndex T ∣ 2 := by
    have hh := (T'.subgroupOf C).relIndex_dvd_index_of_normal (T.subgroupOf C)
    rw [relIndex_subgroupOf hTC] at hh
    exact hT'index ▸ hh
  have hle : T'.subgroupOf T ≤ F := by
    intro a ha
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    apply Subtype.ext
    change x * (a : G) * x⁻¹ = (a : G)
    apply mul_inv_eq_iff_eq_mul.mpr
    have ha' : (a : G) ∈ centralizer
        (E.map (MulAut.conj t).toMonoidHom : Set G) := by
      rw [← map_centralizer_equiv]
      exact ha
    exact ha' x hx
  have hdiv : F.index ∣ 2 := dvd_trans (index_dvd_of_le hle) hd
  rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hone | htwo
  · exfalso
    apply hxT
    intro e he
    have hf : (⟨e, hET he⟩ : T) ∈ F := index_eq_one.mp hone ▸ mem_top _
    have heq := congrArg Subtype.val ((MulAut.mem_fixedSubgroup _ _).mp hf)
    change x * e * x⁻¹ = e at heq
    exact (mul_inv_eq_iff_eq_mul.mp heq).symm
  · exact htwo

end Subgroup
