module

public import Theory.GroupTheory.ConjugateIncidence

/-!
# Conjugacy steps in the final rank-two elimination

Lemma 11.5.2(1) follows from the transitivity supplied by 11.4.1(1): adjust a
conjugator by an element of `L` to fix `z`. The elementary step from 11.5.3(1)
to its centralizer bound is also recorded, leaving the source's module-dimension
and weak-closure arguments to the chapter analysis.

The hypotheses below are explicit local group-theoretic inputs, independent of
the chapter's counterexample setup. They do not assert the final elimination.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
§11.5, printed p. 779, combined 1 March 2004 manuscript.
Conjugates use `g * x * g⁻¹`, the inverse of the source's exponent convention.
-/

namespace CFSG.Quasithin.Chapter11

variable {G : Type*} [Group G]

/-- The conjugacy assertion of 11.5.2(1), from its explicit transitivity input.
In the chapter, `z ∈ C_V(T) \ {1}` and 11.4.1(1) provides `htrans`. -/
public theorem conjugate_containing_mem_centralizer_orbit
    (L V : Subgroup G) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (htrans : ∀ u ∈ V, u ≠ 1 → ∀ v ∈ V, v ≠ 1 →
      ∃ l ∈ L, (MulAut.conj l) u = v)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (g : G) (hg : z ∈ V.map (MulAut.conj g).toMonoidHom) :
    ∃ c ∈ Subgroup.centralizer ({z} : Set G),
      V.map (MulAut.conj c).toMonoidHom = V.map (MulAut.conj g).toMonoidHom := by
  apply V.exists_centralizer_conjugator hz1 _ g hg
  intro u hu hu1
  obtain ⟨l, hl, hlu⟩ := htrans z hz hz1 u hu hu1
  exact ⟨l, hLV hl, hlu⟩

/-- The centralizer step in 11.5.3(2): an intersection bound by `L`-conjugates
of `V₁` forces `C_G(U) ≤ N_G(V)` whenever `U` lies in none of those conjugates.
The source uses a corank bound to establish the last hypothesis. -/
public theorem centralizer_le_normalizer_of_line_intersections
    (L V V₁ U : Subgroup G) (hUV : U ≤ V)
    (hbound : ∀ g : G, g ∉ Subgroup.normalizer (V : Set G) →
      ∃ l ∈ L, V ⊓ V.map (MulAut.conj g).toMonoidHom ≤
        V₁.map (MulAut.conj l).toMonoidHom)
    (havoid : ∀ l ∈ L, ¬ U ≤ V₁.map (MulAut.conj l).toMonoidHom) :
    Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  let family : Set (Subgroup G) :=
    {W | ∃ l ∈ L, W = V₁.map (MulAut.conj l).toMonoidHom}
  apply Subgroup.centralizer_le_normalizer_of_conjugate_intersection V U family hUV
  · intro g hg
    obtain ⟨l, hl, hle⟩ := hbound g hg
    exact ⟨_, ⟨l, hl, rfl⟩, hle⟩
  · rintro W ⟨l, hl, rfl⟩
    exact havoid l hl

end CFSG.Quasithin.Chapter11
