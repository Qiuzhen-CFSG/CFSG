module

public import Theory.SpecificGroups.G2.PRegularClasses.GeometricTorus.RankOne

/-!
# Odd-order torus conjugacy in the actual G₂ model

Over an algebraically closed field of characteristic two, every odd-order
split-octonion automorphism is conjugate to an element of the explicit split
torus. For a nonidentity element, its semisimple linear action supplies an
opposite singular eigenpair. Root operations put that pair in standard
position. A determinant-one eigenbasis for the remaining two-dimensional
block then lifts through the actual SL₂ subgroup and finishes the conjugacy.
Every conjugator belongs to the literal octonion automorphism group.

This proves directly the G₂ normal form supplied in algebraic-group language
by GLS III, 1.4.2(e) and 1.4.3(b), `refs/KGroup/GLS3/Chapter1.tex`.
It is the geometric input to the rank-two semisimple class-count argument
used in Aschbacher--Smith, G.9.3, printed pp.356–357 of `refs/quasithin.pdf`.
The root and torus coordinates are from the licensed ATLAS port; see
`LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff`.
-/

public section

namespace Atlas.G2.PRegularClasses
private theorem orderOf_conjugate {G : Type*} [Group G] (c g : G) :
    orderOf (c * g * c⁻¹) = orderOf g := by
  apply (SemiconjBy.orderOf_eq c ?_).symm
  change c * g = (c * g * c⁻¹) * c
  simp only [mul_assoc, inv_mul_cancel, mul_one]

variable {K : Type*} [Field K] [IsAlgClosed K] [CharP K 2]

/-- Every odd-order element of the actual split-octonion automorphism group
is conjugate inside that group to the explicit two-parameter split torus. -/
theorem isConj_torus_of_odd_order (g : Model K) (hg : ¬ 2 ∣ orderOf g) :
    ∃ l m : Kˣ, IsConj g (torus l m) := by
  by_cases h1 : g = 1
  · subst g
    have ht : (torus (1 : Kˣ) 1 : Model K) = 1 := torusHom.map_one
    exact ⟨1, 1, ht.symm ▸ IsConj.refl (1 : Model K)⟩
  · obtain ⟨a, _, c, h0, h7⟩ :=
      exists_conjugate_scaling_pair g h1 (isSemisimple_action g hg)
    have ho : orderOf (c * g * c⁻¹) = orderOf g :=
      orderOf_conjugate c g
    obtain ⟨m, hm⟩ := isConj_torus_of_scaling_pair (c * g * c⁻¹)
      (by rwa [ho]) a h0 h7
    exact ⟨a, m, (isConj_iff.mpr ⟨c, rfl⟩).trans hm⟩

end Atlas.G2.PRegularClasses
