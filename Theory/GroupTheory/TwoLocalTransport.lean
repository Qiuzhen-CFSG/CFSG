module

public import Theory.Quasithin

/-!
# Transport of two-local subgroups

An isomorphism carries the normalizer of a nontrivial two-subgroup to the
normalizer of its image. This shared interface lets the quasithin rank and
two-local uniqueness developments be imported together.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, §0.1
(definition of a two-local subgroup) and §1.2 (uniqueness arguments).
-/

namespace Theory.GroupTheory

/-- Group isomorphisms preserve two-local subgroups. -/
public theorem isTwoLocal_map {G H : Type*} [Group G] [Group H]
    (f : G ≃* H) {M : Subgroup G} (hM : IsTwoLocal M) :
    IsTwoLocal (M.map f.toMonoidHom) := by
  obtain ⟨Q, hQ, hp, rfl⟩ := hM
  refine ⟨Q.map f.toMonoidHom, ?_, hp.map f.toMonoidHom, ?_⟩
  · exact fun h => hQ ((Subgroup.map_eq_bot_iff_of_injective Q f.injective).mp h)
  · exact Subgroup.map_equiv_normalizer_eq Q f

/-- The automorphism specialization, with the subgroup hypothesis first. -/
public theorem isTwoLocal_map_aut {G : Type*} [Group G]
    {M : Subgroup G} (hM : IsTwoLocal M) (e : MulAut G) :
    IsTwoLocal (M.map e.toMonoidHom) :=
  isTwoLocal_map e hM

end Theory.GroupTheory
