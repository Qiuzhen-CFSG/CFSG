module

public import Theory.Frattini.PGroup

/-!
# Finite p-groups with cyclic abelianization

A finite p-group whose abelianization is cyclic is itself cyclic. Lift a
generator of the abelianization: its cyclic subgroup joins the commutator
subgroup to the whole group. Since the commutator subgroup lies in the
Frattini subgroup, the Frattini nongeneration theorem shows that the lifted
element generates the group.

This standard p-group fact supports the transfer argument in
Alperin--Brauer--Gorenstein, Chapter II, Section 1, Proposition 2, where cyclic
focal quotients control p-group quotients and the resulting normal subgroup.
-/

namespace IsPGroup

/-- A finite p-group with cyclic abelianization is cyclic. -/
public theorem isCyclic_of_cyclic_abelianization {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G)
    [IsCyclic (G ⧸ commutator G)] : IsCyclic G := by
  let : Fact (IsPGroup p G) := ⟨hG⟩
  obtain ⟨q, hq⟩ := isCyclic_iff_exists_zpowers_eq_top.mp
    (inferInstance : IsCyclic (G ⧸ commutator G))
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (commutator G) q
  have hmap : (Subgroup.zpowers x).map (QuotientGroup.mk' (commutator G)) = ⊤ := by
    simpa using hq
  have hsup : Subgroup.zpowers x ⊔ commutator G = ⊤ := by
    simpa only [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] using
      congrArg (Subgroup.comap (QuotientGroup.mk' (commutator G))) hmap
  apply isCyclic_iff_exists_zpowers_eq_top.mpr
  refine ⟨x, frattini_nongenerating (G := G) ?_⟩
  apply top_unique
  rw [← hsup]
  exact sup_le_sup_left (commutator_le_frattini_of_isPGroup (p := p)) _

end IsPGroup
