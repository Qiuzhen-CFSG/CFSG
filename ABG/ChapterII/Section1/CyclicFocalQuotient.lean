module

public import FeitThompson.BGsection1.theorem_1_17
public import Theory.GroupTheory.PGroup.CyclicAbelianization

/-!
# Cyclic p-group quotients from a cyclic focal quotient

If the quotient of a Sylow p-subgroup by its focal subgroup is cyclic,
then every p-group quotient of the finite ambient group is cyclic. This
supplies the normal-subgroup step in ABG Chapter II, Section 1, Proposition 2,
article page 13: in the Q and D cases the relevant focal quotient is cyclic.

The chosen Sylow subgroup maps onto any p-group quotient and then onto
its abelianization. This composite annihilates the focal subgroup, which
lies in the ambient commutator subgroup. Thus the abelianization is an image
of the cyclic focal quotient. A finite p-group with cyclic abelianization
is cyclic by the Frattini nongeneration theorem.
-/

namespace ABG

/-- Cyclicity of the focal quotient forces every p-group quotient to be cyclic. -/
public theorem isCyclic_quotient_of_cyclic_focal_quotient
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) [IsCyclic (P ⧸ (P : Subgroup G).focalSubgroupOf)]
    (N : Subgroup G) [N.Normal] (hQ : IsPGroup p (G ⧸ N)) : IsCyclic (G ⧸ N) := by
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let R := P.mapSurjective (f := q) (QuotientGroup.mk'_surjective N)
  have hR : (R : Subgroup (G ⧸ N)) = ⊤ :=
    (R.is_maximal' (hQ.to_subgroup ⊤) le_top).symm
  have hqP : Function.Surjective (q.comp (P : Subgroup G).subtype) := by
    intro x
    have hx : x ∈ (R : Subgroup (G ⧸ N)) := hR ▸ Subgroup.mem_top x
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨⟨y, hy⟩, rfl⟩
  let a := (Abelianization.of (G := G ⧸ N)).comp q
  let f := a.comp (P : Subgroup G).subtype
  have hf : Function.Surjective f :=
    (QuotientGroup.mk'_surjective _).comp hqP
  have hker : (P : Subgroup G).focalSubgroupOf ≤ f.ker := by
    intro x hx
    exact Abelianization.commutator_subset_ker a
      ((P : Subgroup G).focalSubgroup_le_commutator hx)
  let l := QuotientGroup.lift (P : Subgroup G).focalSubgroupOf f hker
  have hl : Function.Surjective l := by
    intro x
    obtain ⟨y, rfl⟩ := hf x
    exact ⟨QuotientGroup.mk' _ y, rfl⟩
  let : IsCyclic ((G ⧸ N) ⧸ commutator (G ⧸ N)) := isCyclic_of_surjective l hl
  exact hQ.isCyclic_of_cyclic_abelianization

end ABG
