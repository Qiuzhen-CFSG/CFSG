module
public import Theory.GroupTheory.Recognition.QuasithinM23.SylowPlanes

/-!
# Conjugating a full elementary plane inside the original edge group

If a Sylow two-subgroup has exactly two elementary subgroups of order sixteen,
and one is normalized by the whole edge group, every other elementary sixteen
subgroup is conjugate inside that edge group to the second plane. Sylow conjugacy
puts the subgroup in the specified Sylow; invariance excludes the first plane.

Source: Aschbacher--Smith 5.2.20(5), printed p.656. This supplies the core-placement
step without an abstract change of either original subgroup embedding.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace Theory.GroupTheory.QuasithinM23
variable {G : Type*} [Group G] [Finite G]

theorem conjugate_elementary_of_two_planes
    (L S N U Q : Subgroup G) (P : Sylow 2 L)
    (hP : (P : Subgroup L).map L.subtype = S)
    (hN : L ≤ normalizer (N : Set G))
    (hall : ∀ E : Subgroup G, IsElementaryAbelian 2 E → E ≤ S →
      Nat.card E = 16 → E = N ∨ E = U)
    [IsElementaryAbelian 2 Q] (hQL : Q ≤ L) (hcQ : Nat.card Q = 16)
    (hne : Q ≠ N) :
    ∃ g : L, Q.map (MulAut.conj (g : G)).toMonoidHom = U := by
  have hq : IsPGroup 2 (Q.subgroupOf L) :=
    (IsElementaryAbelian.isPGroup 2 Q).comap_subtype
  obtain ⟨R,hR⟩ := hq.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq L R P
  have hgP := congrArg Sylow.toSubgroup hg
  change (R : Subgroup L).map (MulAut.conj g).toMonoidHom = P at hgP
  let E := Q.map (MulAut.conj (g : G)).toMonoidHom
  have hES : E ≤ S := by
    rintro _ ⟨q,hq,rfl⟩
    rw [←hP]
    refine ⟨g * ⟨q,hQL hq⟩ * g⁻¹,?_,rfl⟩
    rw [←hgP]
    exact mem_map_of_mem _ (hR hq)
  have hcE : Nat.card E = 16 :=
    (card_map_of_injective (MulAut.conj (g : G)).injective).trans hcQ
  rcases hall E (IsElementaryAbelian.map _) hES hcE with hh | hh
  · have hn := mem_normalizer_iff_map_conj_eq.mp (hN g.property)
    exact (hne (map_injective (MulAut.conj (g : G)).injective (hh.trans hn.symm))).elim
  · exact ⟨g,hh⟩
end Theory.GroupTheory.QuasithinM23
