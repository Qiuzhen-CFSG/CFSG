module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Ree.TitsMarked
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.Local
public import Theory.SpecificGroups.Tits.RelativeSylowMarking

/-!
# A projection-compatible Tits marking

The component meets the supplied Sylow subgroup in a Sylow two-subgroup.
The literal inner action gives a unique nonidentity involution projection,
which centralizes and belongs to that intersection. Sylow conjugacy aligns
the intersection with the certified Atlas Sylow subgroup; its unique central
involution is r5. Thus the marking retains the actual supplied Sylow subgroup
and sends the projection to r5, without assuming two-centrality separately.

Source: Aschbacher–Smith 1.1.5(3)(a), pp.501–502, and the local setup for
2.3.9(7), pp.525–526; Parrott (1972), §5, for the marked Tits Sylow subgroup.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Ree
open Subgroup
variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- Construct both the Sylow marking and the literal projected involution. -/
theorem tits_exists_compatible_sylow_marking
    (h : LocalSetup H L M S z) (e : L ≃* Tits.ParrottGroup)
    (α : MulAut L) (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (hinner : α ∈ (MulAut.conj (G := L)).range) :
    ∃ (e' : L ≃* Tits.ParrottGroup) (t : L),
      IsConjugationProjection L z t ∧ orderOf t = 2 ∧
      titsAtlasEquiv e' t = Tits.atlas1600R5 ∧
      (((S : Subgroup H).map H.subtype).subgroupOf L).map
        (titsAtlasEquiv e').toMonoidHom = Tits.atlas1600SylowTwoSubgroup := by
  obtain ⟨t, ht, _⟩ := h.exists_unique_projection
    (Tits.RelativeSylowMarking.center_eq_bot (titsAtlasEquiv e)) α hα hinner
  obtain ⟨R, hR⟩ := h.component_sylow
  obtain ⟨f, hf⟩ := Tits.RelativeSylowMarking.exists_sylow_marking (titsAtlasEquiv e) R
  let e' := f.trans Tits.parrottFiniteImageEquiv.symm
  have he' : titsAtlasEquiv e' = f := by
    ext x
    exact Tits.parrottFiniteImageEquiv.apply_symm_apply (f x)
  refine ⟨e', t, ht.1, ht.2, ?_, ?_⟩
  · rw [he']
    apply Tits.RelativeSylowMarking.image_eq_r5_of_sylow_center f R hf
      (h.projection_mem_sylow ht.1 ht.2 R hR)
      (h.projection_centralizes_sylow ht.1 R hR)
    intro he
    rw [he, orderOf_one] at ht
    exact (by decide : (1 : ℕ) ≠ 2) ht.2
  · rwa [he', ← hR]

/-- Express the projection by the inverse image of the distinguished word. -/
theorem tits_projection_of_marked_image
    (e : L ≃* Tits.ParrottGroup) {t : L}
    (ht : IsConjugationProjection L z t)
    (he : titsAtlasEquiv e t = Tits.atlas1600R5) :
    IsConjugationProjection L z ((titsAtlasEquiv e).symm Tits.atlas1600R5) := by
  rwa [← he, MulEquiv.symm_apply_apply]

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Ree

end
