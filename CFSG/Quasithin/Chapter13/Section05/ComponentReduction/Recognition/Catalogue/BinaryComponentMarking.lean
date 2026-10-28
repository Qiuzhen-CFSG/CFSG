module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.BinaryComponentGroups

/-!
# The original outer A₆ actor

Containment of V* in K* would pass through the literal star map to containment
of V̂ in K̂. Condition(ii) of the actual source configuration excludes that
containment in the A₆ row. Consequently the original component is proper in
its actor, as required by the natural A₆ module recognizer.

Source: Aschbacher–Smith13.5.21, printed p.924.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue
open Section08.Source
open CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration
variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G} {K : Subgroup G}
  (s : Selected D K) (h : D.Hypothesis) [(componentCentralizer s h).Normal]

/-- Containment of the original star actors passes to the original centralizer quotient. -/
theorem marked_actor_le_of_star_actor_le
    (hv : starImage D.H D.V ≤ starImage D.H K) : Vhat s h ≤ Khat s h := by
  rintro _ ⟨x,hxV,rfl⟩
  have hxstar : starHom s h x ∈ starImage D.H D.V :=
    mem_map_of_mem _ (show inclusion (s.X_le_H h) x ∈ D.V.subgroupOf D.H from hxV)
  obtain ⟨b,hb,he⟩ := hv hxstar
  let y : X D K := ⟨b.val,(show K ≤ X D K from le_sup_left) hb⟩
  have hy : starHom s h y = starHom s h x := he
  have hxy : x⁻¹ * y ∈ componentCentralizer s h := by
    change starHom s h (x⁻¹*y) ∈ centralizer (starImage D.H K : Set (Hstar D.H))
    rw [map_mul,map_inv,hy,inv_mul_cancel]
    exact one_mem _
  have hq : QuotientGroup.mk' (componentCentralizer s h) x =
      QuotientGroup.mk' (componentCentralizer s h) y := QuotientGroup.eq.mpr hxy
  rw [hq]
  exact mem_map_of_mem _ hb

/-- In the original A₆ branch the source involution lies outside the star component. -/
theorem source_six_star_actor_not_le
    (c : SourceConfiguration s h D.L₁ le_rfl)
    (e : starImage D.H K ≃* alternatingGroup (Fin 6)) :
    ¬ starImage D.H D.V ≤ starImage D.H K := by
  let q := (KhatEquiv s h).trans
    ((Representation.TripleSixOuterDisplacement.centralQuotientEquiv e).trans
      ((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 6)))).trans
        QuotientGroup.quotientBot))
  exact fun hv => LocalModels.source_six_actor_not_le s h D.L₁ c.proved_prefix
    c.condition_ii_O23 q (marked_actor_le_of_star_actor_le s h hv)

/-- The literal component is proper in the actor for the A₆ natural-action branch. -/
theorem source_six_component_ne_top
    (c : SourceConfiguration s h D.L₁ le_rfl)
    (e : component D K ≃* alternatingGroup (Fin 6)) : component D K ≠ ⊤ := by
  intro ht
  apply source_six_star_actor_not_le s h c (TripleSix.componentEquiv.symm.trans e)
  intro v hv
  let a : actor D K := ⟨v,(show starImage D.H D.V ≤ actor D K from le_sup_right) hv⟩
  exact (show a ∈ component D K from ht.symm ▸ mem_top a)
end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue
