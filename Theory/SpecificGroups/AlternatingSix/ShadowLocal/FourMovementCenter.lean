module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.SylowGeometry

/-!
# Four-group movement forces the source center into the inner center line

In the full automorphism Sylow model, the centralizer of the inner D₈ is
an elementary four-group. Either of its noncentral elements has centralizer
the natural subgroup, which is also the normalizer of each inner four-group.
Thus a subgroup containing D₈ and moving one of its four-groups has no
extra central element. This retains the diagram-movement hypothesis used
in Aschbacher--Smith 2.5.8(4), printed pp.556--557.
-/

public section
open Subgroup
namespace AlternatingSix.ShadowLocal
open Identification SylowGeometry

/-- The actual source subgroup has exactly the full Sylow center when it
contains the inner Sylow and moves one of its elementary four-groups. -/
theorem center_image_eq_of_four_movement (P : Sylow 2 AutA6)
    (A E : Subgroup P) [IsKleinFour E] (hDA : sylowInner P ≤ A)
    (hED : E ≤ sylowInner P)
    (hmove : ∃ g ∈ A, E.map (MulAut.conj g).toMonoidHom ≠ E) :
    (center A).map A.subtype = center P := by
  have hZD : center P ≤ sylowInner P := by
    rw [center_eq]
    apply zpowers_le.mpr
    rw [← sylowEquiv_innerD P]
    apply mem_map_of_mem
    rw [show 4 = 2 * 2 from rfl, pow_mul]
    exact Subgroup.pow_mem _ (subset_closure (by simp)) _
  apply le_antisymm
  · rintro u ⟨u, hu, rfl⟩
    have huc : (u : P) ∈ centralizer (sylowInner P : Set P) := by
      intro d hd
      exact congrArg Subtype.val (mem_center_iff.mp hu (⟨d, hDA hd⟩ : A))
    by_contra huz
    have htwo : (u : P) ^ 2 = 1 := by
      let e := centralizerInnerEquiv P
      have hexp : Monoid.exponent (centralizer (sylowInner P : Set P)) = 2 :=
        (Monoid.exponent_eq_of_mulEquiv e).trans IsKleinFour.exponent_two
      have hh := Monoid.pow_exponent_eq_one (⟨u, huc⟩ : centralizer (sylowInner P : Set P))
      rw [hexp] at hh
      exact congrArg Subtype.val hh
    obtain ⟨g, hg, hmove⟩ := hmove
    have hgu : g ∈ centralizer ({(u : P)} : Set P) := by
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (mem_center_iff.mp hu (⟨g, hg⟩ : A))
    rw [centralizer_innerCentralizer_involution P u huc huz htwo,
      centralizer_transposition] at hgu
    have hnorm : normalizer (E : Set P) = sylowNatural P := by
      rcases kleinFour_subgroups_inner P E hED with rfl | rfl
      · exact normalizer_kleinZero P
      · exact normalizer_kleinOne P
    exact hmove (mem_normalizer_iff_map_conj_eq.mp (hnorm ▸ hgu))
  · intro z hz
    refine ⟨⟨z, hDA (hZD hz)⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro a
    exact Subtype.ext (mem_center_iff.mp hz a)

/-- In particular the source center consists of inner automorphisms. -/
theorem center_image_le_inner_of_four_movement (P : Sylow 2 AutA6)
    (A E : Subgroup P) [IsKleinFour E] (hDA : sylowInner P ≤ A)
    (hED : E ≤ sylowInner P)
    (hmove : ∃ g ∈ A, E.map (MulAut.conj g).toMonoidHom ≠ E) :
    (center A).map A.subtype ≤ sylowInner P := by
  rw [center_image_eq_of_four_movement P A E hDA hED hmove, center_eq]
  apply zpowers_le.mpr
  rw [← sylowEquiv_innerD P]
  apply mem_map_of_mem
  rw [show 4 = 2 * 2 from rfl, pow_mul]
  exact Subgroup.pow_mem _ (subset_closure (by simp)) _

end AlternatingSix.ShadowLocal
