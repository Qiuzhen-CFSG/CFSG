module
public import Stellmacher.DirectProductMap
public import Stellmacher.SectionTwo.SL2CoordinateContainerResidual
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.ResidualLift

/-!
# Image and residual of a selected coordinate lift

Let E be a normal subgroup of a finite group X, generated internally by
SL₂(2) factors D, and let T be an ambient Sylow two-subgroup. Suppose the
image of K consists of one whole factor and the Sylow lines in all other
factors, while the image of B is T ∩ E. Then the image of K is the selected
factor joined with the image of B. The image of O²(K) is exactly the
ambient image of the derived subgroup of that same raw factor.

Map the original family from E into X and apply the indexed Sylow-coordinate
theorem. The selected Sylow line is already in the selected whole factor,
so adjoining the other lines is equivalent to adjoining T ∩ E. Residual
functoriality and the coordinate-container residual theorem identify O²(K);
commutator functoriality expresses the answer on the original factor in E.

This keeps the factor family used in the quotient action unchanged and
supplies the two image hypotheses of omega_coordinate_module. Its caller
is the selected natural-module step in Stellmacher (6.3), using (2.2),
journal pp.20 and 31; source: refs/latex/stellmacher-n-group.tex.
-/

namespace Stellmacher.SectionTwo
universe u

public theorem selected_coordinate_image_and_residual
    {G X : Type u} [Group G] [Finite G] [Group X] [Finite X]
    (q : G →* X) (T : Sylow 2 X) (E : Subgroup X) (hEnormal : E.Normal)
    {n : ℕ} (D : Fin n → Subgroup E)
    (hprod : IsInternalDirectProductFamily ⊤ D) (hSL : ∀ j, IsSL2Two (D j))
    (B K : Subgroup G) (i : Fin n)
    (hB : B.map q = (T : Subgroup X) ⊓ E)
    (hK : K.map q = (D i).map E.subtype ⊔
      ⨆ j : {j : Fin n // j ≠ i}, (T : Subgroup X) ⊓ (D j).map E.subtype) :
    K.map q = (D i).map E.subtype ⊔ B.map q ∧
      (twoResidualAmbient K).map q =
        ((commutator (D i)).map (D i).subtype).map E.subtype := by
  let F (j : Fin n) := (D j).map E.subtype
  have hprodF : IsInternalDirectProductFamily E F := by
    have hp := hprod.map_injective E.subtype E.subtype_injective
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at hp
    exact hp
  have hSLF (j : Fin n) : IsSL2Two (F j) := by
    obtain ⟨e⟩ := hSL j
    exact ⟨(Subgroup.equivMapOfInjective (D j) E.subtype E.subtype_injective).symm.trans e⟩
  have hcoord := SectionOne.sl2_family_sylow_coordinates T E hEnormal F hprodF hSLF
  constructor
  · rw [hK, hB]
    change F i ⊔ (⨆ j : {j : Fin n // j ≠ i}, (T : Subgroup X) ⊓ F j.val) =
      F i ⊔ ((T : Subgroup X) ⊓ E)
    apply le_antisymm
    · apply sup_le le_sup_left
      apply iSup_le
      intro j
      exact (le_inf inf_le_left (inf_le_right.trans (Subgroup.map_subtype_le _))).trans
        le_sup_right
    · apply sup_le le_sup_left
      rw [hcoord.1]
      apply iSup_le
      intro j
      by_cases hji : j = i
      · subst j
        exact inf_le_right.trans le_sup_left
      · exact (le_iSup (fun j : {j : Fin n // j ≠ i} =>
          (T : Subgroup X) ⊓ F j.val) ⟨j, hji⟩).trans le_sup_right
  · rw [map_twoResidualAmbient_of_subgroup_image K q _ hK]
    have hr := twoResidual_coordinate_container T E hEnormal F hprodF hSLF i
    simpa only [F, Subgroup.map_subtype_commutator, Subgroup.map_commutator] using hr

end Stellmacher.SectionTwo

