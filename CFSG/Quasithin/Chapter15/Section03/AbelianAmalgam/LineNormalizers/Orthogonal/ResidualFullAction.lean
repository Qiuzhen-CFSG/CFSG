module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Orthogonal.Residual

/-!
# Full action of the residual line product

For a totally singular four-subgroup `E`, the compatible natural action
makes `M_E` induce all six automorphisms of `E`. The image of the chosen
Sylow subgroup of `M_E` is therefore Sylow in `Aut(E)` and has even order;
its prescribed ambient image is the actual `T_E`.

The residual `Y_E` has nontrivial action on `E`: otherwise faithfulness of
the coordinate residual on the line would make it centralize all of `V`,
contradicting `V=[V,Y_E]`. Its cubic action supplies the factor three.
Thus the action image of `Y_E T_E` has order divisible by six and equals
`Aut(E)`. All images are taken through the actual conjugation maps.

The only residual input is the earlier image identity from 15.3.7.
The final specialization uses the genuine `Y = residualY M Mc`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.2, 15.3.7 and 15.3.66(5)–(6), printed pp.1121–1122 and 1152,
PDF pp.1138–1139 and 1169.
-/

public section

open Subgroup OrthogonalFourBinary OrthogonalFourBinary.TerminalLines
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Orthogonal
open GoldschmidtCore.LocalRelations GoldschmidtCore.LocalRelations.OrthogonalProducts
variable {G : Type*} [Group G] [Finite G] {V M : Subgroup G}

private theorem lineY_not_le_centralizer (d : NaturalAction V M) (Y E : Subgroup G)
    (hYM : Y ≤ M) (hEV : E ≤ V) (hcard : Nat.card E = 4)
    (hs : ∀ e : E, d.singular ⟨e, hEV e.property⟩)
    (himage : actionImage d Y = pResidual 2 IsometryGroup) :
    ¬ lineY Y E ≤ centralizer (E : Set G) := by
  intro hcentral
  have hc : lineY Y E ≤ centralizer (V : Set G) := by
    intro y hy
    exact ((lineY_centralizer_line_eq_module d Y E hYM hEV hcard hs himage).le
      ⟨hy, hcentral hy⟩).2
  have hV : V = ⊥ := by
    rw [lineY_commutator d Y E hYM hEV hcard hs himage, commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hc
  have hE : E = ⊥ := le_bot_iff.mp (hEV.trans_eq hV)
  simp [hE] at hcard

/-- The residual line product induces every automorphism of the singular line.
The supplied Sylow witness identifies its two-factor with the actual `T_E`. -/
theorem lineProduct_full_action_of_residual_image (d : NaturalAction V M) (Y T E : Subgroup G)
    (hYM : Y ≤ M) (hEV : E ≤ V) (hcard : Nat.card E = 4)
    (hs : ∀ e : E, d.singular ⟨e, hEV e.property⟩)
    (himage : actionImage d Y = pResidual 2 IsometryGroup)
    (P : Sylow 2 (lineM M E))
    (hP : (P : Subgroup (lineM M E)).map (lineM M E).subtype = lineT T E) :
    Function.Surjective
      (lineAction E (lineY Y E ⊔ lineT T E) (lineProduct_le_normalizer Y T E)) := by
  let := singularLine_isKleinFour d E hEV hcard hs
  let A := lineY Y E ⊔ lineT T E
  let f := lineAction E A (lineProduct_le_normalizer Y T E)
  have hthree : 3 ∣ Nat.card f.range := by
    obtain ⟨y, hy, hny⟩ := SetLike.not_le_iff_exists.mp
      (lineY_not_le_centralizer d Y E hYM hEV hcard hs himage)
    let a : A := ⟨y, mem_sup_left hy⟩
    let b : f.range := ⟨f a, ⟨a, rfl⟩⟩
    have hne : b ≠ 1 := by
      intro hb
      apply hny
      have hk : a ∈ f.ker := congrArg Subtype.val hb
      rw [lineAction_ker] at hk
      exact hk
    have hcube : b ^ 3 = 1 := by
      apply Subtype.ext
      change f a ^ 3 = 1
      rw [← map_pow]
      change a ^ 3 ∈ f.ker
      rw [lineAction_ker]
      exact centralizer_le hEV (lineY_cube_centralizes_module d Y E hYM hEV himage y hy)
    exact (orderOf_eq_prime hcube hne) ▸ orderOf_dvd_natCard b
  let Q : Sylow 2 (MulAut E) := P.mapSurjective (lineM_full_action d E hEV hcard hs)
  have hQ : (Q : Subgroup (MulAut E)) ≤ f.range := by
    rintro u ⟨m, hm, rfl⟩
    have hmT : (m : G) ∈ lineT T E := by
      rw [← hP]
      exact mem_map_of_mem _ hm
    exact ⟨⟨m, mem_sup_right hmT⟩, rfl⟩
  have htwo : 2 ∣ Nat.card f.range :=
    (Q.dvd_card_of_dvd_card (by rw [IsKleinFour.card_mulAut]; decide)).trans
      (card_dvd_of_le hQ)
  have hsix : 6 ∣ Nat.card f.range :=
    (by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd htwo hthree
  have heq : Nat.card f.range = Nat.card (MulAut E) := by
    apply Nat.dvd_antisymm f.range.card_subgroup_dvd_card
    simpa only [IsKleinFour.card_mulAut] using hsix
  exact MonoidHom.range_eq_top.mp (f.range.eq_top_of_card_eq heq)

/-- The full action in source 15.3.66 for the genuine residual from 15.3.7.
The Sylow witness is the one supplied by the preceding selection of `E`. -/
theorem residualY_lineProduct_full_action (d : NaturalAction V M)
    (Mc : Subgroup G) (T : Sylow 2 G) (E : Subgroup G)
    (hEV : E ≤ V) (hcard : Nat.card E = 4)
    (hs : ∀ e : E, d.singular ⟨e, hEV e.property⟩)
    (himage : actionImage d (residualY M Mc) = pResidual 2 IsometryGroup)
    (P : Sylow 2 (lineM M E))
    (hP : (P : Subgroup (lineM M E)).map (lineM M E).subtype = lineT T E) :
    Function.Surjective
      (lineAction E (lineY (residualY M Mc) E ⊔ lineT T E)
        (lineProduct_le_normalizer (residualY M Mc) T E)) :=
  lineProduct_full_action_of_residual_image d (residualY M Mc) T E
    (Chapter14.SourcePreliminaries.sourceResidual_le M Mc) hEV hcard hs himage P hP

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Orthogonal
