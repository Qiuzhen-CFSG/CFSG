module

public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Even.Inner
public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary
public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.NormalizedBlocks
public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.NormalizedBlocks.PairSplitting
public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.NormalizedBlocks.QuartetSplitting
public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.TailRelations
public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.Source

/-!
# The ordinary Ree branch of the marked involution classification

All four additive blocks split in a central cover. For m>=2 the actual
Suzuki Levi has trivial covering kernel, so all four nonabelian blocks split
as well. The simultaneous torus normalization and proved tail relations give
a section of the literal unipotent subgroup. Its odd index eliminates the
entire two-primary covering kernel. This is exactly the part needed by the
original marked involution, whose innerness makes its center a two-group.

The field-eight case m=1 is discharged by the ambient class-two calculation
inside the actual perfect Suzuki-side seed, retaining its literal root maps.
Source: Aschbacher--Smith 1.1.5(3)(a), printed pp.501--503, and I.1.3.
-/

public section
open Subgroup Theory.GroupTheory PerfectCentralCovering
namespace CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
open Chapter15.Section03.Candidates.ComponentStructure ClassificationModels
variable {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
  {α : MulAut L} {P : Sylow 2 L}

/-- The two-primary kernel exclusion at ordinary Ree parameters, using
only actual local sections and their projection triangles. -/
theorem ree_cover_not_two_dvd_kernel {m : ℕ} (hm : 2 ≤ m)
    {E : Type*} [Group E] [Finite E] (c : Cover E (ReeF4.Model m)) :
    ¬ 2 ∣ Nat.card c.toMonoidHom.ker := by
  apply ReeF4.CentralCovers.not_two_dvd_kernel_of_prime_unipotent_sections m _ c
  intro F _ _ d hd
  obtain ⟨L, hL⟩ :=
    ReeF4.CentralCovers.TwoPrimary.exists_torusEquivariant_of_pair_and_quartet_sections m d hd
      (ReeF4.CentralCovers.TwoPrimary.PairSplitting.exists_pair_sections m (by omega) d hd)
      (ReeF4.CentralCovers.TwoPrimary.QuartetSplitting.quartet_sections_of_two_le m hm
        d.toMonoidHom d.surjective d.ker_le_center)
  exact ReeF4.CentralCovers.TwoPrimary.unipotent_section_of_torusEquivariant m (by omega) d L hL

/-- Every ordinary Ree source model gives the full action on the original group. -/
theorem MarkedInvolution.ree_source_of_two_le (d : MarkedInvolution α P)
    {m : ℕ} (hm : 2 ≤ m) (e : L ⧸ center L ≃* ReeF4.Model m) : ModelAction115 L α := by
  have hi := d.ree_inner (by omega : 1 ≤ m) e
  apply d.lie_of_center_eq_bot (.inr (.inl (.ree m (by omega)
    ((ReeF4.exists_localBlockInput_mulEquiv_iff _ m).mpr ⟨e⟩)))) hi
  have hz := MulAut.center_eq_twoCore_of_inner_inverts_oddCore α hi d.inverts_odd_core
  have hp : IsPGroup 2 (center L) := hz ▸ pCore_isPGroup
  have hn := ree_cover_not_two_dvd_kernel hm (centralQuotientCover e)
  rw [centralQuotientCover_ker] at hn
  rcases hp.card_eq_or_dvd with hc | hc
  · exact Subgroup.card_eq_one.mp hc
  · exact False.elim (hn hc)


/-- The ambient field-eight calculation completes the two-primary exclusion
for the full positive Ree parameter range. -/
theorem ree_cover_not_two_dvd_kernel_of_one_le {m : ℕ} (hm : 1 ≤ m)
    {E : Type*} [Group E] [Finite E] (c : Cover E (ReeF4.Model m)) :
    ¬ 2 ∣ Nat.card c.toMonoidHom.ker :=
  ReeF4.CentralCovers.TwoPrimary.not_two_dvd_kernel m hm c

/-- Every Ree source model, including field eight, gives the full action
on the original marked quasisimple group. -/
theorem MarkedInvolution.ree_source (d : MarkedInvolution α P)
    {m : ℕ} (hm : 1 ≤ m) (e : L ⧸ center L ≃* ReeF4.Model m) : ModelAction115 L α := by
  have hi := d.ree_inner hm e
  apply d.lie_of_center_eq_bot (.inr (.inl (.ree m hm
    ((ReeF4.exists_localBlockInput_mulEquiv_iff _ m).mpr ⟨e⟩)))) hi
  have hz := MulAut.center_eq_twoCore_of_inner_inverts_oddCore α hi d.inverts_odd_core
  have hp : IsPGroup 2 (center L) := hz ▸ pCore_isPGroup
  have hn := ree_cover_not_two_dvd_kernel_of_one_le hm (centralQuotientCover e)
  rw [centralQuotientCover_ker] at hn
  rcases hp.card_eq_or_dvd with hc | hc
  · exact Subgroup.card_eq_one.mp hc
  · exact False.elim (hn hc)

end CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
