module

public import CFSG.Quasithin.MainConverse.ReeSections.MaximalCover.Structure
public import CFSG.Quasithin.MainConverse.ReeSections.MaximalCover.Envelope

/-!
# Assembly of structural envelopes for Ree maximal subgroups

Each group on the coarsened Malle list has an envelope: remove the two-group
radical of a parabolic using its Levi map, remove the central and determinant
layers of the unitary groups, use the two Suzuki factors in the wreath product,
and keep the proper Ree subfield as a recursive leaf. Relative normality and
all projective maps are explicit in these proofs.

The final theorem here is conditional. `MalleMaximalAlternatives` still requires
an exhaustive structural classification for the genuine exceptional fixed-point
group; `ParabolicProjections` still requires its two concrete Levi maps with
two-group kernels. Neither input assumes ambient simplicity, known-simple
sections, or the desired envelope conclusion. The task owning this module retains
the obligation to discharge both before exporting an unconditional maximal cover.

Source: Malle, *The maximal subgroups of ²F₄(q²)*, J. Algebra 139 (1991),
52–69, DOI 10.1016/0021-8693(91)90283-E; the list in the proof of Theorem 5
of Himstedt–Nguyen–Tiep, arXiv:0910.4758, pp.2–3. Here `q = 2^(2*m+1)`.
-/

public section

namespace CFSG.Quasithin.MainConverse.ReeSections

open Matrix BenderSuzuki.MatrixGroups

/-- The root-defined full parabolics have envelopes once their Levi maps with
finite two-group kernels have been constructed. -/
theorem envelope_parabolic_of_projections (hπ : ParabolicProjections)
    {m : ℕ} (hm : 1 ≤ m) (s : ReeF4.LargeLocalSeeds.Side) :
    Envelope m (ReeF4.ConverseParabolics.parabolic m s) := by
  obtain ⟨hlinear, hsuzuki⟩ := hπ m hm
  cases s with
  | linear =>
      obtain ⟨π, hπ⟩ := hlinear
      exact Envelope.linearParabolic π hπ
  | suzuki =>
      obtain ⟨π, hπ⟩ := hsuzuki
      exact Envelope.suzukiParabolic hm π hπ

/-- Interpret the structures on Malle's list through their actual normal
layers and projective matrix maps. Exhaustion is a separate input. -/
theorem MaximalAlternative.envelope {m : ℕ} (hm : 1 ≤ m)
    {H : Type} [Group H] (h : MaximalAlternative m H)
    (hparabolic : ∀ s, Envelope m (ReeF4.ConverseParabolics.parabolic m s)) :
    Envelope m H := by
  cases h with
  | parabolic s e => exact (hparabolic s).of_mulEquiv e
  | torusNormalizer hH => exact .solvable _ hH
  | specialUnitary F J hcard hconj N e hindex =>
      have hPSU : Envelope m (ProjectiveSpecialUnitaryMatrixGroup J) :=
        .unitaryThree _ ⟨F, inferInstance, inferInstance, J, hcard, hconj,
          ⟨MulEquiv.refl _⟩⟩
      exact Envelope.of_index_two N ((hPSU.specialUnitary J).of_mulEquiv e) hindex
  | projectiveUnitary F J hcard hconj N e hindex =>
      have hPSU : Envelope m (ProjectiveSpecialUnitaryMatrixGroup J) :=
        .unitaryThree _ ⟨F, inferInstance, inferInstance, J, hcard, hconj,
          ⟨MulEquiv.refl _⟩⟩
      exact Envelope.of_index_two N ((hPSU.projectiveUnitary J).of_mulEquiv e) hindex
  | suzukiWreath N e hindex =>
      exact Envelope.of_index_two N
        (((Envelope.suzuki m hm).prod (.suzuki m hm)).of_mulEquiv e) hindex
  | symplectic F hcard N e hindex =>
      exact Envelope.of_index_two N ((Envelope.symplectic F hcard).of_mulEquiv e) hindex
  | subfield k hlt hdiv _ e => exact (Envelope.reeSubfield k hlt hdiv).of_mulEquiv e

/-- Conditional assembly of the maximal-subgroup envelope theorem. Both
intrinsic Ree inputs still have to be proved for every positive parameter. -/
theorem maximalSubgroupCover_of_malle_and_parabolic_projections
    (hMalle : MalleMaximalAlternatives) (hπ : ParabolicProjections) :
    MaximalSubgroupCover := by
  intro m hm M hM
  exact (hMalle m hm M hM).envelope hm (envelope_parabolic_of_projections hπ hm)

end CFSG.Quasithin.MainConverse.ReeSections
