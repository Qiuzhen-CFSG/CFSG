module
public import Theory.SpecificGroups.ExceptionalOuterDisplacements.HS.Outer.Automorphisms
public import Theory.SpecificGroups.ExceptionalOuterDisplacements.HS.Outer.PermutationFusion
public import Theory.SpecificGroups.ExceptionalOuterDisplacements.HS.Center
public import Theory.SpecificGroups.ExceptionalOuterDisplacements.HS.Witnesses

/-!
# Non-two-central displacements for every outer HS involution

Both concrete outer representatives have short carrier words whose
displacements are fixed-point-free involutions. Every two-central HS element
fixes a point, by the checked Sylow enumeration and Sylow conjugacy, so these
are non-two-central displacements. The full abstract-automorphism equivalence
and exhaustive two-class permutation fusion transport the witnesses to every
outer involution on the literal ATLAS degree-100 carrier.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, I.2.2,
observation (iii), printed p.411 / PDF p.422. This proves the HS displacement
input; the central-cover lifting clauses and four-model assembly are separate.
No covering conclusion, full-centralizer identification, or two-central
marked witness is used. The original ATLAS HSG1-p100B0 attribution and license
are retained in LICENSES/ATLAS.txt and the carrier source directory.
-/

public section
namespace Theory.SpecificGroups.ExceptionalOuterDisplacements.HS
open Subgroup Theory.GroupTheory.DoubleCoverCentralizer
open Sporadic.LeechRelated.HS Outer Witnesses

/-- The two actual outer representatives have non-two-central involution displacements. -/
theorem representative_displacement (i : Fin 2) :
    HasNonTwoCentralDisplacement (generated.normalizerMonoidHom (actor i)) := by
  refine ⟨witness i, displacement_order i, ?_⟩
  intro hc
  obtain ⟨p, hp⟩ := twoCentral_has_fixed_point (displacement i) hc
  exact fixed_point_free i p hp

private theorem displacement_of_conjugate (n g : PermutationNormalizer) (i : Fin 2)
    (hn : n.val = g.val * (actor i).val * g.val⁻¹) :
    HasNonTwoCentralDisplacement (generated.normalizerMonoidHom n) := by
  have hn' : n = g * actor i * g⁻¹ := Subtype.ext hn
  have he : MulAut.congr (generated.normalizerMonoidHom g)
      (generated.normalizerMonoidHom (actor i)) = generated.normalizerMonoidHom n := by
    rw [hn', map_mul, map_mul, map_inv]
    ext x
    simp [MulAut.congr_apply]
  rw [← he]
  exact (representative_displacement i).map (generated.normalizerMonoidHom g)

/-- Every outer involution of the actual Higman–Sims carrier has a displacement
which is an involution and lies in the center of no Sylow two-subgroup. -/
theorem outer_displacement (b : MulAut Carrier) (hb : orderOf b = 2)
    (hout : ¬ ∃ s : Carrier, b = MulAut.conj s) : HasNonTwoCentralDisplacement b := by
  obtain ⟨n, rfl, hn, ho⟩ := outer_involution_lift b hb hout
  rcases outer_involution_permutation_fusion n hn ho with ⟨g, hg⟩ | ⟨g, hg⟩
  · exact displacement_of_conjugate n g 0 hg
  · exact displacement_of_conjugate n g 1 hg

end Theory.SpecificGroups.ExceptionalOuterDisplacements.HS
