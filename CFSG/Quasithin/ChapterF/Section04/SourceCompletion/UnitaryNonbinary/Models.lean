module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.Geometry
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFour.SylowGeometry
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.Model

/-!
# The actual projective carriers of the unitary completion branches

The four-dimensional group has parameter q = 2^m and matrix field of order
q². Its trivial center follows from the core-free Sylow normalizer. Hence
the extension geometry transport applies to the actual native parabolics.
The five-dimensional branch uses the fixed model parameter 4, retaining its
projective scalar quotient; no injectivity of SU₅ → PSU₅ is asserted.

Source: Aschbacher–Smith F.1.12(6–7), F.4.3–6 and 5.2.6–7,
printed pp.263–264, 274–277 and650–651.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry.RankTwo SimpleGraph.PathTransitivePolygon

/-- Full extensions of the actual four-dimensional projective group. -/
abbrev FourExtension (m : ℕ) (hm : 1 ≤ m) :=
  SourceExtension (GreenBook.LieModels.UnitaryFour.pointParabolic m hm)
    (GreenBook.LieModels.UnitaryFour.planeParabolic m hm)

/-- Full extensions of PSU₅(4), over the matrix field of order 16. -/
abbrev FiveExtension (U : GreenBook.UnitaryFive.Model 4) :=
  SourceExtension U.leftParabolic U.rightParabolic

open GreenBook.LieModels.UnitaryFour

/-- A central element lies in the Sylow normalizer and hence its normal core. -/
theorem four_center_eq_bot (m : ℕ) (hm : 1 ≤ m) :
    center (ProjectiveGroup m hm) = ⊥ := by
  have hle : center (ProjectiveGroup m hm) ≤ overlap m hm := by
    rw [← projectiveSylow_normalizer m hm]
    exact center_le_normalizer _
  have hc := normal_le_normalCore.mpr hle
  rw [overlap_normalCore_eq_bot m hm] at hc
  exact bot_unique hc

/-- The base acts faithfully by inner automorphisms, with no matrix-field
or unitary-parameter substitution. -/
theorem four_conj_injective (m : ℕ) (hm : 1 ≤ m) :
    Function.Injective (MulAut.conj : ProjectiveGroup m hm →* MulAut (ProjectiveGroup m hm)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro b hb
  change MulAut.conj b = 1 at hb
  have hc : b ∈ center (ProjectiveGroup m hm) := by
    rw [mem_center_iff]
    intro a
    have he := congrArg (fun f : MulAut (ProjectiveGroup m hm) => f a) hb
    change b*a*b⁻¹ = a at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  rwa [four_center_eq_bot m hm] at hc

/-- The full extension has the native Hermitian coset graph. -/
def fourGraphIso (m : ℕ) (hm : 1 ≤ m) (E : FourExtension m hm) :
    graph (SourceExtension.nativeFamily (P₀ := pointParabolic m hm) (P₁ := planeParabolic m hm)) ≃g
      graph E.family :=
  E.graphIso (four_conj_injective m hm)

/-- Native rooted-path calculations feed an arbitrary full-extension completion
through the literal whole overlap, including extensions of even outer degree. -/
theorem four_completion_rootPathTransitive
    (m : ℕ) (hm : 1 ≤ m) (E : FourExtension m hm) {M : Type*} [Group M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range)
    (i : Bool) (n : ℕ)
    (ht : RootPathTransitive
      (graph (SourceExtension.nativeFamily (P₀ := pointParabolic m hm) (P₁ := planeParabolic m hm)))
      (ProjectiveGroup m hm)
      (base (SourceExtension.nativeFamily (P₀ := pointParabolic m hm) (P₁ := planeParabolic m hm)) i) n) :
    RootPathTransitive (graph c.cosetFamily) M (base c.cosetFamily i) n :=
  E.completion_rootPathTransitive_of_native (four_conj_injective m hm)
    (parabolics_generate m hm) c hoverlap i n ht

end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary
