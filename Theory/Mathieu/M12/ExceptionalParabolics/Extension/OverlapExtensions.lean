module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.Amalgam
public import Theory.GroupTheory.Amalgam.TwistTransport
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.OverlapExtensions.Basic
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.OverlapExtensions.CentralExtensions
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.OverlapExtensions.Coverage

/-!
# Every outer M₁₂ overlap automorphism extends to the first endpoint

The certified generator-image coverage expresses each automorphism of the
actual overlap as inner conjugation after one of four central binary changes.
The two endpoint characters extend those changes to the genuine nonsplit first
endpoint. Composing with conjugation by the included overlap element and using
the certified generating triple gives compatibility on every overlap element.

The final theorem supplies both finite calculations, with no faithfulness,
factorization or coverage premise. It discharges the outer endpoint-extension
input of exceptional rigidity; the full source-theorem assembly remains with
the CFSG consumer. Source context: Aschbacher--Smith F.1.11--12, printed
pp.262--263, E.2.16, p.228, and 14.2.21, p.988, `refs/quasithin.pdf`.
The corrected nonsplit first core and degree-24 ATLAS attribution are retained
from `Extension.Amalgam`.
-/
@[expose] public section
namespace Sporadic.Mathieu.M12ExceptionalExtension.OverlapExtensions
open Theory.GroupTheory.RankTwoAmalgam

/-- Assembly from generator-image coverage and the four central extensions.
Both finite calculations are premises here; the unconditional theorem must
supply their independent producers. -/
theorem all_extend_of_coverage
    (hcover : ∀ d : MulAut overlap, ∃ u : overlap, ∃ p q : Bool,
      ∀ j, d (Overlap.generator j) = generatorImage u p q j)
    (hext : ∀ p q : Bool, ∃ a : MulAut firstParabolic,
      ∀ j, a (VerifiedPair.amalgam.left (Overlap.generator j)) =
        VerifiedPair.amalgam.left (centralImage p q j)) :
    ∀ d : MulAut overlap, ExtendsAcross VerifiedPair.amalgam.left d := by
  intro d
  obtain ⟨u, p, q, hu⟩ := hcover d
  obtain ⟨a, ha⟩ := hext p q
  apply extendsAcross_of_generator_images d
    (a.trans (MulAut.conj (VerifiedPair.amalgam.left u)))
  intro j
  change VerifiedPair.amalgam.left u * a (VerifiedPair.amalgam.left (Overlap.generator j)) *
    (VerifiedPair.amalgam.left u)⁻¹ = VerifiedPair.amalgam.left (d (Overlap.generator j))
  rw [ha, hu]
  simp only [generatorImage, map_mul, map_inv]
end Sporadic.Mathieu.M12ExceptionalExtension.OverlapExtensions

namespace Sporadic.Mathieu.M12ExceptionalExtension
open Theory.GroupTheory.RankTwoAmalgam

/-- Every automorphism of the literal outer overlap extends to its nonsplit
first endpoint. Both the generator coverage and central extensions are proved. -/
theorem overlap_automorphisms_extend :
    ∀ d : MulAut overlap, ExtendsAcross VerifiedPair.amalgam.left d :=
  OverlapExtensions.all_extend_of_coverage
    OverlapExtensions.generator_coverage OverlapExtensions.central_extensions

/-- An actual endpoint automorphism extending the given overlap automorphism. -/
noncomputable def overlapExtension (d : MulAut overlap) : MulAut firstParabolic :=
  Classical.choose (overlap_automorphisms_extend d)

/-- The extension commutes with the literal inclusion on every overlap element. -/
theorem overlapExtension_apply (d : MulAut overlap) (b : overlap) :
    overlapExtension d (VerifiedPair.amalgam.left b) = VerifiedPair.amalgam.left (d b) :=
  Classical.choose_spec (overlap_automorphisms_extend d) b

end Sporadic.Mathieu.M12ExceptionalExtension
