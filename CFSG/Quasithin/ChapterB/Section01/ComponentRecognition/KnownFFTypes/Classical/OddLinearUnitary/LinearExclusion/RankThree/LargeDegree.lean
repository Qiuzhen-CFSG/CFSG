module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.SourceBounds
public import Theory.Representation.BinaryCoprimeDegree.TransitivePlane
public import Theory.SpecificGroups.PSL3.PrimePlane

/-!
# The large-prime binary degree obstruction for PSL₃

Restrict the original faithful binary representation to the actual perfect
subgroup F*(G). Its central quotient is identified with PSL₃(F), |F|=p.
The line parabolic supplies a transitive elementary abelian plane of order p².
If p divides the central kernel, the Schur-field determinant bound gives
degree at least p ordₚ(2); otherwise the plane and its normalizer lift, giving
the stronger bound (p+1) ordₚ(2). For p≥5 either bound exceeds eighteen.

This discharges the large-prime degree input to the rank-three exclusion in
Aschbacher--Smith K.2, printed p.453; compare Guralnick--Malle, Classification
of 2F-modules I, Proposition 4.2, manuscript pp.9--10. The full projective
minimum p²+p−2 is unnecessary here. There is no ratio hypothesis or assumption
of absolute irreducibility on F*(G), and central covers are retained.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree
open Subgroup Theory.GroupTheory Representation Representation.BinaryCoprimeDegree

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The actual source action has degree greater than eighteen whenever its
quasisimple F* has central quotient PSL₃(p), p prime and at least five. -/
theorem source_degree_gt_eighteen
    (ρ : Representation (ZMod 2) G V) (h : SourceAction ρ)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 3 p) :
    18 < Module.finrank (ZMod 2) V := by
  let : Fact p.Prime := ⟨hp⟩
  let : IsQuasisimple (generalizedFitting G) := h.quasisimple
  let : IsIrreducible (ρ.comp (generalizedFitting G).subtype) := h.irreducible
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hm
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center (generalizedFitting G)))
  have hf : Function.Surjective f :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hc : f.ker ≤ center (generalizedFitting G) := by
    dsimp only [f]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hd := central_quotient_transitive_plane_degree
    (ρ.comp (generalizedFitting G).subtype)
    (h.faithful.comp Subtype.val_injective) f hf hc (by omega : p ≠ 2)
    (Matrix.PSL3.prime_hasTransitiveElementaryPlane F hcard)
  have hlo := twenty_le_prime_times_binary_order hp hp5
  omega

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree
