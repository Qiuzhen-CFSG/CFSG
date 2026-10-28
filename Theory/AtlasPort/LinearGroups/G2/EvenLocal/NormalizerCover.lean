module

public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.CosetGeometry
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.HexagonFixedPoint
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon

/-!
# Even-field G₂ normalizers lie in conjugate parabolics

Every nonidentity two-subgroup of the split-octonion automorphism group has its
normalizer contained in a conjugate of one of the two root-defined parabolics.
Sylow conjugacy supplies a fixed incident pair in the actual parabolic coset
graph. The proved octonion hexagon geometry makes the fixed graph a finite tree;
its center and the preserved vertex colors give a vertex fixed by the full
normalizer. Its coset stabilizer yields the asserted containment, with actual
conjugation implemented by `Subgroup.map`.

The proof works over every finite field of characteristic two. Thus it applies
in particular to fields of order `2^f` with `f ≥ 2`, without requiring simplicity
or any additional geometric premise.

Source: the generic case of Aschbacher--Smith, *The Classification of Quasithin
Groups*, Theorem 0.1.2(1), printed pp.3--4, repeated on pp.481--482; the
normalizer containment is the defining-characteristic Borel--Tits step.
-/

public section

namespace Atlas.G2.EvenLocal.NormalizerCover

open LieParabolicSetup

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The normalizer of every nonidentity two-subgroup is conjugate into one of
the two actual root-defined parabolics of the split-octonion automorphism group. -/
theorem normalizer_conjugate_le_parabolic
    (R : Subgroup (Model F)) (hR : R ≠ ⊥) (hpR : IsPGroup 2 R) :
    ∃ g : Model F,
      (Subgroup.normalizer (R : Set (Model F))).map (MulAut.conj g).toMonoidHom ≤
        parabolic₁ ∨
      (Subgroup.normalizer (R : Set (Model F))).map (MulAut.conj g).toMonoidHom ≤
        parabolic₂ := by
  obtain ⟨v, hv⟩ := normalizer_fixed_vertex_of_fixed_edge
    (OctonionHexagon.hexagonData (F := F)) R hR hpR (exists_fixed_edge R hpR)
  exact normalizer_conjugate_le_of_fixed_vertex R v hv

end Atlas.G2.EvenLocal.NormalizerCover
