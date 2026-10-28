module

public import Theory.SpecificGroups.ReeF4.ConverseParabolics
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.FixedGeometry.FixedBruhat
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocal
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocal.Octagon

/-!
# Covering Ree two-local normalizers by full parabolics

The positive subgroup in `ConverseParabolics` has odd index: transport the
proved fixed-Bruhat calculation through the matrix-preserving equivalence
from the canonical local-block construction. Thus every two-subgroup fixes
an edge in the coset graph of the two full parabolics.

For `1 ≤ m`, the concrete coset graph is a proved octagon with odd apartment
stabilizers. The finite-tree argument therefore puts the full normalizer of
every nonidentity two-subgroup in a conjugate proper parabolic. The final
coverage theorems discharge all geometric premises, without requiring
simplicity or an order formula. The parabolics include all torus words, and
the normalizer is taken in the actual fixed-point carrier.

Source: GLS3, Theorem 3.1.3 and §§2.3, 2.6
(`refs/KGroup/GLS3/chapter3.tex`, `refs/KGroup/GLS3/chapter2.tex`). This is the
coverage ingredient for the Ree case of Aschbacher–Smith, Theorem 0.1.2(1),
printed p.4, repeated on p.482 of `refs/quasithin.pdf`.
-/

public section

namespace ReeF4.ConverseParabolics

open Subgroup LargeLocalSeeds
open MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry

/-- The positive subgroup of the actual Ree model has odd index. No
simplicity or order formula is required, even at the binary parameter. -/
theorem unipotent_index_odd (m : ℕ) : Odd (unipotent m).index := by
  let d := canonicalLocalBlockInput m
  have h := LargeLocalSeeds.FixedBruhat.standardUnipotent_index_odd d
  rw [← (standardUnipotent d).index_map_equiv d.modelEquiv] at h
  change Odd ((standardUnipotent d).map d.modelEquiv.toMonoidHom).index at h
  rwa [standardUnipotent_map_eq d] at h

/-- The specified positive subgroup is an ambient Sylow two-subgroup. -/
theorem exists_sylow_eq_unipotent (m : ℕ) :
    ∃ S : Sylow 2 (Model m), (S : Subgroup (Model m)) = unipotent m :=
  ⟨(unipotent_isPGroup m).toSylow (unipotent_index_odd m).not_two_dvd_nat, rfl⟩

/-- Every two-subgroup fixes a chamber in the actual full-parabolic coset
graph. In particular the subgroup need not be a root subgroup. -/
theorem twoSubgroup_fixes_edge {m : ℕ} (R : Subgroup (Model m))
    (hR : IsPGroup 2 R) :
    ∃ v w : Vertex m, (incidenceGraph m).Adj v w ∧
      v ∈ GroupAction.EvenPolygon.fixedVertices R ∧
      w ∈ GroupAction.EvenPolygon.fixedVertices R :=
  exists_fixed_edge (unipotent_index_odd m) R hR

/-- With the concrete octagon geometry supplied, every nonidentity
two-subgroup has its full normalizer in a conjugate proper full parabolic.
Odd index is proved above and is not an additional premise. -/
theorem normalizer_cover_of_octagon {m : ℕ}
    (hgeometry : OctagonGeometry m) (hodd : OddApartmentStabilizers m)
    (R : Subgroup (Model m)) (hR : R ≠ ⊥) (hp : IsPGroup 2 R) :
    ∃ (g : Model m) (s : Side), parabolic m s ≠ ⊤ ∧
      (normalizer (R : Set (Model m))).map (MulAut.conj g).toMonoidHom ≤
        parabolic m s :=
  MaximalSubgroups.AbelianCharacteristic.normalizer_cover_of_octagon
    hgeometry (unipotent_index_odd m) hodd R hR hp

/-- Every nonidentity two-subgroup of the large Ree group has its full
normalizer in a conjugate proper full parabolic. The concrete octagon and
its odd apartment stabilizers discharge the geometric premises. -/
theorem normalizer_cover_proper {m : ℕ} (hm : 1 ≤ m)
    (R : Subgroup (Model m)) (hR : R ≠ ⊥) (hp : IsPGroup 2 R) :
    ∃ (g : Model m) (s : Side), parabolic m s ≠ ⊤ ∧
      (normalizer (R : Set (Model m))).map (MulAut.conj g).toMonoidHom ≤
        parabolic m s :=
  normalizer_cover_of_octagon (octagonGeometry m hm) (oddApartmentStabilizers m hm)
    R hR hp

/-- Full-parabolic normalizer coverage in the form used by the quasithin
converse. This applies to arbitrary nonidentity two-subgroups. -/
theorem normalizer_cover {m : ℕ} (hm : 1 ≤ m)
    (R : Subgroup (Model m)) (hR : R ≠ ⊥) (hp : IsPGroup 2 R) :
    ∃ (g : Model m) (s : Side),
      (normalizer (R : Set (Model m))).map (MulAut.conj g).toMonoidHom ≤
        parabolic m s := by
  obtain ⟨g, s, _, hcover⟩ := normalizer_cover_proper hm R hR hp
  exact ⟨g, s, hcover⟩

end ReeF4.ConverseParabolics
