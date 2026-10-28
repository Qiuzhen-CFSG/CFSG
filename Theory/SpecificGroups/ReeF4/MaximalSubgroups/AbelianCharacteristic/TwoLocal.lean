module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocal.Geometry
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocal.ParabolicComparison

/-!
# The defining-prime Ree normalizer reduction

A nonidentity two-subgroup fixes an edge of the parabolic coset graph by Sylow
conjugacy. The generalized-octagon argument makes its full normalizer fix a
vertex, so a conjugate lies in that vertex's full parabolic. An apartment cycle
proves that both parabolics are proper. Applying this to the image of the
elementary abelian subgroup gives `TwoLocalCover`.

The octagon and odd-order inputs below still have to be proved for the actual
exceptional fixed-point construction. Accordingly only the conditional
assembly is asserted here; `twoLocalCover` remains an obligation of this module.
No ambient normality, simplicity, proper-K, or Malle exhaustion is assumed.

Source: finite Borel--Tits, GLS3 Theorem 3.1.3
(`refs/KGroup/GLS3/chapter3.tex`); the Ree relative Weyl group is dihedral of
order sixteen by GLS3 2.3.2(d), and the BN-pair is described in §§2.3 and 2.6.
-/

public section

namespace ReeF4.MaximalSubgroups.AbelianCharacteristic

open Subgroup LargeLocalSeeds ConverseParabolics GroupAction.EvenPolygon TwoLocalGeometry

/-- The finite-tree argument applies to every nonidentity two-subgroup. All
remaining concrete geometric assertions are explicit premises. -/
theorem normalizer_cover_of_octagon {m : ℕ}
    (hgeometry : OctagonGeometry m) (hindex : Odd (unipotent m).index)
    (hodd : OddApartmentStabilizers m)
    (R : Subgroup (Model m)) (hR : R ≠ ⊥) (hp : IsPGroup 2 R) :
    ∃ (g : Model m) (s : Side), parabolic m s ≠ ⊤ ∧
      (normalizer (R : Set (Model m))).map (MulAut.conj g).toMonoidHom ≤ parabolic m s := by
  obtain ⟨v, hv⟩ := normalizer_fixed_vertex_of_fixed_edge
    (hgeometry.toEvenPolygonAction hodd) R hR hp (exists_fixed_edge hindex R hp)
  obtain ⟨g, s, hcover⟩ := normalizer_conjugate_le_of_fixed_vertex R v hv
  exact ⟨g, s, hgeometry.parabolic_ne_top s, hcover⟩

/-- Conditional final assembly. The parent task must establish every geometric
premise before exporting the unconditional `twoLocalCover`. -/
theorem twoLocalCover_of_octagon
    (hgeometry : ∀ m, 1 ≤ m → OctagonGeometry m)
    (hindex : ∀ m, 1 ≤ m → Odd (unipotent m).index)
    (hodd : ∀ m, 1 ≤ m → OddApartmentStabilizers m) : TwoLocalCover := by
  intro m hm M _ _ E _ hEe hE
  let := hEe
  apply normalizer_cover_of_octagon (hgeometry m hm) (hindex m hm) (hodd m hm)
    (E.map M.subtype)
  · exact fun h => hE ((E.map_eq_bot_iff_of_injective Subtype.val_injective).mp h)
  · exact (IsElementaryAbelian.isPGroup 2 E).map M.subtype

end ReeF4.MaximalSubgroups.AbelianCharacteristic
