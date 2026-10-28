module
public import Theory.Representation.PSL3Two.FourGroupGeometry.Normalizers.FourGroupCoverage
public import Theory.Representation.PSL3Two.FourGroupGeometry.Normalizers.PointModel

/-!
# Self-centrality of elementary four-groups in SL3(2)

The actual point/line four-group coverage moves a given elementary four-group
to the point translations. Their proved automorphism centralizer is the
inner point group. Injective conjugation transports that equality back to
the original matrix subgroup. This is used on the literal local quotient
in MS93 (4.4.1), printed p.892, after the critical image has order four.
-/

public section
open Subgroup Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
namespace BinaryLinearThree.FourGroupGeometry
 theorem fourGroup_centralizer (E : Subgroup SL) [IsElementaryAbelian 2 E]
    (hcard : Nat.card E=4) : centralizer (E : Set SL)=E := by
  obtain ⟨e,he⟩ := Normalizers.fourGroup_map_point E hcard
  let f : SL →* MulAut SL := MulAut.conj.comp e.toMonoidHom
  have hf : Function.Injective f := by
    intro a b hab
    change MulAut.conj (e a) = MulAut.conj (e b) at hab
    exact e.injective (Matrix.PSL3Two.MarkedAutomorphisms.conj_injective hab)
  have hm : E.map f=Normalizers.innerPoint := by
    change E.map (MulAut.conj.comp e.toMonoidHom)=_
    rw [← Subgroup.map_map,he]
  apply le_antisymm _ E.le_centralizer
  apply (map_le_map_iff_of_injective hf).mp
  calc
    (centralizer (E : Set SL)).map f ≤ centralizer (E.map f : Set (MulAut SL)) := by
      simpa only [Subgroup.coe_map] using map_centralizer_le_centralizer_image (E : Set SL) f
    _ = E.map f := by rw [hm,Normalizers.point_centralizer]
end BinaryLinearThree.FourGroupGeometry
