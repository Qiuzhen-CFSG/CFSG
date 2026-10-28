module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.Replacement.Unequal
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.Normalizer

/-!
# Equal edge layers preserve the original moving Z-seed

The local centralizer of an incident Z-layer is its edge kernel. A local
conjugator preserving that Z-layer therefore normalizes the edge kernel.
The actual (4.5.2)(i) normality then preserves the moving neighboring seed.
This is the equal-beta comparison used in (4.5.4)(ii), on the same path
and with its original conjugator; no later marked section is required.

Source: Meierfrankenfeld--Stellmacher (1993), pp.897--899.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.Replacement.Equal
open Early.Orbit.Source PathCentrality
variable {M : Type*} [Group M] [Finite M] {R L : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

/-- The source normality gives equality of the actual Z-seeds when the
original local conjugator preserves their incident Z-layer. -/
theorem seed_Z_eq_of_edge_Z_eq (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : Early.SourcePath R a)
    (g : stabilizer R a)
    (heq : Z R (p.walk.getVert 5) = Z R (act R g (p.walk.getVert 5))) :
    Z R (p.walk.getVert 6) = Z R (act R g (p.walk.getVert 6)) := by
  have ha : color R a = false := p.center_eq ▸ p.even_color (i := 4) (by decide) (by decide)
  have hat : Adjacent R a (p.walk.getVert 5) := by
    simpa only [p.center_eq] using p.adjacent (i := 4) (by decide)
  have hct := adjacent_symm R (p.adjacent (i := 5) (by decide))
  have hgi : (g : FreeAmalgam R)⁻¹ ∈ normalizer (Z R (p.walk.getVert 5) : Set (FreeAmalgam R)) := by
    rw [mem_normalizer_iff_map_conj_eq]
    change (Z R (p.walk.getVert 5)).map (MulAut.conj (g : FreeAmalgam R)⁻¹).toMonoidHom = _
    rw [← Z_act]
    exact heq.symm
  have hgn := (normalizer (Z R (p.walk.getVert 5) : Set (FreeAmalgam R))).inv_mem hgi
  simp only [inv_inv] at hgn
  have hgP : (g : FreeAmalgam R) ∈ relativeNormalizer R a (p.walk.getVert 5) :=
    Unequal.edge_Z_normalizer_le common earlier ha hat ⟨g.property, hgn⟩
  have hm := (p.moving_neighbors source common earlier (i := 4)
    (by decide) (by decide) (by decide)).2
  simp only [p.center_eq] at hm
  have hgZ := Z_normalized_by_relativeNormalizer_of_moving common earlier
    (p.even_color (i := 6) (by decide) (by decide)) ha hct hat hm hgP
  have hgiZ := (normalizer (Z R (p.walk.getVert 6) : Set (FreeAmalgam R))).inv_mem hgZ
  have hmZ := mem_normalizer_iff_map_conj_eq.mp hgiZ
  change (Z R (p.walk.getVert 6)).map (MulAut.conj (g : FreeAmalgam R)⁻¹).toMonoidHom = _ at hmZ
  rw [← Z_act] at hmZ
  exact hmZ.symm

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.Replacement.Equal
