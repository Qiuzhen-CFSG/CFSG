module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.OctadOverlap
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.ResidueCharts

/-!
# Far-orbital exclusion in the literal point residue

Transport a point-plane flag and both lines by the same ambient coset
representative. A δ₁ neighbor of a plane line shares an octad with that
native sextet, so the native octad-overlap lemma excludes δ₄ from every
line of the plane through the point. This is the incidence step used in
the first paragraph of AS91 (7.4). The proof retains the original Todd
marking and left-coset conventions.

Source: Aschbacher–Segev (1991), (3.13.1) and (7.4), pp.596,603.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
open GraphUniquenessSystem
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}
namespace Input
variable (d : Input h)

/-- The actual ambient (3.13.1), in the exact transported marking used by
 the filtration: a δ₁ neighbor of a plane line cannot be δ₄ from any line
 of that plane through the same point. -/
theorem not_delta_four_of_plane_delta_one {x : Point d.P} {π : Plane z}
    {l k m : Line d.L} (hxπ : OnPlane d.P x π)
    (_hxl : OnLine d.L x l) (hlπ : LineOnPlane d.L l π)
    (hxk : OnLine d.L x k) (hkπ : LineOnPlane d.L k π)
    (hmk : LineType d.residue 1 x m k) : ¬ LineType d.residue 4 x m l := by
  rintro ⟨g,a,b,hgx,hga,hgb,ht⟩
  have hgp : g • Cosets.vertex d.P.M 1 = x := by
    simpa only [Cosets.smul_vertex,mul_one] using hgx
  have hp : g⁻¹ • x = Cosets.vertex d.P.M 1 := by rw [← hgp,inv_smul_smul]
  let k' : {l : Line d.L // OnLine d.L (Cosets.vertex d.P.M 1) l} :=
    ⟨g⁻¹ • k, by simpa only [OnLine,hp] using incident_smul g⁻¹ hxk⟩
  let π' : {π : Plane z // OnPlane d.P (Cosets.vertex d.P.M 1) π} :=
    ⟨g⁻¹ • π, by simpa only [OnPlane,hp] using incident_smul g⁻¹ hxπ⟩
  have hpa : g⁻¹ • m = a.val := by rw [← hga,inv_smul_smul]
  have hpb : g⁻¹ • l = b.val := by rw [← hgb,inv_smul_smul]
  have hkπ' : LineOnPlane d.L k'.val π'.val := incident_smul g⁻¹ hkπ
  have hbπ' : LineOnPlane d.L b.val π'.val := by
    change Cosets.Incident d.L.G₂ (centralizer z) b.val (g⁻¹ • π)
    rw [← hpb]
    exact incident_smul g⁻¹ hlπ
  have htype : Native.Delta 1 (d.residue.lines a) (d.residue.lines k') := by
    apply (d.residue.lineType_one_base a k').mp
    simpa only [hp,hpa] using lineType_smul g⁻¹ hmk
  obtain ⟨_hne,A,hA⟩ := htype
  obtain ⟨hAa,hAk⟩ := Finset.mem_inter.mp hA
  have hAkπ : Native.PlaneOctad (d.residue.planes π') A :=
    ((d.residue.incidence k' π').mp hkπ') A hAk
  exact Native.not_delta_four_of_plane_octad ⟨A,hAa,hAkπ⟩
    ((d.residue.incidence b π').mp hbπ') ht

end Input
end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
