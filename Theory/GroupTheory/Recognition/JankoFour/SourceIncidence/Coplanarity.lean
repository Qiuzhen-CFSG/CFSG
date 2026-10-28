module
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Native.Coplanarity
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.OrbitTransport
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.PointChart
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Markers

/-!
# Coplanarity in the literal point residue

The string condition puts every plane shared by two lines through x into
the residue at x. The original Todd chart therefore identifies ambient
coplanarity with native trio coplanarity. The proved native shared-octad
criterion gives exactly the unchanged Input.delta_coplanar clause.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (5.4)(2), p.600,
DOI 10.1007/BF01232280.
-/

public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.LocalData
open LocalGeometry LocalGeometry.LocalSubgroups SourceCycleBase GraphUniquenessSystem
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z} (a : LocalData h)

/-- Common-plane incidence of two lines through x is read in the original
Todd chart at x. The string condition places every common plane at x. -/
theorem coplanar_at (x : Point a.P) (l m : {l : Line a.L // OnLine a.L x l}) :
    Coplanar a.L l.val m.val ↔
      Native.Coplanar (a.residueChart.linesAt x l) (a.residueChart.linesAt x m) := by
  constructor
  · rintro ⟨π,hl,hm⟩
    let π' : {π : Plane z // OnPlane a.P x π} := ⟨π,a.string x l.val π l.property hl⟩
    exact ⟨a.residueChart.planesAt x π',
      (a.residueChart.incidenceAt x l π').mp hl,
      (a.residueChart.incidenceAt x m π').mp hm⟩
  · rintro ⟨π,hl,hm⟩
    let π' := (a.residueChart.planesAt x).symm π
    have he : a.residueChart.planesAt x π' = π := (a.residueChart.planesAt x).apply_symm_apply π
    exact ⟨π'.val,(a.residueChart.incidenceAt x l π').mpr (he.symm ▸ hl),
      (a.residueChart.incidenceAt x m π').mpr (he.symm ▸ hm)⟩

/-- AS91 (5.4)(2), with the unchanged native labels and original point chart. -/
theorem delta_coplanar (x : Point a.P) (l m : Line a.L)
    (hl : OnLine a.L x l) (hm : OnLine a.L x m) :
    Coplanar a.L l m ↔ ∃ i : Fin 5, i.val ≤ 2 ∧ LineType a.residueChart i x l m := by
  rw [a.coplanar_at x ⟨l,hl⟩ ⟨m,hm⟩,NativeCoplanarity.coplanar_iff]
  apply exists_congr
  intro i
  exact and_congr_right (fun _ => (lineType_at a.residueChart i x ⟨l,hl⟩ ⟨m,hm⟩).symm)

end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.LocalData
