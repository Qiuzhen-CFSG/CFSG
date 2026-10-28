module

public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.RadicalIntersection
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Flags

/-!
# Lines recovered from neighboring radicals

The intersection of two neighboring point radicals recovers the conjugate
of the original three-space. Its full normalizer is the supplied line
group, so the two points determine a unique line. A plane containing the
two points has its marker in this intersection, and hence contains the
line. Flag transitivity and the radical's four-point action then identify
the actual H-orbit of the chosen edge with all edges inside its plane.

These prove the unchanged unique-line, plane-closure and local-edge fields
of SourceCycleBase.Input. No ambient uniqueness or generation is assumed.

Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*,
Invent. Math. 105 (1991), (5.2)–(5.3), pp.600–601,
DOI 10.1007/BF01232280.
-/

public section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence
open SourceRecognition LocalGeometry LocalGeometry.LocalSubgroups SourceCycleBase GraphUniquenessSystem
namespace LocalData
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z} (a : LocalData h)

/-- The three-space recovered from a neighboring pair determines its line,
since the supplied line group is exactly its ambient normalizer. -/
private theorem line_eq_of_space_comap_eq (g k : G)
    (he : a.d.space.comap (MulAut.conj g⁻¹).toMonoidHom =
      a.d.space.comap (MulAut.conj k⁻¹).toMonoidHom) :
    Cosets.vertex a.L.G₂ g = Cosets.vertex a.L.G₂ k := by
  apply (Cosets.vertex_eq_iff _ _ _).mpr
  rw [a.line_normalizer]
  apply mem_normalizer_iff.mpr
  intro v
  have hh := SetLike.ext_iff.mp he (k*v*k⁻¹)
  change g⁻¹*(k*v*k⁻¹)*(g⁻¹)⁻¹ ∈ a.d.space ↔
    k⁻¹*(k*v*k⁻¹)*(k⁻¹)⁻¹ ∈ a.d.space at hh
  simpa only [inv_inv,mul_inv_rev,mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using hh.symm

/-- The unchanged unique-line clause, derived from the neighboring-radical
intersection rather than postulated as an incidence property. -/
theorem unique_line (x y : Point a.P) (hxy : Adj a.L x y) :
    ∃! l, OnLine a.L x l ∧ OnLine a.L y l := by
  obtain ⟨hne,l,hxl,hyl⟩ := hxy
  refine ⟨l,⟨hxl,hyl⟩,?_⟩
  intro k hk
  obtain ⟨g,rfl,rfl⟩ := hxl
  obtain ⟨n,hn,rfl⟩ := hk.1
  have hg := a.core_intersection_at g y hyl hne.symm
  have hn' := a.core_intersection_at n y hk.2 (by rw [hn]; exact hne.symm)
  rw [hn] at hn'
  exact a.line_eq_of_space_comap_eq n g (hn'.symm.trans hg)

/-- The unchanged plane-closure clause: its marker belongs to both point
radicals, hence to the recovered line three-space. -/
theorem plane_closed (x y : Point a.P) (l : Line a.L) (π : Plane z)
    (hne : x ≠ y) (hxl : OnLine a.L x l) (hyl : OnLine a.L y l)
    (hxπ : OnPlane a.P x π) (hyπ : OnPlane a.P y π) : LineOnPlane a.L l π := by
  obtain ⟨g,rfl,rfl⟩ := hxl
  have hm : marker π ∈ coreAt a.P (Cosets.vertex a.P.M g) ⊓ coreAt a.P y :=
    ⟨(a.marker_mem_core _ _).mpr hxπ,(a.marker_mem_core _ _).mpr hyπ⟩
  rw [a.core_intersection_at g y hyl hne.symm] at hm
  have hm' : marker (g⁻¹ • π) ∈ a.d.space := by
    rw [marker_smul]
    exact hm
  have hh := incident_smul g ((a.line_plane_marker (g⁻¹ • π)).mpr hm')
  simpa only [LineOnPlane,Cosets.smul_vertex,mul_one,smul_inv_smul] using hh

/-- The actual H-orbit of the source edge is exactly the edges in its plane.
Plane closure supplies a common line-plane flag; its common representative
and E's four-point transitivity give the transporter inside H. -/
theorem local_edge (t : G) (htH : t ∈ centralizer z) (htN : t ∈ a.L.G₂)
    (htM : t ∉ a.P.M) (x y : Point a.P) :
    (∃ k : centralizer z,
      ((k : G) • Cosets.vertex a.P.M 1 = x ∧ (k : G) • Cosets.vertex a.P.M t = y) ∨
      ((k : G) • Cosets.vertex a.P.M 1 = y ∧ (k : G) • Cosets.vertex a.P.M t = x)) ↔
    Adj a.L x y ∧ OnPlane a.P x (Cosets.vertex (centralizer z) 1) ∧
      OnPlane a.P y (Cosets.vertex (centralizer z) 1) := by
  have htne : Cosets.vertex a.P.M t ≠ Cosets.vertex a.P.M 1 :=
    fun he => htM ((Cosets.vertex_eq_base _ _).mp he)
  have htline : OnLine a.L (Cosets.vertex a.P.M t) (Cosets.vertex a.L.G₂ 1) :=
    ⟨t,rfl,(Cosets.vertex_eq_base _ _).mpr htN⟩
  have htadj : Adj a.L (Cosets.vertex a.P.M 1) (Cosets.vertex a.P.M t) :=
    ⟨htne.symm,Cosets.vertex a.L.G₂ 1,⟨1,rfl,rfl⟩,htline⟩
  have hplane (k : centralizer z) (b : Point a.P)
      (hb : OnPlane a.P b (Cosets.vertex (centralizer z) 1)) :
      OnPlane a.P ((k : G) • b) (Cosets.vertex (centralizer z) 1) := by
    have he : (k : G) • Cosets.vertex (centralizer z) 1 = Cosets.vertex (centralizer z) 1 := by
      rw [Cosets.smul_vertex,mul_one]
      exact (Cosets.vertex_eq_base _ _).mpr k.property
    simpa only [OnPlane,he] using incident_smul (k : G) hb
  have hxplane : OnPlane a.P (Cosets.vertex a.P.M 1) (Cosets.vertex (centralizer z) 1) :=
    ⟨1,rfl,rfl⟩
  have htplane : OnPlane a.P (Cosets.vertex a.P.M t) (Cosets.vertex (centralizer z) 1) :=
    ⟨t,rfl,(Cosets.vertex_eq_base _ _).mpr htH⟩
  constructor
  · rintro ⟨k,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩
    · exact ⟨adj_smul k.val htadj,hplane k _ hxplane,hplane k _ htplane⟩
    · exact ⟨adj_symm (adj_smul k.val htadj),hplane k _ htplane,hplane k _ hxplane⟩
  · rintro ⟨⟨hne,l,hxl,hyl⟩,hxπ,hyπ⟩
    have hlπ := a.plane_closed x y l _ hne hxl hyl hxπ hyπ
    obtain ⟨g,hgx,hgl,hgπ⟩ := a.flag_transitive x l _ hxl hlπ
    have hgH := (Cosets.vertex_eq_base _ _).mp hgπ
    have hyline : OnLine a.L (g⁻¹ • y) (Cosets.vertex a.L.G₂ 1) := by
      rw [←hgl] at hyl
      simpa only [OnLine,Cosets.smul_vertex,inv_mul_cancel] using incident_smul g⁻¹ hyl
    have hyne : g⁻¹ • y ≠ Cosets.vertex a.P.M 1 := by
      intro he
      have hh := congrArg (g • ·) he
      have hyx : y = x := by
        simpa only [smul_inv_smul,Cosets.smul_vertex,mul_one,hgx] using hh
      exact hne hyx.symm
    obtain ⟨e,he⟩ := a.core_transitive_base ⟨_,htline⟩ ⟨_,hyline⟩ htne hyne
    have heH : (e : G) ∈ centralizer z :=
      mem_centralizer_singleton_iff.mpr
        ((a.E_le_S e.property) z (a.d.markedPoint 0).property).symm
    refine ⟨⟨g*(e : G),(centralizer z).mul_mem hgH heH⟩,Or.inl ⟨?_,?_⟩⟩
    · change (g*(e : G)) • Cosets.vertex a.P.M 1 = x
      rw [mul_smul,Cosets.smul_vertex,mul_one,
        (Cosets.vertex_eq_base _ _).mpr (a.P.E_le e.property),Cosets.smul_vertex,mul_one]
      exact hgx
    · change (g*(e : G)) • Cosets.vertex a.P.M t = y
      rw [mul_smul,he,smul_inv_smul]

end LocalData
end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence
