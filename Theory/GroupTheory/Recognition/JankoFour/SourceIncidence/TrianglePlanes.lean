module
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Native.TrioRadicals
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.NeighborRadicals
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Coplanarity
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.CommonFixers
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.ChartTransport

/-!
# Triangles and common neighbors in the ambient planes

The original Todd projection maps each neighboring radical stabilizer onto
the literal intrinsic native trio core. If the two lines of a triangle were
noncoplanar, five native radical images would lift to five distinct points
on a four-point punctured line. This proves AS91 (5.5).
For (5.7), the plane marker fixes every common neighbor. If it lies outside
that neighbor's radical, its nontrivial Todd image belongs to both native
trio cores. Their trivial intersection off the coplanar orbit supplies a
plane through all three points; ambient uniqueness identifies that plane
with the original one. All maps use the original P,L and their Todd chart.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (3.12), (5.5),
(5.7), pp.596,601. These are the unchanged Input clauses.
-/

public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.LocalData
open LocalGeometry LocalGeometry.LocalSubgroups SourceCycleBase GraphUniquenessSystem
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z} (a : LocalData h)

/-- The image of E_y∩M at every line through the original point, under the
same Todd marking that defines its residue chart. -/
theorem neighbor_core_image_of_line
    (l : {l : Line a.L // OnLine a.L (Cosets.vertex a.P.M 1) l})
    (y : Point a.P) (hy : OnLine a.L y l.val) (hne : y ≠ Cosets.vertex a.P.M 1) :
    ((coreAt a.P y).subgroupOf a.P.M).map a.P.projection =
      M24ChapterHStabilizers.TrioAction.coreAt (a.residueChart.lines l) := by
  obtain ⟨m,hm,hl⟩ := l.property
  let m' : a.P.M := ⟨m,(Cosets.vertex_eq_base _ _).mp hm⟩
  have hmfix : m • Cosets.vertex a.P.M 1 = Cosets.vertex a.P.M 1 := by
    rw [Cosets.smul_vertex,mul_one,hm]
  have hy' : OnLine a.L (m⁻¹ • y) (Cosets.vertex a.L.G₂ 1) := by
    have hh := incident_smul m⁻¹ hy
    simpa only [OnLine,←hl,Cosets.smul_vertex,inv_mul_cancel] using hh
  have hne' : m⁻¹ • y ≠ Cosets.vertex a.P.M 1 := by
    intro he
    apply hne
    have hh := congrArg (m • ·) he
    simpa only [smul_inv_smul,hmfix] using hh
  let b := (ResidueChart.baseLine : {l : Line a.L // OnLine a.L (Cosets.vertex a.P.M 1) l})
  have hbase : trioStabilizer (a.residueChart.lines b) = trioStabilizer a.trio := by
    rw [←a.line_image,a.residueChart.point_line_overlap]
    apply le_antisymm
    · intro g hg
      obtain ⟨m,rfl⟩ := a.projection_surjective g
      exact ⟨m,hg,rfl⟩
    · exact map_comap_le a.P.projection _
  have hchart : a.residueChart.lines l = a.P.projection m' • a.residueChart.lines b := by
    apply Native.line_parts_injective
    exact a.residueChart.lines_equivariant m' b l (by
      change m • Cosets.vertex a.L.G₂ 1 = l.val
      rw [Cosets.smul_vertex,mul_one]
      exact hl)
  have hcore : M24ChapterHStabilizers.TrioAction.coreAt (a.residueChart.lines b) =
      M24ChapterHStabilizers.TrioAction.coreAt a.trio :=
    congrArg (fun K => K.pCoreIn 2) hbase
  rw [hchart,NativeTrioRadicals.core_smul,hcore]
  rw [←a.neighbor_core_image (m⁻¹ • y) hy' hne']
  apply le_antisymm
  · rintro q ⟨v,hv,rfl⟩
    change (v : G) ∈ coreAt a.P y at hv
    let u := m'⁻¹*v*m'
    have hu : (u : G) ∈ coreAt a.P (m⁻¹ • y) := by
      rw [coreAt_smul]
      change (m⁻¹)⁻¹*(m⁻¹*(v : G)*m)*((m⁻¹)⁻¹)⁻¹ ∈ coreAt a.P y
      simpa only [inv_inv,mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using hv
    refine ⟨a.P.projection u,⟨u,hu,rfl⟩,?_⟩
    change a.P.projection m' * a.P.projection (m'⁻¹*v*m') * (a.P.projection m')⁻¹ = _
    simp only [map_mul,map_inv,mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one]
  · rintro q ⟨r,⟨u,hu,rfl⟩,rfl⟩
    let v := m'*u*m'⁻¹
    have hv : (v : G) ∈ coreAt a.P y := by
      change m*(u : G)*m⁻¹ ∈ coreAt a.P y
      rw [coreAt_smul] at hu
      change (m⁻¹)⁻¹*(u : G)*((m⁻¹)⁻¹)⁻¹ ∈ coreAt a.P y at hu
      simpa only [inv_inv] using hu
    exact ⟨v,hv,by simp only [v,map_mul,map_inv]; rfl⟩

private theorem line_other_card (l : Line a.L) (y : Point a.P) (hy : OnLine a.L y l) :
    Nat.card {u : Point a.P // OnLine a.L u l ∧ u ≠ y} = 4 := by
  classical
  let X := {u : Point a.P // OnLine a.L u l}
  let y' : X := ⟨y,hy⟩
  let e : {u : Point a.P // OnLine a.L u l ∧ u ≠ y} ≃ {u : X // u ≠ y'} :=
    { toFun := fun u => ⟨⟨u.val,u.property.1⟩,fun he => u.property.2 (congrArg Subtype.val he)⟩
      invFun := fun u => ⟨u.val.val,u.val.property,fun he => u.property (Subtype.ext he)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let : Fintype X := Fintype.ofFinite X
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_subtype_compl,
    Fintype.card_subtype_eq,←Nat.card_eq_fintype_card,
    show Nat.card X = 5 from a.line_card l]

private theorem triangles_in_plane_base (y u : Point a.P)
    (hxy : Adj a.L (Cosets.vertex a.P.M 1) y)
    (hyu : Adj a.L y u) (hxu : Adj a.L (Cosets.vertex a.P.M 1) u) :
    ∃ π, OnPlane a.P (Cosets.vertex a.P.M 1) π ∧ OnPlane a.P y π ∧ OnPlane a.P u π := by
  classical
  obtain ⟨l,hxl,hyl⟩ := hxy.2
  obtain ⟨k,hxk,huk⟩ := hxu.2
  obtain ⟨m,hym,hum⟩ := hyu.2
  let l' := (⟨l,hxl⟩ : {l : Line a.L // OnLine a.L (Cosets.vertex a.P.M 1) l})
  let k' := (⟨k,hxk⟩ : {l : Line a.L // OnLine a.L (Cosets.vertex a.P.M 1) l})
  by_contra hn
  have hnc : ¬ Native.Coplanar (a.residueChart.lines l') (a.residueChart.lines k') := by
    intro hc
    obtain ⟨π,hlπ,hkπ⟩ := hc
    let π' := a.residueChart.planes.symm π
    have he : a.residueChart.planes π' = π := a.residueChart.planes.apply_symm_apply π
    have hlπ' := (a.residueChart.incidence l' π').mpr (he.symm ▸ hlπ)
    have hkπ' := (a.residueChart.incidence k' π').mpr (he.symm ▸ hkπ)
    exact hn ⟨π'.val,π'.property,a.string y l π'.val hyl hlπ',a.string u k π'.val huk hkπ'⟩
  obtain ⟨f,hf⟩ := NativeTrioRadicals.five_images _ _ hnc
  have lift (i : Fin 5) : ∃ v : a.P.M, (v : G) ∈ coreAt a.P y ∧ a.P.projection v = (f i).val := by
    exact (a.neighbor_core_image_of_line l' y hyl hxy.1.symm).ge (f i).property
  choose v hv hq using lift
  have fixes (i : Fin 5) : (v i : G) • Cosets.vertex a.P.M 1 = Cosets.vertex a.P.M 1 := by
    rw [Cosets.smul_vertex,mul_one]
    exact (Cosets.vertex_eq_base _ _).mpr (v i).property
  have fixy (i : Fin 5) : (v i : G) • y = y := coreAt_le_stabilizer a.P y (hv i)
  have inc (i : Fin 5) : OnLine a.L (Cosets.vertex a.P.M 1) ((v i : G) • k) := by
    simpa only [OnLine,fixes] using incident_smul (v i : G) hxk
  let images : Fin 5 → {w : Point a.P // OnLine a.L w m ∧ w ≠ y} := fun i =>
    ⟨(v i : G) • u,by
      have hh := incident_smul (v i : G) hum
      rw [a.core_fixes_lines y ⟨v i,hv i⟩ m hym] at hh
      exact hh,
      fun he => hyu.1 (MulAction.injective (v i : G) (he.trans (fixy i).symm)).symm⟩
  have hinj : Function.Injective images := by
    intro i j he
    have huw : (v i : G) • u = (v j : G) • u := congrArg Subtype.val he
    have hui : OnLine a.L ((v i : G) • u) ((v i : G) • k) := incident_smul _ huk
    have huj : OnLine a.L ((v i : G) • u) ((v j : G) • k) := huw.symm ▸ incident_smul _ huk
    have hne : Cosets.vertex a.P.M 1 ≠ (v i : G) • u := by
      intro hh
      exact hxu.1 (MulAction.injective (v i : G) ((fixes i).trans hh))
    obtain ⟨s,_,hs⟩ := a.unique_line _ _ ⟨hne,_,inc i,hui⟩
    have hlines : (v i : G) • k = (v j : G) • k :=
      (hs _ ⟨inc i,hui⟩).trans (hs _ ⟨inc j,huj⟩).symm
    apply hf
    apply Native.line_parts_injective
    change (f i).val • (a.residueChart.lines k').parts =
      (f j).val • (a.residueChart.lines k').parts
    rw [←hq i,←hq j,←a.residueChart.lines_equivariant (v i) k' ⟨_,inc i⟩ rfl,
      ←a.residueChart.lines_equivariant (v j) k' ⟨_,inc j⟩ rfl]
    exact congrArg (fun t => (a.residueChart.lines t).parts) (Subtype.ext hlines)
  have hc := Nat.card_le_card_of_injective images hinj
  rw [Nat.card_fin,a.line_other_card m y hym] at hc
  omega

/-- AS91 (5.5): every ambient triangle lies in a plane. The native radical
has more than four images of a noncoplanar line, while the actual neighboring
radical can move the third point only among four points on its fixed line. -/
theorem triangles_in_plane (x y u : Point a.P)
    (hxy : Adj a.L x y) (hyu : Adj a.L y u) (hux : Adj a.L u x) :
    ∃ π, OnPlane a.P x π ∧ OnPlane a.P y π ∧ OnPlane a.P u π := by
  let g := representative x
  have hx : g⁻¹ • x = Cosets.vertex a.P.M 1 := ResidueChart.representative_inv_point x
  obtain ⟨π,hxπ,hyπ,huπ⟩ := a.triangles_in_plane_base (g⁻¹ • y) (g⁻¹ • u)
    (by simpa only [hx] using adj_smul g⁻¹ hxy) (adj_smul g⁻¹ hyu)
    (by simpa only [hx] using adj_smul g⁻¹ (adj_symm hux))
  refine ⟨g • π,?_,?_,?_⟩
  · simpa only [OnPlane,←hx,smul_inv_smul] using incident_smul g hxπ
  · simpa only [OnPlane,smul_inv_smul] using incident_smul g hyπ
  · simpa only [OnPlane,smul_inv_smul] using incident_smul g huπ

private theorem common_neighbors_in_plane_base (x y : Point a.P) (π : Plane z)
    (hxy : DistanceTwo a.L x y) (hxπ : OnPlane a.P x π) (hyπ : OnPlane a.P y π)
    (hxu : Adj a.L x (Cosets.vertex a.P.M 1))
    (hyu : Adj a.L y (Cosets.vertex a.P.M 1)) :
    OnPlane a.P (Cosets.vertex a.P.M 1) π := by
  classical
  have hfix := a.marker_fixes_common_neighbor x y π hxy hxπ hyπ _ hxu hyu
  have hm : marker π ∈ a.P.M := by
    rw [Cosets.smul_vertex,mul_one] at hfix
    exact (Cosets.vertex_eq_base _ _).mp hfix
  let v : a.P.M := ⟨marker π,hm⟩
  by_cases hv : marker π ∈ a.P.E
  · apply (a.marker_mem_core π _).mp
    rw [coreAt_vertex]
    change 1⁻¹ * marker π * (1⁻¹)⁻¹ ∈ a.P.E
    simpa only [inv_one,one_mul,mul_one] using hv
  have hq : a.P.projection v ≠ 1 := by
    intro he
    apply hv
    have hk : v ∈ a.P.projection.ker := he
    rwa [a.P.projection_ker] at hk
  obtain ⟨l,hxl,hul⟩ := hxu.2
  obtain ⟨k,hyk,huk⟩ := hyu.2
  let l' := (⟨l,hul⟩ : {l : Line a.L // OnLine a.L (Cosets.vertex a.P.M 1) l})
  let k' := (⟨k,huk⟩ : {l : Line a.L // OnLine a.L (Cosets.vertex a.P.M 1) l})
  have hlq : a.P.projection v ∈
      M24ChapterHStabilizers.TrioAction.coreAt (a.residueChart.lines l') := by
    rw [←a.neighbor_core_image_of_line l' x hxl hxu.1]
    exact ⟨v,(a.marker_mem_core π x).mpr hxπ,rfl⟩
  have hkq : a.P.projection v ∈
      M24ChapterHStabilizers.TrioAction.coreAt (a.residueChart.lines k') := by
    rw [←a.neighbor_core_image_of_line k' y hyk hyu.1]
    exact ⟨v,(a.marker_mem_core π y).mpr hyπ,rfl⟩
  have hcop : Native.Coplanar (a.residueChart.lines l') (a.residueChart.lines k') := by
    by_contra hn
    exact hq (NativeTrioRadicals.intersection_trivial _ _ hn _ hlq hkq)
  obtain ⟨σ,hlσ,hkσ⟩ := hcop
  let σ' := a.residueChart.planes.symm σ
  have he : a.residueChart.planes σ' = σ := a.residueChart.planes.apply_symm_apply σ
  have hlσ' := (a.residueChart.incidence l' σ').mpr (he.symm ▸ hlσ)
  have hkσ' := (a.residueChart.incidence k' σ').mpr (he.symm ▸ hkσ)
  have hxσ := a.string x l σ'.val hxl hlσ'
  have hyσ := a.string y k σ'.val hyk hkσ'
  have hσ : σ'.val = π := a.unique_plane π x y hxπ hyπ hxy.1 hxy.2.1 σ'.val hxσ hyσ
  exact hσ ▸ σ'.property

/-- AS91 (5.7): every common neighbor of a nonadjacent pair in a plane lies
in that same ambient plane. A marker outside the common neighbor's radical
would give a nontrivial native radical intersection; (3.12)(1) then gives a
second plane, which ambient uniqueness identifies with the original one. -/
theorem common_neighbors_in_plane (x y : Point a.P) (π : Plane z)
    (hxy : DistanceTwo a.L x y) (hxπ : OnPlane a.P x π) (hyπ : OnPlane a.P y π)
    (u : Point a.P) (hxu : Adj a.L x u) (hyu : Adj a.L y u) : OnPlane a.P u π := by
  let g := representative u
  have hu : g⁻¹ • u = Cosets.vertex a.P.M 1 := ResidueChart.representative_inv_point u
  have hxu' : Adj a.L (g⁻¹ • x) (Cosets.vertex a.P.M 1) := by
    simpa only [hu] using adj_smul g⁻¹ hxu
  have hyu' : Adj a.L (g⁻¹ • y) (Cosets.vertex a.P.M 1) := by
    simpa only [hu] using adj_smul g⁻¹ hyu
  have hxy' : DistanceTwo a.L (g⁻¹ • x) (g⁻¹ • y) := by
    refine ⟨(MulAction.injective g⁻¹).ne hxy.1,?_,_,hxu',adj_symm hyu'⟩
    intro hh
    have hh' := adj_smul g hh
    exact hxy.2.1 (by simpa only [smul_inv_smul] using hh')
  have hp := a.common_neighbors_in_plane_base (g⁻¹ • x) (g⁻¹ • y) (g⁻¹ • π) hxy'
    (incident_smul g⁻¹ hxπ) (incident_smul g⁻¹ hyπ) hxu' hyu'
  have hh := incident_smul g hp
  simpa only [OnPlane,←hu,smul_inv_smul] using hh
end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.LocalData
