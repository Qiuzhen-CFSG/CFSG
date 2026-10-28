module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Endgame
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.ResidueCharts
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.FarOrbit

/-!
# The literal ambient far-line orbit adapter

The checked native M₂₄ far-line orbit statement transfers to the actual left-coset
geometry through the same Todd projection used by the source residue charts.
The proof keeps one lift for both line images and the plane stabilizer, then
translates an arbitrary point flag to the base point by its chosen coset
representative. The exact `Input.FarLineTransitive` condition and AS91 (7.8) follow from
the unchanged earlier-source `Input`. B2 and the component-distance bound
remain explicit in the final base adapter.

Source: Aschbacher–Segev (1991), §3.8 and §7.8, pp.595, 605.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
open GraphUniquenessSystem
open Sporadic.Mathieu
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}
namespace Input
variable (d : Input h)

theorem coplanar_iff_native {x : Point d.P}
    (l m : {l : Line d.L // OnLine d.L x l}) :
    Coplanar d.L l.val m.val ↔ Native.Coplanar (d.residue.linesAt x l) (d.residue.linesAt x m) := by
  constructor
  · rintro ⟨π,hl,hm⟩
    have hx := d.string x l.val π l.property hl
    exact ⟨d.residue.planesAt x ⟨π,hx⟩,
      (d.residue.incidenceAt x l ⟨π,hx⟩).mp hl,
      (d.residue.incidenceAt x m ⟨π,hx⟩).mp hm⟩
  · rintro ⟨π,hl,hm⟩
    obtain ⟨π,rfl⟩ := (d.residue.planesAt x).surjective π
    exact ⟨π.val,(d.residue.incidenceAt x l π).mpr hl,
      (d.residue.incidenceAt x m π).mpr hm⟩

theorem coplanar_iff_native_base
    (l m : {l : Line d.L // OnLine d.L (Cosets.vertex d.P.M 1) l}) :
    Coplanar d.L l.val m.val ↔ Native.Coplanar (d.residue.lines l) (d.residue.lines m) := by
  constructor
  · rintro ⟨π,hl,hm⟩
    have hx := d.string _ l.val π l.property hl
    exact ⟨d.residue.planes ⟨π,hx⟩,
      (d.residue.incidence l ⟨π,hx⟩).mp hl,(d.residue.incidence m ⟨π,hx⟩).mp hm⟩
  · rintro ⟨π,hl,hm⟩
    obtain ⟨π,rfl⟩ := d.residue.planes.surjective π
    exact ⟨π.val,(d.residue.incidence l π).mpr hl,(d.residue.incidence m π).mpr hm⟩

theorem planeLineClose_iff_native_base
    (π : {π : Plane z // OnPlane d.P (Cosets.vertex d.P.M 1) π})
    (l : {l : Line d.L // OnLine d.L (Cosets.vertex d.P.M 1) l}) :
    d.planeLineClose π.val (Cosets.vertex d.P.M 1) l.val ↔
      Native.NearPlane (d.residue.planes π) (d.residue.lines l) := by
  constructor
  · rintro ⟨k,hxk,hkπ,hkl⟩
    exact ⟨d.residue.lines ⟨k,hxk⟩,(d.residue.incidence ⟨k,hxk⟩ π).mp hkπ,
      (d.coplanar_iff_native_base ⟨k,hxk⟩ l).mp hkl⟩
  · rintro ⟨k,hkπ,hkl⟩
    obtain ⟨k,rfl⟩ := d.residue.lines.surjective k
    exact ⟨k.val,k.property,(d.residue.incidence k π).mpr hkπ,
      (d.coplanar_iff_native_base k l).mpr hkl⟩

theorem planeLineClose_smul {π : Plane z} {x : Point d.P} {l : Line d.L}
    (g : G) (hc : d.planeLineClose π x l) :
    d.planeLineClose (g • π) (g • x) (g • l) := by
  obtain ⟨k,hxk,hkπ,σ,hkσ,hlσ⟩ := hc
  exact ⟨g • k,incident_smul g hxk,incident_smul g hkπ,
    g • σ,incident_smul g hkσ,incident_smul g hlσ⟩

theorem farLineTransitive_base_of_native (native : Native.FarTransitive)
    (π : {π : Plane z // OnPlane d.P (Cosets.vertex d.P.M 1) π})
    (l m : {l : Line d.L // OnLine d.L (Cosets.vertex d.P.M 1) l})
    (hl : ¬ d.planeLineClose π.val (Cosets.vertex d.P.M 1) l.val)
    (hm : ¬ d.planeLineClose π.val (Cosets.vertex d.P.M 1) m.val) :
    ∃ g : G, g • Cosets.vertex d.P.M 1 = Cosets.vertex d.P.M 1 ∧
      g • π.val = π.val ∧ g • l.val = m.val := by
  obtain ⟨a,haπ,hal⟩ := native (d.residue.planes π) (d.residue.lines l) (d.residue.lines m)
    (fun hn => hl ((d.planeLineClose_iff_native_base π l).mpr hn))
    (fun hn => hm ((d.planeLineClose_iff_native_base π m).mpr hn))
  let b : d.P.M := d.P.toddEquiv (SemidirectProduct.inr a)
  have hb : d.P.projection b = a := by
    change (d.P.toddEquiv.symm (d.P.toddEquiv (SemidirectProduct.inr a))).right = a
    rw [d.P.toddEquiv.symm_apply_apply]
    rfl
  have hbx : (b : G) • Cosets.vertex d.P.M 1 = Cosets.vertex d.P.M 1 := by
    simp [b.property]
  let π' : {π : Plane z // OnPlane d.P (Cosets.vertex d.P.M 1) π} :=
    ⟨(b : G) • π.val, by simpa only [OnPlane,OnLine,hbx] using incident_smul (b : G) π.property⟩
  let l' : {l : Line d.L // OnLine d.L (Cosets.vertex d.P.M 1) l} :=
    ⟨(b : G) • l.val, by simpa only [OnPlane,OnLine,hbx] using incident_smul (b : G) l.property⟩
  have hp := d.residue.planes_equivariant b π π' rfl
  have hl' := d.residue.lines_equivariant b l l' rfl
  rw [hb,haπ] at hp
  rw [hb,hal] at hl'
  exact ⟨b,hbx,congrArg Subtype.val (d.residue.planes.injective (Native.plane_parts_injective hp)),
    congrArg Subtype.val (d.residue.lines.injective (Native.line_parts_injective hl'))⟩

/-- The exact ambient far-line orbit follows from the native statement
under the original Todd projection and literal left-coset action. -/
theorem farLineTransitive_of_native (native : Native.FarTransitive) : d.FarLineTransitive := by
  intro π x hxπ l m hxl hxm hl hm
  let r := representative x
  have hr : r⁻¹ • x = Cosets.vertex d.P.M 1 := ResidueChart.representative_inv_point x
  let π' : {π : Plane z // OnPlane d.P (Cosets.vertex d.P.M 1) π} :=
    ⟨r⁻¹ • π, by simpa only [OnPlane,OnLine,hr] using incident_smul r⁻¹ hxπ⟩
  let l' : {l : Line d.L // OnLine d.L (Cosets.vertex d.P.M 1) l} :=
    ⟨r⁻¹ • l, by simpa only [OnPlane,OnLine,hr] using incident_smul r⁻¹ hxl⟩
  let m' : {l : Line d.L // OnLine d.L (Cosets.vertex d.P.M 1) l} :=
    ⟨r⁻¹ • m, by simpa only [OnPlane,OnLine,hr] using incident_smul r⁻¹ hxm⟩
  have hrx : r • Cosets.vertex d.P.M 1 = x := by rw [←hr,smul_inv_smul]
  have hl' : ¬ d.planeLineClose π'.val (Cosets.vertex d.P.M 1) l'.val := by
    intro hc
    have hc' := d.planeLineClose_smul r hc
    exact hl (by simpa only [π',l',smul_inv_smul,hrx] using hc')
  have hm' : ¬ d.planeLineClose π'.val (Cosets.vertex d.P.M 1) m'.val := by
    intro hc
    have hc' := d.planeLineClose_smul r hc
    exact hm (by simpa only [π',m',smul_inv_smul,hrx] using hc')
  obtain ⟨g,hgx,hgπ,hgl⟩ := d.farLineTransitive_base_of_native native π' l' m' hl' hm'
  refine ⟨r*g*r⁻¹,?_,?_,?_⟩
  · simp only [mul_smul,hr,hgx,hrx]
  · have hp := congrArg (r • ·) hgπ
    simpa only [π',mul_smul,smul_inv_smul] using hp
  · have hp := congrArg (r • ·) hgl
    simpa only [l',m',mul_smul,smul_inv_smul] using hp

/-- The native forest certificate supplies the actual far-line orbit at every
point-plane flag, under the original Todd marking. -/
theorem farLineTransitive : d.FarLineTransitive :=
  d.farLineTransitive_of_native Native.FarOrbit.far_transitive

/-- AS91 (7.8), with no later-source orbit premise remaining. -/
theorem marker_fixed_iff_planeLineClose_of_input
    {π : Plane z} {x y : Point d.P} (hxπ : OnPlane d.P x π) (hxy : Adj d.L x y)
    {l : Line d.L} (hxl : OnLine d.L x l) (hyl : OnLine d.L y l) :
    marker π • y = y ↔ d.planeLineClose π x l :=
  d.marker_fixed_iff_planeLineClose d.farLineTransitive hxπ hxy hxl hyl

/-- B3 now needs only the component-distance bound (7.6.2). -/
theorem tripleNeighbor_of_component (close : d.ComponentClose) : d.TripleNeighbor :=
  d.tripleNeighbor_of_far_and_component d.farLineTransitive close

/-- The actual cycle-base consumer with the native orbit premise discharged.
B2 and (7.6.2) remain obligations of this source family. -/
theorem isBase_of_bridge_componentClose (bridge : d.Bridge) (close : d.ComponentClose) :
    d.system.IsBase :=
  d.isBase_of_relation_conditions bridge (d.tripleNeighbor_of_component close)

end Input
end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
