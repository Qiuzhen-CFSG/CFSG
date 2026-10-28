module

public import Theory.GroupTheory.Recognition.JankoFour.LocalGeometry
public import Theory.GroupTheory.Recognition.JankoFour.LocalGeometry.LocalSubgroups
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# The literal cosets and transported radicals in the AS91 geometry

All three sorts carry the original left action. The point radical is the
conjugate of the fixed Todd subgroup; the plane marker is the conjugate of
the original involution. The definitions use a representative only to choose
coordinates. Representative independence and equivariance are proved below.

Source: Aschbacher–Segev (1991), §§5–7. In particular the stabilizer at gM
uses conjugation by g⁻¹ in a comap.
-/

@[expose] public section

namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase

open Subgroup GraphUniquenessSystem LocalGeometry LocalGeometry.LocalSubgroups
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G] {z : G}

abbrev Point (P : PointData z) := Cosets.Vertex P.M
abbrev Line {P : PointData z} (L : LineData z P) := Cosets.Vertex L.G₂
abbrev Plane (z : G) := Cosets.Vertex (centralizer z)

def OnLine {P : PointData z} (L : LineData z P) (x : Point P) (l : Line L) : Prop :=
  Cosets.Incident P.M L.G₂ x l

def OnPlane (P : PointData z) (x : Point P) (π : Plane z) : Prop :=
  Cosets.Incident P.M (centralizer z) x π

def LineOnPlane {P : PointData z} (L : LineData z P) (l : Line L) (π : Plane z) : Prop :=
  Cosets.Incident L.G₂ (centralizer z) l π

def Adj {P : PointData z} (L : LineData z P) (x y : Point P) : Prop :=
  Cosets.Collinear P.M L.G₂ x y

def graph {P : PointData z} (L : LineData z P) : SimpleGraph (Point P) where
  Adj := Adj L
  symm := ⟨by
    rintro a b ⟨hne, l, ha, hb⟩
    exact ⟨hne.symm, l, hb, ha⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem adj_symm {P : PointData z} {L : LineData z P} {x y : Point P}
    (h : Adj L x y) : Adj L y x := (show (graph L).Adj x y from h).symm

def Coplanar {P : PointData z} (L : LineData z P) (l m : Line L) : Prop :=
  ∃ π, LineOnPlane L l π ∧ LineOnPlane L m π

def DistanceTwo {P : PointData z} (L : LineData z P) (x y : Point P) : Prop :=
  x ≠ y ∧ ¬ Adj L x y ∧ ∃ u, Adj L x u ∧ Adj L u y

/-- Only the distance-two pairs which share a plane: AS91's Δ₁². -/
def PlaneDistanceTwo {P : PointData z} (L : LineData z P) (x y : Point P) : Prop :=
  DistanceTwo L x y ∧ ∃ π, OnPlane P x π ∧ OnPlane P y π

omit [Finite G] in
theorem incident_smul {A B : Subgroup G} {a : Cosets.Vertex A}
    {b : Cosets.Vertex B} (g : G) (h : Cosets.Incident A B a b) :
    Cosets.Incident A B (g • a) (g • b) := by
  obtain ⟨k, rfl, rfl⟩ := h
  exact ⟨g * k, rfl, rfl⟩

omit [Finite G] in
theorem incident_smul_iff {A B : Subgroup G} (a : Cosets.Vertex A)
    (b : Cosets.Vertex B) (g : G) :
    Cosets.Incident A B (g • a) (g • b) ↔ Cosets.Incident A B a b := by
  constructor
  · intro h
    simpa only [inv_smul_smul] using incident_smul g⁻¹ h
  · exact incident_smul g

theorem adj_smul {P : PointData z} {L : LineData z P} {x y : Point P}
    (g : G) (h : Adj L x y) : Adj L (g • x) (g • y) := by
  obtain ⟨hne, l, hx, hy⟩ := h
  exact ⟨fun he => hne ((MulAction.injective g) he), g • l,
    incident_smul g hx, incident_smul g hy⟩

/-- A chosen representative, with no change to the quotient convention. -/
noncomputable def representative {A : Subgroup G} (a : Cosets.Vertex A) : G := a.out

omit [Finite G] in
@[simp] theorem vertex_representative {A : Subgroup G} (a : Cosets.Vertex A) :
    Cosets.vertex A (representative a) = a := Quotient.out_eq' a

noncomputable def coreAt (P : PointData z) (x : Point P) : Subgroup G :=
  P.E.comap (MulAut.conj (representative x)⁻¹).toMonoidHom

noncomputable def marker (π : Plane z) : G :=
  representative π * z * (representative π)⁻¹

private theorem E_conj_mem_iff (P : PointData z) (m : G) (hm : m ∈ P.M) (a : G) :
    m * a * m⁻¹ ∈ P.E ↔ a ∈ P.E := by
  have hn := P.E_normal
  have forward (m : G) (hm : m ∈ P.M) (a : G) (ha : a ∈ P.E) :
      m * a * m⁻¹ ∈ P.E := by
    exact hn.conj_mem ⟨a, P.E_le ha⟩ ha ⟨m, hm⟩
  constructor
  · intro ha
    simpa only [inv_inv, inv_mul_cancel_left, mul_assoc, mul_inv_cancel_right,
      inv_mul_cancel, mul_one] using
      forward m⁻¹ (P.M.inv_mem hm) (m * a * m⁻¹) ha
  · exact forward m hm a

/-- The point radical is independent of the chosen representative. -/
theorem coreAt_vertex (P : PointData z) (g : G) :
    coreAt P (Cosets.vertex P.M g) = P.E.comap (MulAut.conj g⁻¹).toMonoidHom := by
  let r := representative (Cosets.vertex P.M g)
  have hm : r⁻¹ * g ∈ P.M :=
    (Cosets.vertex_eq_iff P.M r g).mp (vertex_representative _)
  ext a
  change r⁻¹ * a * (r⁻¹)⁻¹ ∈ P.E ↔ g⁻¹ * a * (g⁻¹)⁻¹ ∈ P.E
  simpa only [inv_inv] using
    (show r⁻¹ * a * r ∈ P.E ↔ g⁻¹ * a * g ∈ P.E from by
      have he : (r⁻¹ * g) * (g⁻¹ * a * g) * (r⁻¹ * g)⁻¹ = r⁻¹ * a * r := by group
      rw [← he]
      exact E_conj_mem_iff P _ hm _)

theorem coreAt_smul (P : PointData z) (g : G) (x : Point P) :
    coreAt P (g • x) = (coreAt P x).comap (MulAut.conj g⁻¹).toMonoidHom := by
  induction x using QuotientGroup.induction_on with
  | H k =>
    change coreAt P (Cosets.vertex P.M (g * k)) =
      (coreAt P (Cosets.vertex P.M k)).comap (MulAut.conj g⁻¹).toMonoidHom
    rw [coreAt_vertex, coreAt_vertex]
    ext a
    change (g * k)⁻¹ * a * ((g * k)⁻¹)⁻¹ ∈ P.E ↔
      k⁻¹ * (g⁻¹ * a * (g⁻¹)⁻¹) * (k⁻¹)⁻¹ ∈ P.E
    simp only [mul_inv_rev, inv_inv, mul_assoc]

theorem coreAt_le_stabilizer (P : PointData z) (x : Point P) :
    coreAt P x ≤ MulAction.stabilizer G x := by
  rw [← vertex_representative x, coreAt_vertex, Cosets.stabilizer_vertex]
  exact Subgroup.comap_mono P.E_le

omit [Finite G] in
/-- The plane marker is the conjugate of the original z, for every representative. -/
theorem marker_vertex (g : G) : marker (Cosets.vertex (centralizer z) g) = g * z * g⁻¹ := by
  let r := representative (Cosets.vertex (centralizer z) g)
  have hm : r⁻¹ * g ∈ centralizer z :=
    (Cosets.vertex_eq_iff (centralizer z) r g).mp (vertex_representative _)
  have hc := mem_centralizer_singleton_iff.mp hm
  change r * z * r⁻¹ = g * z * g⁻¹
  calc
    r * z * r⁻¹ = r * (z * (r⁻¹ * g)) * g⁻¹ := by group
    _ = r * ((r⁻¹ * g) * z) * g⁻¹ := by rw [hc]
    _ = g * z * g⁻¹ := by group

omit [Finite G] in
theorem marker_smul (g : G) (π : Plane z) : marker (g • π) = g * marker π * g⁻¹ := by
  induction π using QuotientGroup.induction_on with
  | H k =>
    change marker (Cosets.vertex (centralizer z) (g * k)) =
      g * marker (Cosets.vertex (centralizer z) k) * g⁻¹
    rw [marker_vertex, marker_vertex]
    group

end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
