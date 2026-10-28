module
public import CFSG.Quasithin.ChapterF.Section05.SourceSystemLocalMaps

/-!
# Transport the local orbit before constructing the source system

An isomorphism of local groups preserving their vertex intersections identifies
their local coset actions. Choose the source edge element to be the image of the
model element carrying the first vertex to the second. It is automatically
outside the source vertex group, and the local edge-set stabilizers correspond.
Thus final assembly needs no separate proof of the local-edge membership field.

The actual F.5 consumer below retains only the vertex and local maps, their
agreement and vertex-intersection marking, the full edge-fixer marking, and the
edge-conjugation identity. Earlier source generation comes from the proved
fusion theorem and the graph-centralizer join.

Source: Aschbacher--Smith F.5.7(2)--(3), printed p.303.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory.GraphUniquenessSystem
namespace CFSG.Quasithin.ChapterF.Section05

private theorem local_orbit_eq_iff {K X G : Type*} [Group K] [MulAction K X] [Group G]
    (U : System K X) (M H : Subgroup G) (e : U.H ≃* H)
    (hv : ∀ a : U.H, (a : K) ∈ U.vertexGroup ↔ (e a : G) ∈ M)
    (a b : U.H) :
    (a : K) • U.x = (b : K) • U.x ↔
      Cosets.vertex M (e a) = Cosets.vertex M (e b) := by
  rw [Cosets.vertex_eq_iff]
  have hh := hv (a⁻¹ * b)
  change ((a : K)⁻¹ * (b : K)) • U.x = U.x ↔ _ at hh
  rw [mul_smul, inv_smul_eq_iff, eq_comm] at hh
  simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] using hh

private theorem local_edge_iff {K X G : Type*} [Group K] [MulAction K X] [Group G]
    (U : System K X) (M H : Subgroup G) (e : U.H ≃* H)
    (hv : ∀ a : U.H, (a : K) ∈ U.vertexGroup ↔ (e a : G) ∈ M)
    (t : U.H) (htx : (t : K) • U.x = U.y) (a : U.H) :
    (a : K) ∈ U.edgeSetGroup ↔
      (e a : G) ∈ edgeStabilizer G (Cosets.vertex M 1) (Cosets.vertex M (e t)) := by
  have hx := local_orbit_eq_iff U M H e hv a 1
  have hy := local_orbit_eq_iff U M H e hv (a*t) t
  have hxy := local_orbit_eq_iff U M H e hv a t
  have hyx := local_orbit_eq_iff U M H e hv (a*t) 1
  simp only [Subgroup.coe_one, one_smul, map_one, Subgroup.coe_mul, mul_smul,
    htx, map_mul] at hx hy hxy hyx
  change ((a : K) • U.x = U.x ∧ (a : K) • U.y = U.y) ∨
      ((a : K) • U.x = U.y ∧ (a : K) • U.y = U.x) ↔ _
  change _ ↔
    (Cosets.vertex M ((e a : G)*1) = Cosets.vertex M 1 ∧
      Cosets.vertex M ((e a : G)*(e t : G)) = Cosets.vertex M (e t)) ∨
    (Cosets.vertex M ((e a : G)*1) = Cosets.vertex M (e t) ∧
      Cosets.vertex M ((e a : G)*(e t : G)) = Cosets.vertex M 1)
  simp only [mul_one]
  exact or_congr (and_congr hx hy) (and_congr hxy hyx)

open Theory.GroupTheory GreenBook.LieModels.UnitaryFour ExceptionalLocal
open OmegaSixThree.OrthogonalityGraph (modelSystem)
local notation "hn" => Nat.le_refl 1
local notation "O" => OmegaSixThree.omegaPlusSixThree
variable {G G0 : Type*} [Group G] [Group G0] [Finite G] [IsSimpleGroup G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
  (R : Sylow 2 (C c i)) (hR : Tf c i ≤ (R : Subgroup (C c i)))
  (hcentral : C c i = Rimage c i R ⊔ D c i)
  (eV : modelSystem.vertexGroup ≃* i.range) (eH : modelSystem.H ≃* H c i)
  (hagree : ∀ (g : O) (hgH : g∈modelSystem.H) (hgv : g∈modelSystem.vertexGroup),
    (eV ⟨g,hgv⟩:G)=(eH ⟨g,hgH⟩:G))
  (hlocalV : ∀a : modelSystem.H, (a:O)∈modelSystem.vertexGroup ↔ (eH a:G)∈i.range)
  (t : modelSystem.H) (htx : (t:O) • modelSystem.x = modelSystem.y)
  (hedge : ∀a : modelSystem.vertexGroup, (a:O)∈modelSystem.edgeGroup ↔
    (eV a:G)∈i.range ⊓ i.range.comap (MulAut.conj (eH t:G)⁻¹).toMonoidHom)

include hlocalV htx in
omit [Finite G] [IsSimpleGroup G] in
private theorem local_image_outside : (eH t:G) ∉ i.range := by
  intro hm
  have ht : (t:O) • modelSystem.x = modelSystem.x := (hlocalV t).mpr hm
  exact modelSystem.adjacent.ne (ht.symm.trans htx)

/-- The actual source system with its edge chosen through the local comparison. -/
def sourceCosetSystemOfLocalOrbit : System G (G ⧸ i.range) :=
  sourceCosetSystemOfMaps c i z h R hR hcentral (eH t) (eH t).property
    (by exact local_image_outside c i eH hlocalV t htx) eV eH hagree hlocalV hedge
    (by exact local_edge_iff modelSystem i.range (H c i) eH hlocalV t htx)

/-- The local orbit transport discharges the local-edge field of the similarity. -/
def sourceCosetSimilarityOfLocalOrbit : Similarity modelSystem
    (sourceCosetSystemOfLocalOrbit c i z h R hR hcentral eV eH hagree hlocalV t htx hedge) :=
  sourceCosetSimilarityOfMaps c i z h R hR hcentral (eH t) (eH t).property
    (by exact local_image_outside c i eH hlocalV t htx) eV eH hagree hlocalV hedge
    (by exact local_edge_iff modelSystem i.range (H c i) eH hlocalV t htx)

/-- The original ambient endpoint without an independent local-edge premise. -/
theorem source_ambient_of_local_orbit_maps
    (hs : (sourceCosetSimilarityOfLocalOrbit c i z h R hR hcentral eV eH
      hagree hlocalV t htx hedge).IsEquivalence) :
    Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 3)) :=
  CompletionRecognition.source_ambient_of_model_equivalence i _
    (sourceCosetSimilarityOfLocalOrbit c i z h R hR hcentral eV eH
      hagree hlocalV t htx hedge) hs

end CFSG.Quasithin.ChapterF.Section05
