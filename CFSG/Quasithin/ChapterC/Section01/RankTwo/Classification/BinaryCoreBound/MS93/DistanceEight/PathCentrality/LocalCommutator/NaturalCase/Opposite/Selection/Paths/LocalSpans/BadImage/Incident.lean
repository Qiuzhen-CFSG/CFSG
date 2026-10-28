module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.Paths.LocalSpans.BadImage.Incident.Properness
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Module.ZMod

/-!
# An incident natural point annihilating the radius image

For the actual intersection W ∩ V_u, its orthogonal complement in U_c is
normalized by Q_u. This follows from the opposite conjugation formulas with
the frame's original marking. If the image is proper, elementary duality
makes the orthogonal complement nontrivial. It is a normal subgroup of the
finite two-group Q_u, so it contains a nonidentity point centralized by Q_u.

The properness theorem in Incident.Properness discharges the premise using
the second-commutator bound and edge transitivity. The resulting witness
annihilates the literal incident coordinate image and is centralized by Q_u.
Both the subgroup inclusion and pointwise pairing are exported for the
bad-conjugate assembly. No order-four or parabolic-selection input is needed.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1)(1), printed pp.890–891,
the bad-conjugate display multiplied by V_(alpha+3).
-/

public section

open Subgroup Matrix Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.LocalSpans.BadImage
open Escape.Propagation.Backward.Products.Selection.Choices (Space)
open Escape.PairingControl.Geometry.Selection.Centralizer.Generation.SourceDisplay

private theorem proper_image_has_annihilator (H : Subgroup Space) (hH : H ≠ ⊤) :
    ∃ w : Space, w ≠ 1 ∧ H ≤ Model.annihilator w := by
  let P := AddSubgroup.toZModSubmodule 2 (AddSubgroup.toSubgroup.symm H)
  have hP : P < ⊤ := lt_top_iff_ne_top.mpr (by
    intro he
    apply hH
    apply top_unique
    intro x _
    exact (show x.toAdd ∈ P from he.symm ▸ Submodule.mem_top))
  obtain ⟨f, hf, hzero⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hP inferInstance
  let w : Space := Multiplicative.ofAdd (fun i => f (Pi.single i 1))
  have hrow (x : Space) : dotProduct w.toAdd x.toAdd = f x.toAdd := by
    have he := congrArg f ((Pi.basisFun (ZMod 2) (Fin 3)).sum_repr x.toAdd)
    simpa [w, dotProduct, map_sum, mul_comm] using he
  refine ⟨w, ?_, ?_⟩
  · intro hw
    apply hf
    apply LinearMap.ext
    intro x
    have he := hrow (Multiplicative.ofAdd x)
    simpa [hw] using he.symm
  · intro x hx
    change dotProduct w.toAdd x.toAdd = 0
    rw [hrow]
    exact hzero.le (Submodule.mem_map_of_mem (show x.toAdd ∈ P from hx))

private def orthogonal (H : Subgroup Space) : Subgroup Space :=
  ⨅ x : H, Model.annihilator x.val

private theorem mem_orthogonal (H : Subgroup Space) (w : Space) :
    w ∈ orthogonal H ↔ ∀ x ∈ H, dotProduct w.toAdd x.toAdd = 0 := by
  simp only [orthogonal, mem_iInf]
  change (∀ x : H, dotProduct x.val.toAdd w.toAdd = 0) ↔ _
  simp only [Subtype.forall, dotProduct_comm]

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R} {a c u : Vertex R}

/-- A proper image of the literal incident intersection has a nonzero
annihilating natural point fixed by Q_u. The image properness is an explicit
geometric premise, discharged below by incident_coordinate_image_ne_top. -/
theorem exists_incident_annihilator_of_image_ne_top
    (hc : color R c = false) (hd : (cosetGraph R).dist a c = 2)
    (hb : 2 < geometry.b R) (f : FrameAt a c) (hop : ¬ f.SameOrientation)
    (hcu : Adjacent R c u)
    (hproper : coordinateImage source hc hd hb f hop (V R u) ≠ ⊤) :
    ∃ w : U R c, w ≠ 1 ∧
      (w : FreeAmalgam R) ∈ centralizer (Q R u : Set (FreeAmalgam R)) ∧
      coordinateImage source hc hd hb f hop (V R u) ≤
        Model.annihilator (naturalCoordinates f w) := by
  let H := coordinateImage source hc hd hb f hop (V R u)
  let A := (orthogonal H).comap (naturalCoordinates f).toMonoidHom
  let E := A.map (U R c).subtype
  let T := Q R u
  have hEU : E ≤ U R c := map_subtype_le _
  have hUT : U R c ≤ T := (U_le_Z R c).trans
    (Escape.EdgeTransfer.edge_Z_le_Q hb c u hc hcu)
  have hET : E ≤ T := hEU.trans hUT
  have hTS : T ≤ stabilizer R c := fun _ hq => hq.2 c (adjacent_symm R hcu)
  have hmem (w : U R c) : w ∈ A ↔ H ≤ Model.annihilator (naturalCoordinates f w) :=
    mem_orthogonal H _
  have hnormal : T ≤ normalizer (E : Set (FreeAmalgam R)) := by
    apply le_normalizer_iff.mpr
    intro q hq z hz
    obtain ⟨w, hw, rfl⟩ := hz
    let q₀ : stabilizer R c := ⟨q, hTS hq⟩
    let w' : U R c := ⟨q * (w : FreeAmalgam R) * q⁻¹,
      le_normalizer_iff.mp (U_normalized c) q q₀.property w w.property⟩
    refine ⟨w', (hmem w').mpr ?_, rfl⟩
    rintro _ ⟨x, hx, rfl⟩
    let y : localZSpan R a c := ⟨q⁻¹ * (x : FreeAmalgam R) * q, by
      simpa only [inv_inv] using le_normalizer_iff.mp (localZSpan_normalized R a c)
        q⁻¹ ((stabilizer R c).inv_mem q₀.property) x x.property⟩
    have hy : (y : FreeAmalgam R) ∈ V R u := by
      simpa only [inv_inv] using le_normalizer_iff.mp (DistanceEight.V_normalized R u)
        q⁻¹ ((stabilizer R u).inv_mem hq.1) x hx
    have hzero := (hmem w).mp hw (mem_map_of_mem
      (coordinates source hc hd hb f hop) (show y ∈ (V R u).subgroupOf (localZSpan R a c) from hy))
    change dotProduct (naturalCoordinates f w).toAdd
      (coordinates source hc hd hb f hop y).toAdd = 0 at hzero
    change dotProduct (naturalCoordinates f w').toAdd
      (coordinates source hc hd hb f hop x).toAdd = 0
    rw [naturalCoordinates_conjugation f q₀ w w' rfl]
    change dotProduct
      ((f.naturalU.marking (f.sectionData.projection q₀)).val.mulVec
        (naturalCoordinates f w).toAdd) (coordinates source hc hd hb f hop x).toAdd = 0
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      ← coordinates_inverse_conjugation source hc hd hb f hop q₀ x y rfl,
      dotProduct_comm]
    exact hzero
  have hEne : E ≠ ⊥ := by
    obtain ⟨v, hv, hvan⟩ := proper_image_has_annihilator H hproper
    let w := (naturalCoordinates f).symm v
    have hw : w ∈ A := (hmem w).mpr (by simpa only [w, MulEquiv.apply_symm_apply] using hvan)
    intro he
    have hwone : w = 1 := Subtype.ext (he.le (mem_map_of_mem (U R c).subtype hw))
    apply hv
    have hh := congrArg (naturalCoordinates f) hwone
    simpa only [w, MulEquiv.apply_symm_apply, map_one] using hh
  let := finite_stabilizer R c
  let : Finite T := Finite.of_injective (inclusion hTS) (inclusion_injective _)
  let : Fact (IsPGroup 2 T) := ⟨Escape.EdgeTransfer.edge_kernel_two source c u hc hcu⟩
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Nontrivial E := (nontrivial_iff_ne_bot E).mpr hEne
  let : Nontrivial (E.subgroupOf T) := (subgroupOfEquivOfLe hET).toEquiv.nontrivial
  let : (E.subgroupOf T).Normal := normal_subgroupOf_of_le_normalizer hnormal
  obtain ⟨z, hzne, hzfix⟩ := exists_nontrivial_center_mem_normal (E.subgroupOf T) (p := 2)
  obtain ⟨w, hw, he⟩ := z.property
  change (w : FreeAmalgam R) = ((z : T) : FreeAmalgam R) at he
  refine ⟨w, ?_, ?_, (hmem w).mp hw⟩
  · intro hwone
    apply hzne
    exact Subtype.ext (Subtype.ext (by simpa only [hwone, coe_one] using he.symm))
  · intro q hq
    rw [he]
    exact congrArg Subtype.val ((mem_center_iff.mp hzfix) ⟨q,hq⟩)

/-- A nonidentity natural point fixed by the incident kernel annihilates the
literal image of W ∩ V_u. This supplies the incident factor in the source's
bad-conjugate display. -/
theorem exists_incident_annihilator (common : CommonFacts R source geometry)
    (hc : color R c = false) (hd : (cosetGraph R).dist a c = 2)
    (hb : 2 < geometry.b R) (f : FrameAt a c) (hop : ¬ f.SameOrientation)
    (hcu : Adjacent R c u) :
    ∃ w : U R c, w ≠ 1 ∧
      (w : FreeAmalgam R) ∈ centralizer (Q R u : Set (FreeAmalgam R)) ∧
      coordinateImage source hc hd hb f hop (V R u) ≤
        Model.annihilator (naturalCoordinates f w) :=
  exists_incident_annihilator_of_image_ne_top hc hd hb f hop hcu
    (incident_coordinate_image_ne_top common hc hd hb f hop hcu)

/-- The pointwise incident-radius pairing, with the actual frame marking
and the literal membership x ∈ V_u inside W. -/
theorem exists_incident_radius_pairing (common : CommonFacts R source geometry)
    (hc : color R c = false) (hd : (cosetGraph R).dist a c = 2)
    (hb : 2 < geometry.b R) (f : FrameAt a c) (hop : ¬ f.SameOrientation)
    (hcu : Adjacent R c u) :
    ∃ w : U R c, w ≠ 1 ∧
      (w : FreeAmalgam R) ∈ centralizer (Q R u : Set (FreeAmalgam R)) ∧
      ∀ x : localZSpan R a c, (x : FreeAmalgam R) ∈ V R u →
        dotProduct (naturalCoordinates f w).toAdd
          (coordinates source hc hd hb f hop x).toAdd = 0 := by
  obtain ⟨w, hw, hfix, hann⟩ := exists_incident_annihilator common hc hd hb f hop hcu
  exact ⟨w, hw, hfix, fun x hx => hann (mem_map_of_mem
    (coordinates source hc hd hb f hop) hx)⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.LocalSpans.BadImage
