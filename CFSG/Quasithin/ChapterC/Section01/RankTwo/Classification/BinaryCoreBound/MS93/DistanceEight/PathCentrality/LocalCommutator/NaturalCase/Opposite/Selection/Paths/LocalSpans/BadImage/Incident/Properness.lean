module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.Paths.LocalSpans.BadImage.Incident.Commutators

/-!
# Properness of the incident coordinate image

We use the literal image of W ∩ V_u, with W = localZSpan a c and the
original frame marking. Suppose this image were the whole dual space.
The bound [[V_u,Q_u],Q_u] ≤ Z_u ≤ B_c makes every first displacement
fixed modulo B_c. Pairing with the natural edge displacement and using
surjectivity therefore forces that edge displacement to centralize Q_u.

The edge fixed-point identity puts it in Z_u. Edge transitivity then gives
[V_u,Q_u] ≤ Z_u. Thus the supposed full image annihilates a nonidentity
natural edge point, contradicting nondegeneracy. No coordinates on the
full radius or contrary-local hypotheses enter this argument.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1)(1), pp.890–891,
the incident-radius factor in the bad-conjugate display.
-/

public section

open Subgroup Matrix Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.LocalSpans.BadImage
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R} {a c u : Vertex R}
open Escape.PairingControl.Geometry.Selection.Centralizer.Generation.SourceDisplay

/-- A full incident image would make the natural edge displacement fixed. -/
theorem edge_le_of_incident_image_eq_top (common : CommonFacts R source geometry)
    (hc : color R c = false) (hd : (cosetGraph R).dist a c = 2)
    (hb : 2 < geometry.b R) (f : FrameAt a c) (hop : ¬ f.SameOrientation)
    (hcu : Adjacent R c u)
    (hfull : coordinateImage source hc hd hb f hop (V R u) = ⊤) :
    ⁅Z R c, Q R u⁆ ≤ Z R u := by
  have hEU : ⁅Z R c, Q R u⁆ ≤ U R c :=
    Escape.EdgeTransfer.edge_commutator_le_natural hb (moduleFacts common) c u hc hcu
  have hZB : Z R u ≤ B R c (geometry.Z_normal c) :=
    (Escape.EdgeTransfer.edge_Z_le c u hc hcu).trans
      (Escape.EdgeTransfer.Z_le_B hb c hc)
  have hsecond := (radius_second_commutator_le common hc hcu).trans hZB
  have hcentral : ⁅Z R c, Q R u⁆ ≤ centralizer (Q R u : Set (FreeAmalgam R)) := by
    intro w hw q hq
    let w₀ : U R c := ⟨w, hEU hw⟩
    let q₀ : stabilizer R c := ⟨q, hq.2 c (adjacent_symm R hcu)⟩
    let w₁ : U R c := ⟨q * w * q⁻¹,
      le_normalizer_iff.mp (U_normalized c) q q₀.property w w₀.property⟩
    have heq : naturalCoordinates f w₁ = naturalCoordinates f w₀ := by
      apply Multiplicative.toAdd.injective
      apply dotProduct_eq
      intro v
      obtain ⟨x, hx, hpx⟩ := (show Multiplicative.ofAdd v ∈
        coordinateImage source hc hd hb f hop (V R u) from hfull.symm ▸ mem_top _)
      let y : localZSpan R a c := ⟨q⁻¹ * (x : FreeAmalgam R) * q, by
        simpa only [inv_inv] using le_normalizer_iff.mp (localZSpan_normalized R a c)
          q⁻¹ ((stabilizer R c).inv_mem q₀.property) x x.property⟩
      let d : localZSpan R a c := y * x⁻¹
      have hdcomm : (d : FreeAmalgam R) ∈ ⁅V R u, Q R u⁆ := by
        rw [commutator_comm]
        change q⁻¹ * (x : FreeAmalgam R) * q * (x : FreeAmalgam R)⁻¹ ∈ _
        simpa only [commutatorElement_def, inv_inv] using
          commutator_mem_commutator ((Q R u).inv_mem hq)
            (show (x : FreeAmalgam R) ∈ V R u from hx)
      have hfix (r : FreeAmalgam R) (hr : r ∈ Q R u) :
          ⁅r, (d : FreeAmalgam R)⁆ ∈ B R c (geometry.Z_normal c) := by
        rw [commutator_comm] at hsecond
        exact hsecond (commutator_mem_commutator hr hdcomm)
      have hz := fixed_annihilates_edge common hc hd hb f hop hcu d hfix
        (mem_map_of_mem (naturalCoordinates f).toMonoidHom
          (show w₀ ∈ (edgeCommutator R c u).subgroupOf (U R c) from hw))
      change dotProduct (coordinates source hc hd hb f hop d).toAdd
        (naturalCoordinates f w₀).toAdd = 0 at hz
      rw [dotProduct_comm] at hz
      change dotProduct (naturalCoordinates f w₀).toAdd
        (coordinates source hc hd hb f hop (y * x⁻¹)).toAdd = 0 at hz
      rw [map_mul, map_inv, toAdd_mul, toAdd_inv,
        dotProduct_add, dotProduct_neg] at hz
      have hpair : dotProduct (naturalCoordinates f w₁).toAdd
          (coordinates source hc hd hb f hop x).toAdd =
          dotProduct (naturalCoordinates f w₀).toAdd
          (coordinates source hc hd hb f hop x).toAdd := by
        rw [naturalCoordinates_conjugation f q₀ w₀ w₁ rfl]
        change dotProduct
          ((f.naturalU.marking (f.sectionData.projection q₀)).val.mulVec
            (naturalCoordinates f w₀).toAdd) _ = _
        rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
          ← coordinates_inverse_conjugation source hc hd hb f hop q₀ x y rfl,
          dotProduct_comm]
        exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hz)
      simpa only [hpx, toAdd_ofAdd] using hpair
    have he := congrArg Subtype.val ((naturalCoordinates f).injective heq)
    change q * w * q⁻¹ = w at he
    exact (mul_inv_eq_iff_eq_mul.mp he)
  rw [Escape.EdgeTransfer.edge_Z_eq_fixed hb (moduleFacts common) c u hc hcu]
  exact le_inf (hEU.trans (U_le_Z R c)) hcentral

/-- The image of the literal intersection W ∩ V_u is a proper subgroup of
the marked three-dimensional dual space. -/
theorem incident_coordinate_image_ne_top (common : CommonFacts R source geometry)
    (hc : color R c = false) (hd : (cosetGraph R).dist a c = 2)
    (hb : 2 < geometry.b R) (f : FrameAt a c) (hop : ¬ f.SameOrientation)
    (hcu : Adjacent R c u) :
    coordinateImage source hc hd hb f hop (V R u) ≠ ⊤ := by
  intro he
  have hfirst := radius_commutator_le_of_edge_le common hc hcu
    (edge_le_of_incident_image_eq_top common hc hd hb f hop hcu he)
  have hcomm : ⁅localZSpan R a c ⊓ V R u, Q R u⁆ ≤ B R c (geometry.Z_normal c) :=
    (commutator_mono inf_le_right le_rfl).trans (hfirst.trans
      ((Escape.EdgeTransfer.edge_Z_le c u hc hcu).trans
        (Escape.EdgeTransfer.Z_le_B hb c hc)))
  obtain ⟨w, hw, hwE, _⟩ := exists_incident_fixed_point common hc hcu
  have hle : coordinateImage source hc hd hb f hop (V R u) ≤
      Model.annihilator (naturalCoordinates f w) := by
    rintro _ ⟨x, hx, rfl⟩
    exact radius_annihilates_edge_of_commutator common hc hd hb f hop hcu hcomm w hwE x hx
  have hn : naturalCoordinates f w ≠ 1 := by
    intro hh
    exact hw ((naturalCoordinates f).injective (hh.trans (map_one _).symm))
  apply annihilator_ne_top (naturalCoordinates f w) hn
  rw [he] at hle
  exact top_unique hle


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.LocalSpans.BadImage
