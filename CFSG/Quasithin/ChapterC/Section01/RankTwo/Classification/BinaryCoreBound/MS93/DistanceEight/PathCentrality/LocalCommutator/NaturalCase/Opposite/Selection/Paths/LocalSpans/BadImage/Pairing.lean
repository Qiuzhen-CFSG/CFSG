module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.Paths.LocalSpans.Coordinates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.Paths.LocalSpans.BadImage.Model

/-!
# The natural pairing for the original opposite-frame orbit

The natural coordinates use exactly the frame's marking. Fixation in W/B_c
annihilates the corresponding natural displacement. In particular every
original conjugate seed annihilates its own transported edge displacement,
by the already proved fixation modulo Z_c. No full-radius natural section or
contrary-local facts enter this argument.

The commutator calculation adapts the independent dual-action calculation in
SourceDisplay/RadiusCoordinates, keeping the smaller actual span W throughout.
Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1)(1), pp.890–891.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.LocalSpans.BadImage
open RankOnePairing
open Escape.Propagation.Backward.Products.Selection.Choices (Space modelAction planeFixer)
open Escape.PairingControl.Geometry.Selection.Centralizer.Generation.SourceDisplay

private def pairingMap {G : Type*} [Group G] {π : G →* SL} {U : Subgroup G}
    (n : NaturalFactor π ⊤ U ⊥) (v : Fin 3 → ZMod 2) : U →* Multiplicative (ZMod 2) where
  toFun u := Multiplicative.ofAdd (dotProduct v (n.coordinates u).toAdd)
  map_one' := by simp
  map_mul' u w := by
    change Multiplicative.ofAdd (dotProduct v (n.coordinates (u*w)).toAdd) = _
    rw [map_mul, toAdd_mul, dotProduct_add]
    rfl

private theorem fixed_annihilates_commutator {G : Type*} [Group G] {π : G →* SL}
    {U W B : Subgroup G} (n : NaturalFactor π ⊤ U ⊥)
    (d : DualFactor π ⊤ W B U n) (A : Subgroup G) (x : W)
    (hfixed : ∀ a ∈ A, ⁅a, (x : G)⁆ ∈ B) :
    ∀ u ∈ ⁅U, A⁆, ∀ hu : u ∈ U,
      dotProduct (d.coordinates x).toAdd (n.coordinates ⟨u, hu⟩).toAdd = 0 := by
  let v := (d.coordinates x).toAdd
  let k := pairingMap n v
  have hcomm : ⁅U, A⁆ ≤ k.ker.map U.subtype := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro a ha u hu
    let u₀ : U := ⟨u, hu⟩
    let u₁ : U := ⟨a * u * a⁻¹, le_normalizer_iff.mp n.normalized a (mem_top _) u hu⟩
    let y : W := ⟨a⁻¹ * (x : G) * a,
      by simpa using le_normalizer_iff.mp d.normalized a⁻¹ (mem_top _) (x : G) x.property⟩
    have hy : y * x⁻¹ ∈ d.coordinates.ker := by
      rw [d.kernel]
      change a⁻¹ * (x : G) * a * (x : G)⁻¹ ∈ B
      simpa only [commutatorElement_def, inv_inv] using hfixed a⁻¹ (A.inv_mem ha)
    have he : d.coordinates y = d.coordinates x := by
      apply mul_inv_eq_one.mp
      simpa only [MonoidHom.mem_ker, map_mul, map_inv] using hy
    have hact := d.action a⁻¹ (mem_top _) x y (by simp only [inv_inv]; rfl)
    rw [he] at hact
    simp only [map_inv, inv_inv] at hact
    refine ⟨u₁ * u₀⁻¹, ?_, rfl⟩
    change k (u₁ * u₀⁻¹) = 1
    rw [map_mul, map_inv, mul_inv_eq_one]
    change Multiplicative.ofAdd (dotProduct v (n.coordinates u₁).toAdd) =
      Multiplicative.ofAdd (dotProduct v (n.coordinates u₀).toAdd)
    congr 1
    rw [n.action a (mem_top _) u₀ u₁ rfl, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose, ← hact]
  intro u hu hU
  obtain ⟨w, hw, he⟩ := hcomm hu
  have hw' : w = (⟨u, hU⟩ : U) := Subtype.ext he
  rw [hw'] at hw
  exact hw

variable {M : Type*} [Group M] {L R : Subgroup M} {a c : Vertex R}

/-- Coordinates of the actual U_c with the frame's original marking. -/
noncomputable def naturalCoordinates (f : FrameAt a c) : U R c ≃* Space :=
  (subgroupOfEquivOfLe ((U_le_Z R c).trans (Z_le_stabilizer R c))).symm.trans
    f.naturalU.equivOfBot

/-- Natural image, always restricting to U_c before mapping. -/
noncomputable def naturalImage (f : FrameAt a c)
    (D : Subgroup (FreeAmalgam R)) : Subgroup Space :=
  (D.subgroupOf (U R c)).map (naturalCoordinates f).toMonoidHom

theorem naturalImage_card (f : FrameAt a c) (D : Subgroup (FreeAmalgam R))
    (hD : D ≤ U R c) : Nat.card (naturalImage f D) = Nat.card D := by
  rw [naturalImage, card_map_of_injective (naturalCoordinates f).injective,
    Nat.card_congr (subgroupOfEquivOfLe hD).toEquiv]

theorem naturalCoordinates_conjugation (f : FrameAt a c)
    (g : stabilizer R c) (u v : U R c)
    (hv : (v : FreeAmalgam R) = g * (u : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹) :
    naturalCoordinates f v = modelAction (f.naturalU.marking (f.sectionData.projection g))
      (naturalCoordinates f u) := by
  apply Multiplicative.toAdd.injective
  exact f.naturalU.action g (mem_top g) _ _ (Subtype.ext hv)

theorem naturalImage_fixes (f : FrameAt a c) (D : Subgroup (FreeAmalgam R))
    (g : stabilizer R c) (hg : (g : FreeAmalgam R) ∈ centralizer (D : Set (FreeAmalgam R))) :
    f.naturalU.marking (f.sectionData.projection g) ∈ planeFixer (naturalImage f D) := by
  rintro _ ⟨u, hu, rfl⟩
  exact (naturalCoordinates_conjugation f g u u (by
    rw [← hg u hu, mul_inv_cancel_right])).symm

/-- The edge transported by the source's inverse conjugation is the actual
edge at the transported neighbor of c. -/
theorem conjugate_edge_eq (s : EdgeData a c) (g : stabilizer R c) :
    (edgeCommutator R a s.neighbor).map (MulAut.conj (g : FreeAmalgam R)⁻¹).toMonoidHom =
      edgeCommutator R c (act R g s.neighbor) := by
  rw [s.edge_eq, edgeCommutator, map_commutator, ← Z_act, ← Q_act, g.property]
  rfl

variable [Finite M] {source : LocalSource L R} {geometry : Geometry R}

/-- Fixation modulo B_c on the actual W annihilates the incident natural
displacement. The hypothesis concerns the element of W, not a larger radius. -/
theorem fixed_annihilates_edge (common : CommonFacts R source geometry)
    (hc : color R c = false) (hd : (cosetGraph R).dist a c = 2)
    (hb : 2 < geometry.b R) (f : FrameAt a c) (hop : ¬ f.SameOrientation)
    {t : Vertex R} (hct : Adjacent R c t) (x : localZSpan R a c)
    (hfixed : ∀ q ∈ Q R t, ⁅q, (x : FreeAmalgam R)⁆ ∈ B R c (geometry.Z_normal c)) :
    naturalImage f (edgeCommutator R c t) ≤
      Model.annihilator (coordinates source hc hd hb f hop x) := by
  let S := stabilizer R c
  let T := (Q R t).subgroupOf S
  let U₀ := (U R c).subgroupOf S
  have hTS : Q R t ≤ S := fun _ hq => hq.2 c (adjacent_symm R hct)
  have hUS : U R c ≤ S := (U_le_Z R c).trans (Z_le_stabilizer R c)
  let x₀ : (localZSpan R a c).subgroupOf S :=
    ⟨⟨x, f.sectionData.local_group x.property⟩, x.property⟩
  have hcomm := fixed_annihilates_commutator f.naturalU
    (spanDual source hc hd hb f hop) T x₀ (fun q hq => hfixed q hq)
  have he : ⁅U₀,T⁆ = (edgeCommutator R c t).subgroupOf S := by
    apply map_injective S.subtype_injective
    change (⁅U₀,T⁆).map S.subtype = ((⁅Z R c,Q R t⁆).subgroupOf S).map S.subtype
    rw [map_commutator, map_subgroupOf_eq_of_le hUS, map_subgroupOf_eq_of_le hTS,
      map_subgroupOf_eq_of_le ((Escape.EdgeTransfer.edge_commutator_le_natural hb
        (moduleFacts common) c t hc hct).trans hUS)]
    exact (Escape.EdgeTransfer.edge_commutator_eq_natural hb (moduleFacts common) c t hc hct).symm
  rintro _ ⟨u, hu, rfl⟩
  exact hcomm ⟨u, hUS u.property⟩ (he.symm ▸ hu) u.property

/-- Every original conjugate seed annihilates its own literal conjugate edge. -/
theorem conjugate_seed_annihilates (common : CommonFacts R source geometry)
    (hc : color R c = false) (hd : (cosetGraph R).dist a c = 2)
    (hb : 2 < geometry.b R) (f : FrameAt a c) (hop : ¬ f.SameOrientation)
    (s : EdgeData a c) (g : stabilizer R c) (x : localZSpan R a c)
    (hx : (x : FreeAmalgam R) ∈ Z R (act R g a)) :
    naturalImage f ((edgeCommutator R a s.neighbor).map
      (MulAut.conj (g : FreeAmalgam R)⁻¹).toMonoidHom) ≤
      Model.annihilator (coordinates source hc hd hb f hop x) := by
  rw [conjugate_edge_eq s g]
  have hct : Adjacent R c (act R g s.neighbor) := by
    have hg : act R (g : FreeAmalgam R) c = c := g.property
    simpa only [hg] using
      (adjacent_act_iff R (g : FreeAmalgam R) c s.neighbor).mpr s.adjacent_center
  apply fixed_annihilates_edge common hc hd hb f hop hct x
  intro q hq
  have h := conjugate_seed_fixed_mod_Z s g
  rw [commutator_comm] at h
  exact Escape.EdgeTransfer.Z_le_B hb c hc (h (commutator_mem_commutator hq hx))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.LocalSpans.BadImage
