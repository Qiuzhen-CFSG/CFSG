module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Centralizer.Generation.Native.Intersection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Centralizer.Generation.SourceDisplay.Model

/-!
# Actual neighbor vectors and compatible full-radius coordinates

Use the supplied full natural section to extend the opposite coordinates
from Vcirc/U to V/B without changing the marking of U. Every neighboring
radius group has a nonzero image. Fixation by its own kernel shows that its
covector annihilates the actual displacement plane; both planes have order
four, so this is equality.

The final lifting lemma uses the exact intersection Vcirc ∩ B = U. It
lifts images of actual products in K ∩ Vcirc, with no premise requiring a
native lift inside any single neighboring group. The annihilation argument
is adapted from Six/Complement/FixedComparison/DualFixed.lean.

Source: Meierfrankenfeld--Stellmacher (1993), the generation display before
(4.3.2)(4), printed p.884.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Centralizer.Generation.SourceDisplay
open RankOnePairing
private def pairingMap {G : Type*} [Group G] {π : G →* SL} {U : Subgroup G}
    (n : NaturalFactor π ⊤ U ⊥) (f : Fin 3 → ZMod 2) : U →* Multiplicative (ZMod 2) where
  toFun u := Multiplicative.ofAdd (dotProduct f (n.coordinates u).toAdd)
  map_one' := by simp
  map_mul' u v := by
    change Multiplicative.ofAdd (dotProduct f (n.coordinates (u*v)).toAdd) = _
    rw [map_mul, toAdd_mul, dotProduct_add]
    rfl

private theorem fixed_annihilates_commutator {G : Type*} [Group G] {π : G →* SL}
    {U V B : Subgroup G} (n : NaturalFactor π ⊤ U ⊥)
    (d : DualFactor π ⊤ V B U n) (A : Subgroup G) (x : V)
    (hfixed : ∀ a ∈ A, ⁅a, (x : G)⁆ ∈ B) :
    ∀ u ∈ ⁅U, A⁆, ∀ hu : u ∈ U,
      dotProduct (d.coordinates x).toAdd (n.coordinates ⟨u, hu⟩).toAdd = 0 := by
  let f := (d.coordinates x).toAdd
  let k := pairingMap n f
  have hcomm : ⁅U, A⁆ ≤ k.ker.map U.subtype := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro a ha u hu
    let u₀ : U := ⟨u, hu⟩
    let u₁ : U := ⟨a * u * a⁻¹, le_normalizer_iff.mp n.normalized a (mem_top _) u hu⟩
    let y : V := ⟨a⁻¹ * (x : G) * a,
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
    change Multiplicative.ofAdd (dotProduct f (n.coordinates u₁).toAdd) =
      Multiplicative.ofAdd (dotProduct f (n.coordinates u₀).toAdd)
    congr 1
    rw [n.action a (mem_top _) u₀ u₁ rfl, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose, ← hact]
  intro u hu hU
  obtain ⟨w, hw, he⟩ := hcomm hu
  have hw' : w = (⟨u, hU⟩ : U) := Subtype.ext he
  rw [hw'] at hw
  exact hw


variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : MS93.Geometry R}

noncomputable def radiusCoordinates (source : LocalSource L R) (hb : 2 < geometry.b R)
    {c : Vertex R} (hc : color R c = false)
    (s : NaturalSectionAt c (V R c) (Z R c)) (o : OppositeSectionAt c) :
    V R c →* Space :=
  (Six.Complement.FixedComparison.fullRadiusDual source hb hc s o).coordinates.comp
    (subgroupOfEquivOfLe
      ((geometry.V_le_Q hb c hc).trans (fun _ hx => hx.1))).symm.toMonoidHom

theorem radiusCoordinates_kernel (source : LocalSource L R) (hb : 2 < geometry.b R)
    {c : Vertex R} (hc : color R c = false)
    (s : NaturalSectionAt c (V R c) (Z R c)) (o : OppositeSectionAt c) :
    (radiusCoordinates source hb hc s o).ker =
      (B R c (geometry.Z_normal c)).subgroupOf (V R c) := by
  ext x
  change (Six.Complement.FixedComparison.fullRadiusDual source hb hc s o).coordinates _ = 1 ↔ _
  rw [← MonoidHom.mem_ker, (Six.Complement.FixedComparison.fullRadiusDual source hb hc s o).kernel]
  rfl

theorem radiusCoordinates_conjugation (source : LocalSource L R) (hb : 2 < geometry.b R)
    {c : Vertex R} (hc : color R c = false)
    (s : NaturalSectionAt c (V R c) (Z R c)) (o : OppositeSectionAt c)
    (g : stabilizer R c) (x y : V R c)
    (hy : (y : FreeAmalgam R) = g * (x : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹) :
    radiusCoordinates source hb hc s o y =
      Model.dualAction (markedProjection o g) (radiusCoordinates source hb hc s o x) := by
  apply Multiplicative.toAdd.injective
  exact (Six.Complement.FixedComparison.fullRadiusDual source hb hc s o).action
    g (mem_top g) _ _ (Subtype.ext hy)

theorem neighbor_coordinates_annihilate (source : LocalSource L R) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry) (facts : ContraryLocalFacts geometry)
    {c t : Vertex R} (hc : color R c = false) (hct : Adjacent R c t)
    (s : NaturalSectionAt c (V R c) (Z R c)) (o : OppositeSectionAt c)
    (x : V R c) (hx : (x : FreeAmalgam R) ∈ V R t) :
    naturalImage o (edgeDisplacement c t) ≤
      Model.annihilator (radiusCoordinates source hb hc s o x) := by
  let A := stabilizer R c
  let hVA : V R c ≤ A := (geometry.V_le_Q hb c hc).trans (fun _ hx => hx.1)
  let x₀ : (V R c).subgroupOf A := ⟨⟨x, hVA x.property⟩, x.property⟩
  let T := (Q R t).subgroupOf A
  let U₀ := (U R c).subgroupOf A
  have hTA : Q R t ≤ A := fun _ hx => hx.2 c (adjacent_symm R hct)
  have hUA : U R c ≤ A := (U_le_Z c).trans (Z_le_stabilizer R c)
  have hfixed : ∀ a ∈ T, ⁅a, (x₀ : A)⁆ ∈
      (B R c (geometry.Z_normal c)).subgroupOf A := by
    intro a ha
    have h := neighbor_fixed_mod_B source hb facts hc hct
    rw [commutator_comm] at h
    exact h (commutator_mem_commutator ha hx)
  have hcomm := fixed_annihilates_commutator o.naturalU
    (Six.Complement.FixedComparison.fullRadiusDual source hb hc s o) T x₀ hfixed
  have he : ⁅U₀,T⁆ = (edgeDisplacement c t).subgroupOf A := by
    apply map_injective A.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hUA, map_subgroupOf_eq_of_le hTA,
      map_subgroupOf_eq_of_le ((Initial.edge_le_natural source c t hc hct).trans hUA)]
    exact (Initial.edge_eq_natural_commutator source hb modules c t hc hct).symm
  rintro _ ⟨u, hu, rfl⟩
  exact hcomm ⟨u, hUA u.property⟩ (he.symm ▸ hu) u.property

theorem exists_neighbor_coordinate (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry) (p : Counterexample geometry)
    {c t : Vertex R} (hc : color R c = false) (hct : Adjacent R c t)
    (s : NaturalSectionAt c (V R c) (Z R c)) (o : OppositeSectionAt c) :
    ∃ x : V R c, (x : FreeAmalgam R) ∈ V R t ∧
      radiusCoordinates source hb hc s o x ≠ 1 ∧
      naturalImage o (edgeDisplacement c t) =
        Model.annihilator (radiusCoordinates source hb hc s o x) := by
  have hi := neighbor_fixed_quotient_index source hb modules initial facts p hc hct
  have hnot : ¬ V R t ≤ B R c (geometry.Z_normal c) := by
    intro h
    rw [relIndex_eq_one.mpr h] at hi
    omega
  obtain ⟨x, hx, hxn⟩ := SetLike.not_le_iff_exists.mp hnot
  let x₀ : V R c := ⟨x, neighbor_V_le hc hct hx⟩
  have hn : radiusCoordinates source hb hc s o x₀ ≠ 1 := by
    intro h
    have hk : x₀ ∈ (radiusCoordinates source hb hc s o).ker := h
    rw [radiusCoordinates_kernel] at hk
    exact hxn hk
  refine ⟨x₀, hx, hn, eq_of_le_of_card_ge
    (neighbor_coordinates_annihilate source hb modules facts hc hct s o x₀ hx) ?_⟩
  rw [edge_image_card source p (by omega) initial hc hct o, Model.annihilator_card _ hn]


theorem moving_le_of_radius_image (source : LocalSource L R)
    (hb : 2 < geometry.b R) {c : Vertex R} (hc : color R c = false)
    (s : NaturalSectionAt c (V R c) (Z R c)) (o : OppositeSectionAt c)
    (K : Subgroup (FreeAmalgam R)) (hUK : U R c ≤ K)
    (himage : ((K ⊓ Vcirc R c).subgroupOf (V R c)).map
      (radiusCoordinates source hb hc s o) = ⊤) : Vcirc R c ≤ K := by
  intro x hx
  let x₀ : V R c := ⟨x, Vcirc_le_V c hx⟩
  have hm : radiusCoordinates source hb hc s o x₀ ∈
      ((K ⊓ Vcirc R c).subgroupOf (V R c)).map
        (radiusCoordinates source hb hc s o) := himage.symm ▸ mem_top _
  obtain ⟨y, hy, he⟩ := hm
  have hz : x₀ * y⁻¹ ∈ (radiusCoordinates source hb hc s o).ker := by
    change radiusCoordinates source hb hc s o (x₀ * y⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  rw [radiusCoordinates_kernel] at hz
  have hU : x * (y : FreeAmalgam R)⁻¹ ∈ U R c := by
    rw [← Six.Complement.FixedComparison.moving_inf_fixed source hb hc s o]
    exact ⟨(Vcirc R c).mul_mem hx ((Vcirc R c).inv_mem hy.2), hz⟩
  have hp := K.mul_mem (hUK hU) hy.1
  change x * (y : FreeAmalgam R)⁻¹ * (y : FreeAmalgam R) ∈ K at hp
  simpa only [inv_mul_cancel_right] using hp

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Centralizer.Generation.SourceDisplay
