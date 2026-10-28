module

public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.CoreOrbit.Transport.Lifting
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.QuotientModule.Natural

/-!
# The marked binary plane and its actual parabolic lifts

The image of V/Z in the specified Ru2 coordinates is a four-element binary
plane. Its inverse image in U is exactly V. Every SL₂(4) element preserving
that plane lifts through the original Ru2 marking to an element of L ∩ H:
its lift normalizes V, and Ru1 identifies this normalizer with L.

Consequently a model calculation on the plane quotient gives literal
transport on U/V, with the same marking and actual ambient conjugators.

Source: Aschbacher–Smith J.2.1–3 and J.2.8, pp.432–434,437–438.
-/

@[expose] public section
noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.ChapterJ.Fusion.CoreOrbit
variable {G : Type*} [Group G] [Finite G]

/-- The specified map on V, with kernel Z. -/
def planeMap (d : LocalSetup G) : d.V →* Multiplicative FourSpace :=
  d.ru2.natural.coordinates.comp (inclusion (le_conjugateSpan _ _))

/-- V/Z as an actual binary subspace of the original natural four-space. -/
def naturalPlane (d : LocalSetup G) : Submodule (ZMod 2) FourSpace :=
  AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup' (planeMap d).range)

theorem mem_naturalPlane (d : LocalSetup G) (w : FourSpace) :
    w ∈ naturalPlane d ↔ ∃ v : d.V, planeMap d v = Multiplicative.ofAdd w := Iff.rfl

/-- The inverse image of the plane is the literal V, not merely an isomorphic subgroup. -/
theorem coordinates_mem_naturalPlane (d : LocalSetup G) (u : d.toTypeRuSetup.U) :
    (d.ru2.natural.coordinates u).toAdd ∈ naturalPlane d ↔ (u : G) ∈ d.V := by
  constructor
  · rintro ⟨v, hv⟩
    change planeMap d v = d.ru2.natural.coordinates u at hv
    let vU : d.toTypeRuSetup.U := inclusion (le_conjugateSpan _ _) v
    have hc : d.ru2.natural.coordinates (vU⁻¹ * u) = 1 := by
      rw [map_mul, map_inv]
      change (planeMap d v)⁻¹ * d.ru2.natural.coordinates u = 1
      rw [hv, inv_mul_cancel]
    have hz := (d.ru2.natural.coordinates_eq_one_iff _).mp hc
    have hZV := d.center_eq.le.trans inf_le_left
    have hm := d.V.mul_mem v.property (hZV hz)
    change (v : G) * ((v : G)⁻¹ * u) ∈ d.V at hm
    simpa only [mul_inv_cancel_left] using hm
  · intro hu
    exact ⟨⟨u, hu⟩, rfl⟩

theorem naturalPlane_card (d : LocalSetup G) : Nat.card (naturalPlane d) = 4 := by
  have hk : (planeMap d).ker = d.toTypeRuSetup.Z.subgroupOf d.V := by
    ext v
    exact d.ru2.natural.coordinates_eq_one_iff (inclusion (le_conjugateSpan _ _) v)
  have hZV := d.center_eq.le.trans inf_le_left
  have hc := card_eq_card_quotient_mul_card_subgroup (planeMap d).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (planeMap d)).toEquiv,
    hk, Nat.card_congr (subgroupOfEquivOfLe hZV).toEquiv, d.card_Z,
    d.ru1.card_V] at hc
  have he : Nat.card (naturalPlane d) = Nat.card (planeMap d).range := rfl
  rw [he]
  omega

/-- A plane-preserving model matrix lifts to the actual parabolic overlap. -/
theorem lift_plane_stabilizer (d : LocalSetup G) (g : SL2FourNatural.SL)
    (hg : ∀ w ∈ naturalPlane d, SL2FourNatural.action g w ∈ naturalPlane d) :
    ∃ h : (d.L ⊓ d.toTypeRuSetup.H : Subgroup G),
      d.ru2.quotientMap ⟨h, h.property.2⟩ = d.ru2.naturalAction.marking g := by
  obtain ⟨h, hh⟩ := d.ru2.quotient_surjective (d.ru2.naturalAction.marking g)
  have hL : (h : G) ∈ d.L := by
    rw [d.ru1.normalizer_eq]
    apply mem_normalizer_fintype
    intro v hv
    let vU : d.toTypeRuSetup.U := ⟨v, le_conjugateSpan _ _ hv⟩
    let c : d.toTypeRuSetup.U := ⟨h * v * (h : G)⁻¹,
      (mem_normalizer_iff.mp (d.ru2.natural.normalized h.property) v).mp vU.property⟩
    apply (coordinates_mem_naturalPlane d c).mp
    have he := d.ru2.natural.equivariant h vU
    change (d.ru2.natural.coordinates c).toAdd =
      d.ru2.naturalAction.action (d.ru2.quotientMap h) _ at he
    rw [he, hh, d.ru2.naturalAction.restriction]
    exact hg _ ((coordinates_mem_naturalPlane d vU).mpr hv)
  exact ⟨⟨h, hL, h.property⟩, hh⟩

/-- A calculation on the natural plane quotient yields an actual parabolic
transporter of each pair of nonzero U/V cosets. -/
theorem elementary_quotient_of_plane (d : LocalSetup G)
    (hmodel : ∀ a b : FourSpace, a ∉ naturalPlane d → b ∉ naturalPlane d →
      ∃ g : SL2FourNatural.SL,
        (∀ w ∈ naturalPlane d, SL2FourNatural.action g w ∈ naturalPlane d) ∧
        b - SL2FourNatural.action g a ∈ naturalPlane d)
    (u v : G) (hu : u ∈ d.toTypeRuSetup.U) (huV : u ∉ d.V)
    (hv : v ∈ d.toTypeRuSetup.U) (hvV : v ∉ d.V) :
    ∃ l : d.L, ((l : G) * u * (l : G)⁻¹)⁻¹ * v ∈ d.V := by
  let uU : d.toTypeRuSetup.U := ⟨u, hu⟩
  let vU : d.toTypeRuSetup.U := ⟨v, hv⟩
  obtain ⟨g, hg, hab⟩ := hmodel (d.ru2.natural.coordinates uU).toAdd
    (d.ru2.natural.coordinates vU).toAdd
    (fun he => huV ((coordinates_mem_naturalPlane d uU).mp he))
    (fun he => hvV ((coordinates_mem_naturalPlane d vU).mp he))
  obtain ⟨h, hh⟩ := lift_plane_stabilizer d g hg
  let hH : d.toTypeRuSetup.H := ⟨h, h.property.2⟩
  let c : d.toTypeRuSetup.U := ⟨h * u * (h : G)⁻¹,
    (mem_normalizer_iff.mp (d.ru2.natural.normalized h.property.2) u).mp hu⟩
  refine ⟨⟨h, h.property.1⟩, ?_⟩
  change ((c⁻¹ * vU : d.toTypeRuSetup.U) : G) ∈ d.V
  apply (coordinates_mem_naturalPlane d (c⁻¹ * vU)).mp
  have he := d.ru2.natural.equivariant hH uU
  change (d.ru2.natural.coordinates c).toAdd =
    d.ru2.naturalAction.action (d.ru2.quotientMap hH) _ at he
  rw [show d.ru2.quotientMap hH = d.ru2.naturalAction.marking g from hh,
    d.ru2.naturalAction.restriction] at he
  rw [map_mul, map_inv]
  change -(d.ru2.natural.coordinates c).toAdd + (d.ru2.natural.coordinates vU).toAdd ∈ _
  rw [he, add_comm, ← sub_eq_add_neg]
  exact hab

end CFSG.Quasithin.ChapterJ.Fusion.CoreOrbit
