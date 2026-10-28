module

public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.CommutatorGeometry.FixedSeed.FixedLift
public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.CommutatorGeometry.FixedSeed.Action
public import Theory.Representation.SL2FourNaturalOrbits.SylowDisplacement
public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.CommutatorGeometry.FixedSeed.MarkedImage

/-!
# The full commutator seed from the marked natural Sylow image

The natural fixed plane is the literal image of V in U/Z: S centralizes V,
and both planes have four elements. Upper-unipotent displacements then
supply every vector of V/Z in the row of a noncentral u in U. For a
T-fixed coset uV, the invariant row also contains Z, so it is all of V.
The marked Sylow-image theorem discharges the action identification from
the two core equalities of J.2.2(1), which remain explicit source inputs.

Source: Aschbacher–Smith, J.2.3 assertion (!), printed p.433 (PDF p.444).
-/

@[expose] public section
noncomputable section
open Subgroup Representation
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterJ.SpecialCore.CommutatorGeometry.FixedSeed
variable {G : Type*} [Group G] [Finite G] (d : LocalSetup G)

private def vMap : d.V →* Multiplicative FourSpace :=
  d.ru2.natural.coordinates.comp (inclusion (le_conjugateSpan d.toTypeRuSetup.H d.V))

private theorem vMap_kernel : (vMap d).ker = d.toTypeRuSetup.Z.subgroupOf d.V := by
  ext v
  exact d.ru2.natural.coordinates_eq_one_iff _

private theorem card_vMap_range : Nat.card (vMap d).range = 4 := by
  have hc := (vMap d).ker.card_mul_index
  rw [index_ker, vMap_kernel] at hc
  have hk : Nat.card (d.toTypeRuSetup.Z.subgroupOf d.V) = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (d.center_eq.le.trans inf_le_left)).toEquiv,
      d.card_Z]
  rw [hk, d.ru1.card_V] at hc
  omega

private theorem coordinates_mem_vMap (u : d.toTypeRuSetup.U) :
    d.ru2.natural.coordinates u ∈ (vMap d).range ↔ (u : G) ∈ d.V := by
  constructor
  · rintro ⟨v, hv⟩
    let v' : d.toTypeRuSetup.U := inclusion (le_conjugateSpan d.toTypeRuSetup.H d.V) v
    have hc : ((v'⁻¹ * u : d.toTypeRuSetup.U) : G) ∈ d.toTypeRuSetup.Z := by
      apply (d.ru2.natural.coordinates_eq_one_iff _).mp
      rw [map_mul, map_inv, show d.ru2.natural.coordinates v' =
        d.ru2.natural.coordinates u from hv, inv_mul_cancel]
    have hm := d.V.mul_mem v.property ((d.center_eq.le.trans inf_le_left) hc)
    simpa [v'] using hm
  · intro hu
    exact ⟨⟨u, hu⟩, rfl⟩

private theorem lift_actor (P : Sylow 2 SL2FourNatural.SL)
    (hP : (coreMap d).range = (P : Subgroup SL2FourNatural.SL).map (markingMap d))
    (a : SL2FourNatural.SL) (ha : a ∈ (P : Subgroup SL2FourNatural.SL)) :
    ∃ s : d.toTypeRuSetup.S, coreMap d s = markingMap d a := by
  apply MonoidHom.mem_range.mp
  rw [hP]
  exact mem_map.mpr ⟨a, ha, rfl⟩

/-- V/Z is the fixed plane for the same Sylow and the same Ru2 coordinates. -/
theorem natural_fixed_plane (P : Sylow 2 SL2FourNatural.SL)
    (hP : (coreMap d).range = (P : Subgroup SL2FourNatural.SL).map (markingMap d))
    (W : Submodule (ZMod 2) FourSpace) (hcard : Nat.card W = 4)
    (hfixed : ∀ v, v ∈ W ↔ ∀ a ∈ (P : Subgroup SL2FourNatural.SL),
      SL2FourNatural.action a v = v) (u : d.toTypeRuSetup.U) :
    (d.ru2.natural.coordinates u).toAdd ∈ W ↔ (u : G) ∈ d.V := by
  have hle : (vMap d).range ≤ W.toAddSubgroup.toSubgroup := by
    rintro x ⟨v, rfl⟩
    apply (hfixed _).mpr
    intro a ha
    obtain ⟨s, hs⟩ := lift_actor d P hP a ha
    let v' : d.toTypeRuSetup.U := inclusion (le_conjugateSpan d.toTypeRuSetup.H d.V) v
    have he := d.ru2.natural.equivariant (inclusion d.S_le_H s) v'
    have hc : (s : G) * v * (s : G)⁻¹ = v := by
      rw [d.ru1.central_V v.property s s.property, mul_inv_cancel_right]
    have hv' : (⟨s * v' * (s : G)⁻¹,
        (mem_normalizer_iff.mp (d.ru2.natural.normalized (d.S_le_H s.property)) v').mp
          v'.property⟩ : d.toTypeRuSetup.U) = v' := Subtype.ext hc
    change (d.ru2.natural.coordinates ⟨(s : G) * v' * (s : G)⁻¹, _⟩).toAdd =
      d.ru2.naturalAction.action (coreMap d s) (d.ru2.natural.coordinates v').toAdd at he
    rw [hv'] at he
    rw [hs] at he
    exact (d.ru2.naturalAction.restriction a _).symm.trans he.symm
  have he : (vMap d).range = W.toAddSubgroup.toSubgroup :=
    eq_of_le_of_card_ge hle (by change Nat.card W ≤ Nat.card (vMap d).range; rw [hcard, card_vMap_range])
  rw [← coordinates_mem_vMap d u, he]
  rfl

/-- Natural displacements supply every V/Z coordinate in the commutator row. -/
theorem commutator_covers_mod_center (himage : HasNaturalSylowImage d)
    (u : d.toTypeRuSetup.U) (hu : (u : G) ∉ d.V) (v : d.V) :
    ∃ c : d.toTypeRuSetup.U,
      (c : G) ∈ ⁅zpowers (u : G), d.toTypeRuSetup.S⁆ ∧
      d.ru2.natural.coordinates c = d.ru2.natural.coordinates
        ⟨v, le_conjugateSpan d.toTypeRuSetup.H d.V v.property⟩ := by
  obtain ⟨P, hP⟩ := himage
  obtain ⟨W, hcard, hfixed, hdispl⟩ := SL2FourNatural.sylow_fixed_plane_displacements P
  have huW : (d.ru2.natural.coordinates u).toAdd ∉ W := by
    simpa only [natural_fixed_plane d P hP W hcard hfixed u] using hu
  let v' : d.toTypeRuSetup.U := inclusion (le_conjugateSpan d.toTypeRuSetup.H d.V) v
  have hvW : (d.ru2.natural.coordinates v').toAdd ∈ W :=
    (natural_fixed_plane d P hP W hcard hfixed v').mpr v.property
  obtain ⟨a, ha, had⟩ := hdispl _ huW _ hvW
  obtain ⟨s, hs⟩ := lift_actor d P hP a ha
  let b : d.toTypeRuSetup.U := ⟨s * u * (s : G)⁻¹,
    (mem_normalizer_iff.mp (d.ru2.natural.normalized (d.S_le_H s.property)) u).mp u.property⟩
  have he := d.ru2.natural.equivariant (inclusion d.S_le_H s) u
  change (d.ru2.natural.coordinates b).toAdd =
    d.ru2.naturalAction.action (coreMap d s) (d.ru2.natural.coordinates u).toAdd at he
  rw [hs] at he
  change (d.ru2.natural.coordinates b).toAdd = d.ru2.naturalAction.action
    (d.ru2.naturalAction.marking a) (d.ru2.natural.coordinates u).toAdd at he
  rw [d.ru2.naturalAction.restriction] at he
  refine ⟨b * u⁻¹, ?_, ?_⟩
  · change ⁅(s : G), (u : G)⁆ ∈ ⁅zpowers (u : G), d.toTypeRuSetup.S⁆
    rw [← commutatorElement_inv (u : G) (s : G)]
    exact inv_mem (commutator_mem_commutator (mem_zpowers _) s.property)
  · apply Multiplicative.toAdd.injective
    change (d.ru2.natural.coordinates (b * u⁻¹)).toAdd = (vMap d v).toAdd
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, ← sub_eq_add_neg]
    change (d.ru2.natural.coordinates b).toAdd - (d.ru2.natural.coordinates u).toAdd = _
    rw [he]
    exact had

/-- The seed assertion (!) after identifying the literal natural Sylow image. -/
theorem sylowSeed_of_marked_action (himage : HasNaturalSylowImage d) :
    SylowSeed d.ru1 d.sylowInL := by
  obtain ⟨u, huU, huV, hf⟩ := exists_fixed_lift_in_U d
  refine ⟨u, huV, hf, le_antisymm (d.ru1.commutator_le_V u) ?_⟩
  have hZ := center_le_fixed_commutator d u huV hf
  intro v hv
  obtain ⟨c, hc, he⟩ := commutator_covers_mod_center d himage ⟨u, huU⟩ huV ⟨v, hv⟩
  let v' : d.toTypeRuSetup.U := ⟨v, le_conjugateSpan d.toTypeRuSetup.H d.V hv⟩
  have hz : ((c⁻¹ * v' : d.toTypeRuSetup.U) : G) ∈ d.toTypeRuSetup.Z := by
    apply (d.ru2.natural.coordinates_eq_one_iff _).mp
    rw [map_mul, map_inv, he]
    exact inv_mul_cancel (vMap d ⟨v, hv⟩)
  have hm := (⁅zpowers (u : G), d.toTypeRuSetup.S⁆ : Subgroup G).mul_mem hc (hZ hz)
  simpa [v'] using hm

/-- Consumer application of the single-seed propagation theorem. The
independent natural-parabolic premise remains with the geometry owner. -/
theorem full_commutator_of_marked_action (himage : HasNaturalSylowImage d)
    (hparabolic : NaturalParabolics d.L d.V)
    (t : d.toTypeRuSetup.S) (ht : (t : G) ∉ d.V) :
    ⁅zpowers (t : G), d.toTypeRuSetup.S⁆ = d.V :=
  full_commutator_of_one_seed d.ru1 hparabolic d.sylowInL
    (sylowSeed_of_marked_action d himage) t ht

/-- The full-image seed (!) of J.2.3 from the preceding two-core equalities.
Their producer is J.2.2(1); final source assembly discharges both inputs. -/
theorem sylowSeed
    (hprod : d.toTypeRuSetup.R₁ = d.toTypeRuSetup.Q ⊔ d.toTypeRuSetup.S)
    (hcore : (d.toTypeRuSetup.L₁ ⊔ (d.T : Subgroup G)).pCoreIn 2 = d.toTypeRuSetup.R₁) :
    SylowSeed d.ru1 d.sylowInL :=
  sylowSeed_of_marked_action d (hasNaturalSylowImage d hprod hcore)

/-- Application to the propagation step, with NaturalParabolics left for
its independent geometry producer. No additional seed premise remains. -/
theorem full_commutator
    (hprod : d.toTypeRuSetup.R₁ = d.toTypeRuSetup.Q ⊔ d.toTypeRuSetup.S)
    (hcore : (d.toTypeRuSetup.L₁ ⊔ (d.T : Subgroup G)).pCoreIn 2 = d.toTypeRuSetup.R₁)
    (hparabolic : NaturalParabolics d.L d.V)
    (t : d.toTypeRuSetup.S) (ht : (t : G) ∉ d.V) :
    ⁅zpowers (t : G), d.toTypeRuSetup.S⁆ = d.V :=
  full_commutator_of_one_seed d.ru1 hparabolic d.sylowInL
    (sylowSeed d hprod hcore) t ht

end CFSG.Quasithin.ChapterJ.SpecialCore.CommutatorGeometry.FixedSeed
