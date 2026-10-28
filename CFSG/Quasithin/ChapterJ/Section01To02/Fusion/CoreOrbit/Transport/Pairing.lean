module

public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.CoreOrbit.Transport.Plane
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.ConjugateIntersections.Basic

/-!
# The restricted quotient as actual commutator functionals

For q in Q, the central commutator row u ↦ [q,u] descends through the
specified U/Z coordinates to a binary linear functional. Equality of rows
is precisely equality under the literal coreMap. Membership in S is
precisely vanishing on the plane V/Z, since S = C_G(V).

These statements retain the pairing, which an arbitrary equivariant
identification with the dual module need not specify. They connect the
plane-annihilator action to the restricted transport needed by J.2.8.

Source: Aschbacher–Smith J.2.2(4), J.2.8, pp.432,437–438.
-/

public section
noncomputable section
open Subgroup Representation
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterJ.Fusion.CoreOrbit
variable {G : Type*} [Group G] [Finite G]

private def centerCoordinates (d : LocalSetup G) :
    d.toTypeRuSetup.Z ≃* Multiplicative (ZMod 2) :=
  mulEquivOfPrimeCardEq d.card_Z (by simp)

private def shear (d : LocalSetup G) (q : d.toTypeRuSetup.Q) :
    d.toTypeRuSetup.U →* d.toTypeRuSetup.Z :=
  Classical.choose (d.transvection_of_Q q)

private theorem shear_eq (d : LocalSetup G) (q : d.toTypeRuSetup.Q)
    (u : d.toTypeRuSetup.U) : (shear d q u : G) = ⁅(q : G), (u : G)⁆ := by
  have he := (Classical.choose_spec (d.transvection_of_Q q)).2 u
  change (q : G) * u * (q : G)⁻¹ = (shear d q u : G) * u at he
  rw [commutatorElement_def, he]
  group

private theorem shear_kills_Z (d : LocalSetup G) (q : d.toTypeRuSetup.Q)
    (z : d.toTypeRuSetup.Z) :
    shear d q ⟨z, d.ru2.natural.kernel_le z.property⟩ = 1 :=
  (Classical.choose_spec (d.transvection_of_Q q)).1 z

private def characterRow (d : LocalSetup G) (q : d.toTypeRuSetup.Q) :
    Multiplicative FourSpace →* Multiplicative (ZMod 2) :=
  d.ru2.natural.coordinates.liftOfSurjective d.ru2.natural.onto
    ⟨(centerCoordinates d).toMonoidHom.comp (shear d q), by
      intro u hu
      have hz := (d.ru2.natural.coordinates_eq_one_iff u).mp hu
      change centerCoordinates d (shear d q u) = 1
      rw [show shear d q u = 1 from shear_kills_Z d q ⟨u, hz⟩, map_one]⟩

/-- The commutator functional in the original Ru2 natural coordinates. -/
def commutatorCharacter (d : LocalSetup G) (q : d.toTypeRuSetup.Q) :
    Module.Dual (ZMod 2) FourSpace :=
  ({ toFun w := (characterRow d q (Multiplicative.ofAdd w)).toAdd
     map_zero' := (characterRow d q).map_one
     map_add' := (characterRow d q).map_mul } : FourSpace →+ ZMod 2).toZModLinearMap 2

private theorem character_eval (d : LocalSetup G) (q : d.toTypeRuSetup.Q)
    (u : d.toTypeRuSetup.U) :
    commutatorCharacter d q (d.ru2.natural.coordinates u).toAdd =
      (centerCoordinates d (shear d q u)).toAdd := by
  exact congrArg Multiplicative.toAdd
    (MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ u)

/-- Vanishing is equivalent to actual centralization of the represented element. -/
theorem character_eval_eq_zero (d : LocalSetup G) (q : d.toTypeRuSetup.Q)
    (u : d.toTypeRuSetup.U) :
    commutatorCharacter d q (d.ru2.natural.coordinates u).toAdd = 0 ↔
      (q : G) * u = (u : G) * q := by
  rw [character_eval]
  change centerCoordinates d (shear d q u) = 1 ↔ _
  rw [← (centerCoordinates d).map_one, (centerCoordinates d).injective.eq_iff]
  rw [Subtype.ext_iff, shear_eq]
  exact commutatorElement_eq_one_iff_mul_comm

/-- The zero functional has exactly the prescribed kernel HC. -/
theorem character_eq_zero (d : LocalSetup G) (q : d.toTypeRuSetup.Q) :
    commutatorCharacter d q = 0 ↔ (q : G) ∈ d.toTypeRuSetup.HC := by
  constructor
  · intro he
    refine ⟨pCoreIn_le 2 _ q.property, ?_⟩
    intro u hu
    exact ((character_eval_eq_zero d q ⟨u, hu⟩).mp
      (by rw [he]; rfl)).symm
  · intro hq
    apply LinearMap.ext
    intro w
    obtain ⟨u, rfl⟩ := d.ru2.natural.onto (Multiplicative.ofAdd w)
    exact (character_eval_eq_zero d q u).mpr (hq.2 u u.property).symm

/-- Equality of functionals is equality under the exact map used by CoreOrbit. -/
theorem character_eq_iff (d : LocalSetup G) (x y : d.toTypeRuSetup.Q) :
    commutatorCharacter d x = commutatorCharacter d y ↔
      coreMap d.toTypeRuSetup x = coreMap d.toTypeRuSetup y := by
  rw [coreMap_eq_iff]
  have hrows : commutatorCharacter d x = commutatorCharacter d y ↔
      ∀ u : d.toTypeRuSetup.U, ⁅(x : G), (u : G)⁆ = ⁅(y : G), (u : G)⁆ := by
    constructor
    · intro he u
      have hh := congrArg (fun f : Module.Dual (ZMod 2) FourSpace =>
        f (d.ru2.natural.coordinates u).toAdd) he
      rw [character_eval, character_eval] at hh
      have hh' := congrArg Subtype.val
        ((centerCoordinates d).injective (Multiplicative.toAdd.injective hh))
      simpa only [shear_eq] using hh'
    · intro he
      apply LinearMap.ext
      intro w
      obtain ⟨u, rfl⟩ := d.ru2.natural.onto (Multiplicative.ofAdd w)
      change commutatorCharacter d x (d.ru2.natural.coordinates u).toAdd =
        commutatorCharacter d y (d.ru2.natural.coordinates u).toAdd
      rw [character_eval, character_eval]
      congr 2
      apply Subtype.ext
      simpa only [shear_eq] using he u
  rw [hrows]
  constructor
  · intro he
    refine ⟨d.toTypeRuSetup.H.mul_mem
      (d.toTypeRuSetup.H.inv_mem (pCoreIn_le 2 _ y.property))
      (pCoreIn_le 2 _ x.property), ?_⟩
    intro u hu
    have hh := congrArg (fun a : G => (y : G)⁻¹ * a * u * y) (he ⟨u, hu⟩)
    simp only [commutatorElement_def] at hh
    have hh' : (y : G)⁻¹ * x * u * (x : G)⁻¹ * y = u := by
      simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left,
        inv_mul_cancel, mul_inv_cancel, mul_one] using hh
    have hc := congrArg (fun a : G => a * ((y : G)⁻¹ * x)) hh'
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left,
      inv_mul_cancel, mul_one] using hc.symm
  · intro hc u
    have hh := hc.2 u u.property
    have he := congrArg (fun a : G => (y : G) * a * (x : G)⁻¹ * (u : G)⁻¹) hh
    simpa only [commutatorElement_def, mul_assoc, mul_inv_cancel_left,
      inv_mul_cancel_left, inv_mul_cancel, mul_inv_cancel, one_mul, mul_one] using he.symm

/-- Centralizing V is precisely vanishing on its marked image. -/
theorem character_annihilates_plane (d : LocalSetup G) (q : d.toTypeRuSetup.Q) :
    (∀ w ∈ naturalPlane d, commutatorCharacter d q w = 0) ↔
      (q : G) ∈ d.toTypeRuSetup.S := by
  change _ ↔ (q : G) ∈ d.L.pCoreIn 2
  rw [← d.ru1.centralizer_V]
  constructor
  · intro hf v hv
    exact ((character_eval_eq_zero d q ⟨v, le_conjugateSpan _ _ hv⟩).mp
      (hf _ ((coordinates_mem_naturalPlane d _).mpr hv))).symm
  · intro hq w hw
    obtain ⟨v, hv⟩ := (mem_naturalPlane d w).mp hw
    rw [← show (planeMap d v).toAdd = w from congrArg Multiplicative.toAdd hv]
    exact (character_eval_eq_zero d q (inclusion (le_conjugateSpan _ _) v)).mpr
      (hq v v.property).symm

/-- Conjugation acts contragrediently on the actual commutator rows. -/
theorem character_conjugate (d : LocalSetup G) (h : d.toTypeRuSetup.H)
    (q : d.toTypeRuSetup.Q) :
    commutatorCharacter d (coreConj d.toTypeRuSetup h q) =
      (commutatorCharacter d q).comp
        (d.ru2.naturalAction.action ((d.ru2.quotientMap h)⁻¹)) := by
  apply LinearMap.ext
  intro w
  obtain ⟨u, rfl⟩ := d.ru2.natural.onto (Multiplicative.ofAdd w)
  let u' : d.toTypeRuSetup.U := ⟨(h : G)⁻¹ * u * h,
    by simpa only [inv_inv] using
      (mem_normalizer_iff.mp (d.ru2.natural.normalized (d.toTypeRuSetup.H.inv_mem h.property)) u).mp u.property⟩
  have hu' : (d.ru2.natural.coordinates u').toAdd =
      d.ru2.naturalAction.action ((d.ru2.quotientMap h)⁻¹)
        (d.ru2.natural.coordinates u).toAdd := by
    simpa only [u', MonoidHom.comp_apply, coe_inv, inv_inv, map_inv] using
      d.ru2.natural.equivariant h⁻¹ u
  change commutatorCharacter d (coreConj d.toTypeRuSetup h q)
    (d.ru2.natural.coordinates u).toAdd =
      commutatorCharacter d q (d.ru2.naturalAction.action
        ((d.ru2.quotientMap h)⁻¹) (d.ru2.natural.coordinates u).toAdd)
  rw [← hu', character_eval, character_eval]
  congr 2
  apply Subtype.ext
  rw [shear_eq, shear_eq]
  have hc := h.property _ (d.toTypeRuSetup.commutator_Q_U_le_Z
    (commutator_mem_commutator q.property u'.property))
  have he : (h : G) * ⁅(q : G), (u' : G)⁆ * (h : G)⁻¹ = ⁅(q : G), (u' : G)⁆ := by
    rw [← hc, mul_inv_cancel_right]
  rw [← he]
  change ⁅(h : G) * q * (h : G)⁻¹, (u : G)⁆ =
    (h : G) * ⁅(q : G), (h : G)⁻¹ * u * h⁆ * (h : G)⁻¹
  simp only [commutatorElement_def]
  group

end CFSG.Quasithin.ChapterJ.Fusion.CoreOrbit
