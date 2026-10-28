module

public import Theory.Representation.HexacodeAction.PlaneStabilizer.Action
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# The full hexacode action on the six full-weight scalar planes

Every hexacode automorphism normalizes the cubic scalar group, so it permutes
the literal full-weight scalar planes. This extends their existing even
action. An involution preserving one of these planes fixes a nonzero vector
there. Thus an involution with no full-weight fixed word is fixed-point-free
on the six planes and has cycle type 2^3 in this precise permutation action.

Source: Aschbacher--Smith, 12.7.10(3,5), printed pp.842--843. This is the
six-plane action, not an unproved identification with the code coordinates.
-/

public noncomputable section
open Atlas.Codes Subgroup Representation.BinaryOffender
namespace Representation.Hexacode

private theorem full_image_full (g : HexAutomorphisms) (P : FullWeightScalarPlane) :
    IsFullWeightScalarPlane (P.val.map (action g)) := by
  refine ⟨(hexAction g).finrank_map_eq P.val |>.trans P.property.1, ?_, ?_⟩
  · intro w
    change action hexZ w ∈ P.val.map (hexAction g).toLinearMap ↔
      w ∈ P.val.map (hexAction g).toLinearMap
    simp only [Submodule.mem_map_equiv]
    rw [show (hexAction g).symm = hexAction g⁻¹ from (map_inv hexAction g).symm]
    change action g⁻¹ (action hexZ w) ∈ P.val ↔ action g⁻¹ w ∈ P.val
    have hc : g⁻¹ * hexZ * g ∈ subspaceStabilizer action P.val := by
      have hh := (subspaceStabilizer action P.val).zpow_mem P.property.2.1
        (hexSign g⁻¹ : ℤ)
      rw [← hex_conjugation_zpow g⁻¹] at hh
      simpa only [MulAut.conj_apply, inv_inv] using hh
    have he : action (g⁻¹ * hexZ * g) (action g⁻¹ w) =
        action g⁻¹ (action hexZ w) := by
      simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, mul_inv_cancel,
        mul_one]
    exact he ▸ hc (action g⁻¹ w)
  · rintro ⟨v, w, hw, rfl⟩ hn
    have hwn : (⟨w, hw⟩ : P.val) ≠ 0 := by
      intro he
      apply hn
      apply Subtype.ext
      change action g w = 0
      rw [show w = 0 from congrArg Subtype.val he, map_zero]
    exact (Monomial.act_weight g.val w.val).trans (P.property.2.2 ⟨w, hw⟩ hwn)

private def fullPlaneImage (g : HexAutomorphisms) (P : FullWeightScalarPlane) :
    FullWeightScalarPlane := ⟨P.val.map (action g), full_image_full g P⟩

private theorem fullPlaneImage_one (P : FullWeightScalarPlane) : fullPlaneImage 1 P = P := by
  apply Subtype.ext
  change P.val.map (action 1) = P.val
  rw [map_one]
  exact Submodule.map_id _

private theorem fullPlaneImage_mul (g h : HexAutomorphisms) (P : FullWeightScalarPlane) :
    fullPlaneImage (g * h) P = fullPlaneImage g (fullPlaneImage h P) := by
  apply Subtype.ext
  change P.val.map (action (g * h)) = (P.val.map (action h)).map (action g)
  rw [← Submodule.map_comp, map_mul]
  rfl

/-- The full actor permutes the actual six full-weight scalar planes. -/
@[expose] def fullPlanePerm : HexAutomorphisms →* Equiv.Perm FullWeightScalarPlane where
  toFun g :=
    { toFun P := ⟨P.val.map (action g), by exact full_image_full g P⟩
      invFun P := ⟨P.val.map (action g⁻¹), by exact full_image_full g⁻¹ P⟩
      left_inv := by
        intro P
        change fullPlaneImage g⁻¹ (fullPlaneImage g P) = P
        rw [← fullPlaneImage_mul, inv_mul_cancel, fullPlaneImage_one]
      right_inv := by
        intro P
        change fullPlaneImage g (fullPlaneImage g⁻¹ P) = P
        rw [← fullPlaneImage_mul, mul_inv_cancel, fullPlaneImage_one] }
  map_one' := by apply _root_.Equiv.ext; intro P; exact fullPlaneImage_one P
  map_mul' g h := by apply _root_.Equiv.ext; intro P; exact fullPlaneImage_mul g h P

/-- The permutation retains the literal image submodule. -/
theorem fullPlanePerm_apply (g : HexAutomorphisms) (P : FullWeightScalarPlane) :
    (fullPlanePerm g P).val = P.val.map (action g) := rfl

/-- Restriction is the already established alternating action on the same planes. -/
theorem fullPlanePerm_even (g : HexEvenAutomorphisms) : fullPlanePerm g.val = planePerm g := by
  apply _root_.Equiv.ext
  intro P
  apply Subtype.ext
  rfl

/-- A fixed point in the six-plane action is precisely a preserved scalar plane. -/
theorem fullPlanePerm_fixed_iff (g : HexAutomorphisms) (P : FullWeightScalarPlane) :
    fullPlanePerm g P = P ↔ g ∈ subspaceStabilizer action P.val := by
  rw [Subtype.ext_iff, fullPlanePerm_apply]
  constructor
  · intro he w
    constructor
    · intro hw
      have hh : action g w ∈ P.val.map (action g) := he.symm ▸ hw
      obtain ⟨v, hv, hvw⟩ := hh
      exact (hexAction g).injective hvw ▸ hv
    · intro hw
      rw [← he]
      exact ⟨w, hw, rfl⟩
  · intro hg
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact (hg v).2 hv
    · intro hw
      refine ⟨action g⁻¹ w, ?_, ?_⟩
      · apply (hg (action g⁻¹ w)).1
        simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
          map_one, Module.End.one_apply] using hw
      · simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
          map_one, Module.End.one_apply]

private theorem binary_self_add (v : hexacode) : v + v = 0 := by
  have hh : (2 : Bit) • v = 0 := by rw [show (2 : Bit) = 0 by decide, zero_smul]
  simpa only [two_smul] using hh

private theorem preserved_plane_fixed_word (g : HexAutomorphisms) (hg : g ^ 2 = 1)
    (P : FullWeightScalarPlane) (hP : fullPlanePerm g P = P) :
    ∃ v : hexacode, action g v = v ∧ hammingNorm v.val = 6 := by
  have hne : P.val ≠ ⊥ := by
    intro hh
    have hd := P.property.1
    rw [hh, finrank_bot] at hd
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hstab := (fullPlanePerm_fixed_iff g P).mp hP
  have hsquare (v : hexacode) : action g (action g v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, ← pow_two, hg, map_one, Module.End.one_apply]
  by_cases hfix : action g v = v
  · exact ⟨v, hfix, P.property.2.2 ⟨v, hv⟩ (fun hh => hv0 (congrArg Subtype.val hh))⟩
  · have hw : v + action g v ∈ P.val := P.val.add_mem hv ((hstab v).2 hv)
    have hw0 : v + action g v ≠ 0 := by
      intro hh
      have he := congrArg (fun w => v + w) hh
      simp only [← add_assoc, binary_self_add, zero_add, add_zero] at he
      exact hfix he
    exact ⟨v + action g v, by rw [map_add, hsquare, add_comm],
      P.property.2.2 ⟨_, hw⟩ (fun hh => hw0 (congrArg Subtype.val hh))⟩

/-- An involution with no full-weight fixed word acts by three transpositions
on the actual six full-weight scalar planes. -/
theorem fullPlanePerm_cycleType_of_no_full_weight_fixed (g : HexAutomorphisms)
    (hg : g ^ 2 = 1)
    (hfix : ∀ v : hexacode, action g v = v → hammingNorm v.val ≠ 6) :
    (fullPlanePerm g).cycleType = {2, 2, 2} := by
  classical
  have hn (P : FullWeightScalarPlane) : fullPlanePerm g P ≠ P := by
    intro hh
    obtain ⟨v, hv, hw⟩ := preserved_plane_fixed_word g hg P hh
    exact hfix v hv hw
  have hs : (fullPlanePerm g).support = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro P
    exact Equiv.Perm.mem_support.mpr (hn P)
  have hp : (fullPlanePerm g) ^ 2 = 1 := by rw [← map_pow, hg, map_one]
  have hc := Equiv.Perm.cycleType_of_pow_prime_eq_one hp
  have hsum := Equiv.Perm.sum_cycleType (fullPlanePerm g)
  rw [hc, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, hs,
    Finset.card_univ, fullWeightScalarPlane_card] at hsum
  have hcard : (fullPlanePerm g).cycleType.card = 3 := by omega
  rw [hcard] at hc
  exact hc

end Representation.Hexacode
