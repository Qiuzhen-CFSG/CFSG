module

public import Theory.AtlasPort.LinearGroups.G2.DerivedNormalizerSolvable.Binary
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.MarkedRestriction
public import Theory.SpecificGroups.FFG2PrimeCore

/-!
# The center of the actual derived binary G₂ group

The actual commutator subgroup D of the split-octonion group G₂(2) has
trivial center. Its Sylow two-subgroup S is self-normalizing, so Z(D)
is a two-group contained in S. A nontrivial Z(D) would contain an
involution. The calculation of Ω₁(Z(S)) identifies this involution with
the distinguished root element z, but an explicit element of D moves z.

Consequently the center is a three-group. With the quasisimplicity inherited
from the source classification, the existing order and normal-subgroup
reduction gives O₃′(D) = 1.

Source application: Aschbacher–Smith, combined 1 March 2004 manuscript,
B.5.6(1), printed p.105, and 15.4.18, printed p.1163. The intrinsic
Sylow geometry and marked root elements are reused from the licensed
ATLAS port; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section

open Subgroup Atlas.G2.BinaryParabolicPair Atlas.G2.BinaryCore Theory.GroupTheory

namespace Theory.SpecificGroups

/-- The actual commutator of the binary split-octonion group is centerless. -/
theorem g2_derived_two_center_eq_bot :
    center (commutator (Atlas.G2.Model (ZMod 2))) = ⊥ := by
  classical
  have hZS : center DerivedModel ≤ (derivedSylow : Subgroup DerivedModel) := by
    rw [← Atlas.G2.DerivedNormalizerSolvable.binary_normalizer_derivedSylow]
    exact center_le_normalizer _
  have hZP : IsPGroup 2 (center DerivedModel) := derivedSylow.isPGroup'.to_le hZS
  by_contra hZ
  have htwo : 2 ∣ Nat.card (center DerivedModel) := hZP.card_eq_or_dvd.resolve_left
    (fun h => hZ (Subgroup.card_eq_one.mp h))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := center DerivedModel) 2 htwo
  have hxpow : x ^ 2 = 1 := by
    simpa only [hx] using pow_orderOf_eq_one x
  have hxne : (x : DerivedModel) ≠ 1 := by
    intro h
    have he : x = 1 := Subtype.ext h
    rw [he, orderOf_one] at hx
    norm_num at hx
  let xs : (derivedSylow : Subgroup DerivedModel) := ⟨x, hZS x.property⟩
  have hxs : xs ∈ center (derivedSylow : Subgroup DerivedModel) := by
    apply mem_center_iff.mpr
    intro g
    exact Subtype.ext (mem_center_iff.mp x.property g.val)
  have hxo : (⟨xs, hxs⟩ : center (derivedSylow : Subgroup DerivedModel)) ∈
      omega₁ (center (derivedSylow : Subgroup DerivedModel)) (p := 2) := by
    apply Subgroup.subset_closure
    change (⟨xs, hxs⟩ : center (derivedSylow : Subgroup DerivedModel)) ^ (2 ^ 1) = 1
    apply Subtype.ext
    apply Subtype.ext
    change (x : DerivedModel) ^ (2 ^ 1) = 1
    simpa only [pow_one, Subgroup.coe_pow, Subgroup.coe_one] using
      congrArg (fun y : center DerivedModel => (y : DerivedModel)) hxpow
  have hxD : (x : DerivedModel) ∈ derivedDistinguished := by
    rw [← derivedSylow_omega_center_in_model]
    exact ⟨xs, ⟨⟨xs, hxs⟩, hxo, rfl⟩, rfl⟩
  have hxz : (x : DerivedModel) = ⟨z, rootA_one_mem_commutator⟩ := by
    have hm : x.val.val ∈ zpowers z := hxD
    have hr := mem_zpowers_iff_mem_range_orderOf.mp hm
    rw [z_order] at hr
    obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hr
    have hnlt : n < 2 := Finset.mem_range.mp hn
    have hn1 : n = 1 := by
      by_contra h
      have hn0 : n = 0 := by omega
      apply hxne
      apply Subtype.ext
      simpa [hn0] using he.symm
    apply Subtype.ext
    simpa [hn1] using he.symm
  apply movingActor_derived_moves
  have hcomm := mem_center_iff.mp x.property
    (⟨movingActor, movingActor_mem_derived⟩ : DerivedModel)
  rw [hxz] at hcomm
  rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]

/-- The center input for the binary derived model in the FF alternatives. -/
theorem g2_derived_two_center_isThreeGroup :
    IsPGroup 3 (center (commutator (Atlas.G2.Model (ZMod 2)))) := by
  rw [g2_derived_two_center_eq_bot]
  exact IsPGroup.of_bot

/-- Source quasisimplicity and the proved center calculation eliminate O₃′. -/
theorem g2_derived_two_threePrimeCore
    [IsQuasisimple (commutator (Atlas.G2.Model (ZMod 2)))] :
    pPrimeCore 3 (commutator (Atlas.G2.Model (ZMod 2))) = ⊥ :=
  g2_derived_two_threePrimeCore_of_center g2_derived_two_center_isThreeGroup

end Theory.SpecificGroups
