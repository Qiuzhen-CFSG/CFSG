module

public import Theory.AtlasPort.LinearGroups.G2.BinarySecondParabolic

/-!
# The natural four in the binary second parabolic

The coordinate plane `c=d=e=0` has order four and lies in the elementary
eight of `BinaryCore`. It is invariant under the second parabolic and is
minimal among invariant subgroups containing the distinguished involution.
Thus it realizes the conjugate-generated natural subgroup in the source.
The proofs use the explicit conjugation formulas of `BinarySecondParabolic`.

Source: Aschbacher–Smith, Hypothesis 14.2.1(4) and Lemma 14.2.21,
printed pp.981 and 988. Root conventions follow the licensed ATLAS port.
-/

@[expose] public section

namespace Atlas.G2.BinaryCore
open Atlas.G2.Explicit
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def naturalCoordinates : Subgroup Coordinates where
  carrier := {x | x.c = 0 ∧ x.d = 0 ∧ x.e = 0}
  one_mem' := by decide +kernel
  mul_mem' := by
    intro x y hx hy
    change (x*y).c = 0 ∧ (x*y).d = 0 ∧ (x*y).e = 0
    simp [hx.1, hx.2.1, hx.2.2, hy.1, hy.2.1, hy.2.2]
  inv_mem' := by
    intro x hx
    change -x.c = 0 ∧ -x.d = 0 ∧ -x.e = 0
    simp [hx.1, hx.2.1, hx.2.2]
instance : DecidablePred (· ∈ naturalCoordinates) := fun _ =>
  inferInstanceAs (Decidable (_ = (0 : ZMod 2) ∧ _ = (0 : ZMod 2) ∧ _ = (0 : ZMod 2)))

theorem naturalCoordinates_le_elementary : naturalCoordinates ≤ elementaryCoordinates :=
  fun _ h => h.2

def natural : Subgroup (Model (ZMod 2)) := naturalCoordinates.map embedding

theorem natural_le_elementary : natural ≤ elementary :=
  Subgroup.map_mono naturalCoordinates_le_elementary

theorem card_natural : Nat.card natural = 4 := by
  change Nat.card (naturalCoordinates.map embedding) = 4
  rw [← Nat.card_congr (naturalCoordinates.equivMapOfInjective embedding embedding_injective).toEquiv,
    Nat.card_eq_fintype_card]
  decide +kernel

theorem z_mem_natural : z ∈ natural :=
  ⟨involution, ⟨rfl, rfl, rfl⟩, embedding_involution⟩

theorem unipotent_normalizes_natural : unipotent (K := ZMod 2) ≤ Subgroup.normalizer (natural : Set (Model (ZMod 2))) := by
  rw [Subgroup.le_normalizer_iff]
  intro g hg x hx
  rw [unipotent_eq_range] at hg
  obtain ⟨t, rfl⟩ := hg
  obtain ⟨x, hx, rfl⟩ := hx
  let xe : elementaryCoordinates := ⟨x, hx.2⟩
  refine ⟨unipotentConjugate t xe, ⟨hx.1, rfl, rfl⟩, ?_⟩
  change unipotentProduct (parameters (unipotentConjugate t xe)) =
    unipotentProduct t * unipotentProduct (parameters x) * (unipotentProduct t)⁻¹
  rw [unipotentProduct_inv, unipotentProduct_mul, unipotentProduct_mul,
    unipotent_conjugate_parameters t xe]

theorem weylR_normalizes_natural : (weylR : Model (ZMod 2)) ∈ Subgroup.normalizer (natural : Set (Model (ZMod 2))) := by
  have hf : ∀ a ∈ natural, (weylR : Model (ZMod 2))*a*weylR⁻¹ ∈ natural := by
    rintro _ ⟨x,hx,rfl⟩
    exact ⟨weylConjugate ⟨x,hx.2⟩, ⟨hx.1,rfl,rfl⟩,
      (weyl_conjugate_elementary ⟨x,hx.2⟩).symm⟩
  apply Subgroup.mem_normalizer_iff.mpr
  intro g
  constructor
  · exact hf g
  · intro hg
    have hww : (weylR : Model (ZMod 2)) * weylR = 1 := by
      simpa [pow_two] using (weylR_sq (K := ZMod 2))
    have h := hf _ hg
    have heq : (weylR : Model (ZMod 2)) * (weylR * g * weylR⁻¹) * weylR⁻¹ = g := by
      calc
        _ = (weylR * weylR) * g * (weylR * weylR)⁻¹ := by group
        _ = g := by rw [hww]; simp
    rwa [heq] at h

theorem secondParabolic_normalizes_natural : secondParabolic ≤ Subgroup.normalizer (natural : Set (Model (ZMod 2))) := by
  have htorus : splitTorus (K := ZMod 2) ≤ Subgroup.normalizer (natural : Set (Model (ZMod 2))) := by
    rintro g ⟨p,rfl⟩
    have hp : ∀ p : (ZMod 2)ˣ × (ZMod 2)ˣ, p = 1 := by decide +kernel
    rw [hp p, map_one]
    exact Subgroup.one_mem _
  exact sup_le (sup_le unipotent_normalizes_natural htorus)
    ((Subgroup.closure_le _).mpr (by simpa using weylR_normalizes_natural))

theorem elementary_le_secondParabolic : elementary ≤ secondParabolic :=
  elementary_le_core.trans (core_le_unipotent.trans unipotent_le_parabolic)

instance elementary_normal : (elementary.subgroupOf secondParabolic).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer secondParabolic_normalizes_elementary

instance natural_normal : (natural.subgroupOf secondParabolic).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer secondParabolic_normalizes_natural

/-- Every invariant subgroup containing the distinguished involution contains V. -/
theorem natural_minimal (D : Subgroup (Model (ZMod 2)))
    (hD : secondParabolic ≤ Subgroup.normalizer (D : Set (Model (ZMod 2)))) (hz : z ∈ D) : natural ≤ D := by
  have hw : (weylR : Model (ZMod 2)) * z * weylR⁻¹ ∈ D :=
    (Subgroup.mem_normalizer_iff.mp (hD weylR_mem_parabolic) z).mp hz
  have he : embedding (weylConjugate ⟨involution, involution_mem_elementary⟩) ∈ D := by
    rw [← weyl_conjugate_elementary, embedding_involution]
    exact hw
  rintro _ ⟨x, hx, rfl⟩
  have hc : ∀ x : naturalCoordinates,
      x.val = 1 ∨ x.val = involution ∨
      x.val = weylConjugate ⟨involution, involution_mem_elementary⟩ ∨
      x.val = involution * weylConjugate ⟨involution, involution_mem_elementary⟩ := by
    decide +kernel
  rcases hc ⟨x, hx⟩ with h | h | h | h
  · change x = _ at h
    rw [h, map_one]; exact D.one_mem
  · change x = _ at h
    rw [h, embedding_involution]; exact hz
  · change x = _ at h
    rw [h]; exact he
  · change x = _ at h
    rw [h, map_mul, embedding_involution]; exact D.mul_mem hz he


theorem z_order : orderOf z = 2 := by
  apply orderOf_eq_prime
  · rw [z, ← embedding_involution, ← map_pow, involution_sq, map_one]
  · exact z_ne_one

/-- The marked order-two subgroup; its identification with Ω₁(Z(T)) belongs
  to the common-Sylow calculation. -/
def distinguished : Subgroup (Model (ZMod 2)) := Subgroup.zpowers z

theorem card_distinguished : Nat.card distinguished = 2 := by
  rw [distinguished, Nat.card_zpowers, z_order]

theorem distinguished_le_natural : distinguished ≤ natural :=
  Subgroup.zpowers_le.mpr z_mem_natural

theorem movingActor_order : orderOf movingActor = 3 := by
  apply orderOf_eq_prime movingActor_cube
  intro h
  apply movingActor_moves
  simp [h]

theorem z_centralizes_core (q : Model (ZMod 2)) (hq : q ∈ core) : q * z = z * q := by
  obtain ⟨x, rfl⟩ := hq
  rw [z, ← embedding_involution, ← map_mul, ← map_mul]
  congr 1
  exact Subgroup.mem_center_iff.mp involution_mem_center x

theorem secondParabolic_card : Nat.card secondParabolic = 192 := by
  change Nat.card (parabolic (F := ZMod 2)) = 192
  rw [card_parabolic, Nat.card_eq_fintype_card, ZMod.card]
  norm_num

end Atlas.G2.BinaryCore
