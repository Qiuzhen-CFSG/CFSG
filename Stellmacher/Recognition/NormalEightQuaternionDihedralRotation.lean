module

public import Stellmacher.Recognition.NormalEightQuaternionDihedralSetup
public import Theory.GroupTheory.NormalSubgroupInvolutionFiber
public import Theory.GroupTheory.QuaternionCentralProductOuterInvolution
public import Theory.GroupTheory.QuaternionCentralProductSquareAction

/-!
# The action in the quaternion rotation fiber

An involution outside the core in the rotation preimage maps to the half-turn.
A lift of the quarter-turn shows that its core action is a square modulo inner
automorphisms. The lifted action has two-power order, and self-centrality of
the core shows that the involution action is not inner.

The conditional assembly below reduces the desired fixed four and single
involution orbit to an intrinsic automorphism calculation on the quaternion
central product. Fixed subgroups and cocycles are transported through the
actual core equivalence, so the conclusion concerns the original Sylow.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, the square actor calculation
on printed p.391 and case (c) on printed p.392. No bound on arbitrary
elementary subgroups is used.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage

open Subgroup NormalFourCentralOmegaTwo

variable {G : Type*} [Group G] [Finite G]

/-- The original Sylow action expressed on the actual quotient core. -/
@[expose] public noncomputable def quaternionDihedralCoreAction (S : Sylow 2 G) :
    S →* MulAut (pCore 2 (OmegaQuotient S)) :=
  normalConjThrough (omegaCorePreimage S) (omegaCorePreimageEquiv S)

/-- An outside-core rotation involution acts as a non-inner square modulo
inner automorphisms, with a square root of two-power order. -/
public theorem quaternionDihedral_rotation_action_data
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (e : (S ⧸ omegaCorePreimage S) ≃* DihedralGroup 4)
    (u : S) (huM : u ∈ quaternionDihedralMaximal S e)
    (huP : u ∉ omegaCorePreimage S) (hu : orderOf u = 2) :
    (quaternionDihedralCoreAction S u) ^ 2 = 1 ∧
      (¬ ∃ q, quaternionDihedralCoreAction S u = MulAut.conj q) ∧
      ∃ (β : MulAut (pCore 2 (OmegaQuotient S)))
        (q : pCore 2 (OmegaQuotient S)) (n : ℕ),
        β ^ (2 ^ n) = 1 ∧ quaternionDihedralCoreAction S u = MulAut.conj q * β ^ 2 := by
  let P := omegaCorePreimage S
  let a := quaternionDihedralCoreAction S
  let f := quaternionDihedralHom S e
  have hu2 : u ^ 2 = 1 := by simpa only [hu] using pow_orderOf_eq_one u
  have hcentral : centralizer (P : Set S) ≤ P := by
    intro s hs
    apply omegaQuotient_centralizer_pCore_le hN S hZ
    intro x hx
    rw [← omegaCorePreimage_map S] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    simpa only [map_mul] using congrArg (omegaQuotientHom S) (hs k hk)
  refine ⟨by rw [← map_pow, hu2, map_one],
    normalConjThrough_not_inner P (omegaCorePreimageEquiv S) hcentral u huP, ?_⟩
  have hfu : f u = DihedralGroup.r 2 :=
    DihedralGroup.image_eq_r_two_of_rotation_involution f u hu huM
      (fun h => huP ((quaternionDihedralHom_eq_one_iff S e u).mp h))
  obtain ⟨s, hs⟩ := quaternionDihedralHom_surjective S e (DihedralGroup.r 1)
  have hs2 : f (s ^ 2) = f u := by
    rw [map_pow, hs, hfu, DihedralGroup.r_one_pow]
    rfl
  have hp : u * (s ^ 2)⁻¹ ∈ P := by
    apply (quaternionDihedralHom_eq_one_iff S e _).mp
    change f (u * (s ^ 2)⁻¹) = 1
    rw [map_mul, map_inv, hs2, mul_inv_cancel]
  let p : P := ⟨u * (s ^ 2)⁻¹, hp⟩
  obtain ⟨n, hn⟩ := S.isPGroup'.exists_pow_pow_eq_one s
  refine ⟨a s, omegaCorePreimageEquiv S p, n, ?_, ?_⟩
  · rw [← map_pow, hn, map_one]
  · have hup : u = (p : S) * s ^ 2 := by simp [p]
    change a u = _
    rw [hup, map_mul, map_pow]
    congr 1
    exact normalConjThrough_coe P (omegaCorePreimageEquiv S) p

/-- The intrinsic square-action calculation supplies precisely the rotation
premise used by the geometry assembly. Its discharge is quaternion mathematics. -/
public theorem quaternion_dihedral_rotation_of_action_calculation
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (e : (S ⧸ omegaCorePreimage S) ≃* DihedralGroup 4)
    (hcalc : ∀ (α β : MulAut (pCore 2 (OmegaQuotient S)))
      (q : pCore 2 (OmegaQuotient S)) (n : ℕ),
      α ^ 2 = 1 → (¬ ∃ p, α = MulAut.conj p) →
      β ^ (2 ^ n) = 1 → α = MulAut.conj q * β ^ 2 →
      IsElementaryAbelian 2 (α.toMonoidHom.eqLocus (MonoidHom.id _)) ∧
      Nat.card (α.toMonoidHom.eqLocus (MonoidHom.id _)) = 4 ∧
      ∀ x, x * α x = 1 → ∃ p, x = p * α p⁻¹) :
    ∀ u : S, u ∈ quaternionDihedralMaximal S e →
      u ∉ omegaCorePreimage S → orderOf u = 2 →
      IsElementaryAbelian 2 (omegaCorePreimage S ⊓ centralizer ({u} : Set S) : Subgroup S) ∧
      Nat.card (omegaCorePreimage S ⊓ centralizer ({u} : Set S) : Subgroup S) = 4 ∧
      ∀ v : S, orderOf v = 2 →
        quaternionDihedralHom S e v = quaternionDihedralHom S e u →
        ∃ p : omegaCorePreimage S, (p : S) * u * (p : S)⁻¹ = v := by
  intro u huM huP hu
  obtain ⟨ha2, haout, β, q, n, hb, hab⟩ :=
    quaternionDihedral_rotation_action_data hN S hZ e u huM huP hu
  obtain ⟨helem, hcard, horbit⟩ := hcalc _ β q n ha2 haout hb hab
  obtain ⟨helem', hcard'⟩ := normalConjThrough_fixed_elementary_card
    (omegaCorePreimage S) (omegaCorePreimageEquiv S) u 4 helem hcard
  refine ⟨helem', hcard', ?_⟩
  intro v hv hf
  apply normalConjThrough_involution_orbit (omegaCorePreimage S)
    (omegaCorePreimageEquiv S) u (by simpa only [hu] using pow_orderOf_eq_one u)
    horbit v (by simpa only [hv] using pow_orderOf_eq_one v)
  apply (quaternionDihedralHom_eq_one_iff S e _).mp
  rw [map_mul, map_inv, hf, mul_inv_cancel]

/-! The two intrinsic quaternion calculations discharge the abstract action
premise above.  The factors live in the order-32 quotient core, so the
transport through `omegaCorePreimageEquiv` is already built into the action
data theorem. -/

public theorem quaternion_dihedral_rotation_of_quaternion_factors
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (e : (S ⧸ omegaCorePreimage S) ≃* DihedralGroup 4)
    (B C : Subgroup (pCore 2 (OmegaQuotient S)))
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤)
    (hinter : Nat.card (B ⊓ C : Subgroup (pCore 2 (OmegaQuotient S))) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b) :
    ∀ u : S, u ∈ quaternionDihedralMaximal S e →
      u ∉ omegaCorePreimage S → orderOf u = 2 →
      IsElementaryAbelian 2 (omegaCorePreimage S ⊓ centralizer ({u} : Set S) : Subgroup S) ∧
      Nat.card (omegaCorePreimage S ⊓ centralizer ({u} : Set S) : Subgroup S) = 4 ∧
      ∀ v : S, orderOf v = 2 →
        quaternionDihedralHom S e v = quaternionDihedralHom S e u →
        ∃ p : omegaCorePreimage S, (p : S) * u * (p : S)⁻¹ = v := by
  let H := pCore 2 (OmegaQuotient S)
  have hcalc : ∀ (α β : MulAut H) (q : H) (n : ℕ),
      α ^ 2 = 1 → (¬ ∃ p, α = MulAut.conj p) →
      β ^ (2 ^ n) = 1 → α = MulAut.conj q * β ^ 2 →
      IsElementaryAbelian 2 (α.toMonoidHom.eqLocus (MonoidHom.id _)) ∧
      Nat.card (α.toMonoidHom.eqLocus (MonoidHom.id _)) = 4 ∧
      ∀ x, x * α x = 1 → ∃ p, x = p * α p⁻¹ := by
    intro α β q n hα hout hβ hαβ
    have hs := quaternion_central_product_square_action B C hB hC hjoin hinter hcomm
      α β q n hβ hαβ hout
    have ho := quaternion_central_product_outer_involution B C hB hC hjoin hinter hcomm
      α hα hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
    exact ho
  exact quaternion_dihedral_rotation_of_action_calculation hN S hZ e hcalc

/-! A wrapper retaining the full local hypotheses used in the recognition
argument.  The rotation calculation itself only needs the displayed
quaternion factors, but keeping this interface lets the downstream geometry
pass its original local data unchanged. -/

public theorem quaternion_dihedral_rotation_hrotation
    [IsSimpleGroup G]
    (_hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (A : Subgroup S) [IsElementaryAbelian 2 A] (_hA : 8 ≤ Nat.card A)
    (_hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (_hW : Nat.card W = 4)
    (_hno : ¬ ∃ F : Subgroup S, F.Normal ∧ IsElementaryAbelian 2 F ∧
      8 ≤ Nat.card F)
    (_hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (_hnormal : ¬ (fourImage S W).Normal)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (_hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (_hindex : 4 ≤ (omegaCorePreimage S).index)
    (B C : Subgroup (pCore 2 (OmegaQuotient S)))
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤)
    (hinter : Nat.card (B ⊓ C : Subgroup (pCore 2 (OmegaQuotient S))) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (z t : S) (_hz : orderOf z = 2) (_hzc : z ∈ center S)
    (_ht : orderOf t = 2) (_htP : t ∉ omegaCorePreimage S)
    (_hzt : IsConj (z : G) (t : G))
    (e : (S ⧸ omegaCorePreimage S) ≃* DihedralGroup 4) :
    ∀ u : S, u ∈ quaternionDihedralMaximal S e →
      u ∉ omegaCorePreimage S → orderOf u = 2 →
      IsElementaryAbelian 2 (omegaCorePreimage S ⊓ centralizer ({u} : Set S) : Subgroup S) ∧
      Nat.card (omegaCorePreimage S ⊓ centralizer ({u} : Set S) : Subgroup S) = 4 ∧
      ∀ v : S, orderOf v = 2 →
        quaternionDihedralHom S e v = quaternionDihedralHom S e u →
        ∃ p : omegaCorePreimage S, (p : S) * u * (p : S)⁻¹ = v := by
  exact quaternion_dihedral_rotation_of_quaternion_factors hN S hZ e B C hB hC hjoin hinter hcomm

end Stellmacher.Recognition.NormalEightNonnormalImage
