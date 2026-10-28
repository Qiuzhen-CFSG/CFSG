module

public import Theory.SpecificGroups.ReeTwo.SemilinearExtensionData
public import Theory.SpecificGroups.ReeTwo.OrbitCommutatorRigidity

/-!
# Intrinsic transport of the semilinear orbit commutators

Normalize the doubling symmetry at the seed, then pass to the quotient by the
center. The derived subgroup becomes central with exponent two, so its cosets
may be substituted inside commutators. Orbit shifts and doubling give the five
remaining commutators and the two compatibility identities. Restriction to the
center transports binary words with columns `[2,4,8,15]` and `[1,4,15,2]`.

No tail-coordinate injectivity, spanning, or model recognition is used.
The calculation follows Parrott (1972), pp.672–674, with the right-commutator
convention of Shinoda (1975), pp.81–82.
-/

@[expose] public section
namespace ReeTwo
open Subgroup
open scoped IsMulCommutative commutatorElement

private theorem rc_map {G H M : Type*} [Group G] [Group H]
    [FunLike M G H] [MonoidHomClass M G H] (f : M) (x y : G) :
    f (rightComm x y) = rightComm (f x) (f y) := by
  simp only [rightComm, map_mul, map_inv]

private theorem rc_left {H : Type*} [Group H]
    (hc : ∀ x y : H, rightComm x y ∈ center H) (x y w : H) :
    rightComm (x*y) w = rightComm x w * rightComm y w := by
  have hh := mem_center_iff.mp (hc x w) y
  calc
    _ = y⁻¹ * rightComm x w * y * rightComm y w := by simp [rightComm, mul_assoc]
    _ = _ := by rw [mul_assoc y⁻¹, ← hh]; simp

private theorem rc_symm {H : Type*} [Group H]
    (he : ∀ x y : H, rightComm x y * rightComm x y = 1) (x y : H) :
    rightComm x y = rightComm y x := by
  have hi : (rightComm x y)⁻¹ = rightComm x y := inv_eq_of_mul_eq_one_right (he x y)
  rw [← hi]
  simp [rightComm, mul_assoc]

private theorem rc_congr_left {H : Type*} [Group H]
    (hc : ∀ x y : H, rightComm x y ∈ center H)
    {x y : H} (hxy : x / y ∈ center H) (w : H) :
    rightComm x w = rightComm y w := by
  have hz : rightComm (x/y) w = 1 := by
    apply (rightComm_eq_one_iff_commute _ _).mpr
    exact (mem_center_iff.mp hxy w).symm
  calc
    _ = rightComm ((x/y)*y) w := by rw [div_mul_cancel]
    _ = _ := by rw [rc_left hc, hz, one_mul]

private def quotientCenterAut {K : Type*} [Group K] (f : MulAut K) :
    MulAut (K ⧸ center K) :=
  QuotientGroup.congr (center K) (center K) f
    (characteristic_iff_map_eq.mp inferInstance f)

private theorem transport_algebra {H : Type*} [Group H]
    (hc : ∀ x y : H, rightComm x y ∈ center H)
    (he : ∀ x y : H, rightComm x y * rightComm x y = 1)
    (U : ℕ → H) (T : H) (F S : MulAut H)
    (hF : ∀ n, F (U n) = U (n+1)) (hFT : F T = T)
    (hperiod : ∀ n, U (n+5) = U n)
    (hS : ∀ i j, S (rightComm (U i) (U j)) = rightComm (U (2*i)) (U (2*j)))
    (hST : ∀ i, S (rightComm (U i) T) = rightComm (U (2*i)) T)
    (hrel : ∀ x, rightComm (U 4) x = rightComm (U 0 * U 1 * U 2 * U 3) x) :
    Nonempty (OrbitCommutatorTransport (fun i : Fin 4 => U i.val) T) := by
  let d : Fin 4 → center H := fun i => ⟨rightComm (U i.val) T, hc _ _⟩
  let FC : center H →* center H := (MulAut.characteristic (center H) F).toMonoidHom
  let SC : center H →* center H := (MulAut.characteristic (center H) S).toMonoidHom
  have hd (i) : d i * d i = 1 := Subtype.ext (he _ _)
  have hshift (i j) : F (rightComm (U i) (U j)) = rightComm (U (i+1)) (U (j+1)) := by
    rw [rc_map F, hF, hF]
  have htshift (i) : F (rightComm (U i) T) = rightComm (U (i+1)) T := by
    rw [rc_map F, hF, hFT]
  have h5 : U 5 = U 0 := hperiod 0
  have h6 : U 6 = U 1 := hperiod 1
  have htail : rightComm (U 4) T =
      rightComm (U 0) T * rightComm (U 1) T * rightComm (U 2) T * rightComm (U 3) T := by
    rw [hrel]; simp only [rc_left hc]
  have hfcol : ∀ i, FC (d i) = binaryWord4 d (orbitFive (Pi.single i 1)) := by
    intro i
    apply Subtype.ext
    change F (rightComm (U i.val) T) = _
    rw [htshift]
    fin_cases i <;> simp [binaryWord4, orbitFive, d, htail]
  have hscol : ∀ i, SC (d i) = binaryWord4 d (orbitSymmetry (Pi.single i 1)) := by
    intro i
    apply Subtype.ext
    change S (rightComm (U i.val) T) = _
    rw [hST]
    fin_cases i <;> simp [binaryWord4, orbitSymmetry, d, htail, h6]
  have word (e : OrbitBits) :
      ((binaryWord4 d e : center H) : H) = binaryWord4 (fun i : Fin 4 => rightComm (U i.val) T) e := by
    simp [binaryWord4, d]
  have h02 : rightComm (U 0) (U 2) = S (rightComm (U 0) (U 1)) := by
    simpa using (hS 0 1).symm
  have h03 : rightComm (U 0) (U 3) = F (F (F (S (rightComm (U 0) (U 1))))) := by
    rw [← h02, hshift, hshift, hshift]
    simp only [h5]
    exact rc_symm he _ _
  have h12 : rightComm (U 1) (U 2) = F (rightComm (U 0) (U 1)) := (hshift 0 1).symm
  have h13 : rightComm (U 1) (U 3) = F (S (rightComm (U 0) (U 1))) := by
    rw [← h02, hshift]
  have h23 : rightComm (U 2) (U 3) = F (F (rightComm (U 0) (U 1))) := by
    rw [hshift, hshift]
  refine ⟨{ five := F.toMonoidHom
            symmetry := S.toMonoidHom
            word_add := ?_
            map_five := ?_
            map_symmetry := ?_
            comm02 := h02
            comm03 := h03
            comm12 := h12
            comm13 := h13
            comm23 := h23
            five_constraint := ?_
            symmetry_constraint := ?_ }⟩
  · intro e f
    exact (word (e+f)).symm.trans ((congrArg Subtype.val (binaryWord4_add d hd e f)).trans (by rw [Subgroup.coe_mul, word, word]))
  · intro e
    have hh := congrArg Subtype.val (binaryWord4_map_five d hd FC hfcol e)
    change F ((binaryWord4 d e : center H) : H) = ((binaryWord4 d (orbitFive e) : center H) : H) at hh
    simpa only [word, MulEquiv.coe_toMonoidHom] using hh
  · intro e
    have hh := congrArg Subtype.val (binaryWord4_map_symmetry d hd SC hscol e)
    change S ((binaryWord4 d e : center H) : H) = ((binaryWord4 d (orbitSymmetry e) : center H) : H) at hh
    simpa only [word, MulEquiv.coe_toMonoidHom] using hh
  · change F (F (F (F (S (rightComm (U 0) (U 1)))))) =
        rightComm (U 0) (U 1) * F (rightComm (U 0) (U 1)) * F (S (rightComm (U 0) (U 1)))
    rw [← h03, hshift, ← h12, ← h13, rc_symm he (U 1) (U 4), hrel]
    simp only [rc_left hc]
    rw [rc_symm he (U 2) (U 1), rc_symm he (U 3) (U 1)]
    simp [rightComm]
  · change S (S (rightComm (U 0) (U 1))) = _
    rw [← h02, hS]
    change rightComm (U 0) (U 4) = _
    rw [rc_symm he (U 0) (U 4), hrel]
    simp only [rc_left hc]
    rw [rc_symm he (U 1), rc_symm he (U 2), rc_symm he (U 3), h02, h03]
    simp [rightComm]

variable {K A : Type*} [Group K] [Group A] [Finite K] [Finite A]

/-- The intrinsic five-action and normalized doubling symmetry transport all
orbit commutators and binary root-displacement words. Only the fifth-orbit
relation modulo the derived subgroup is required. -/
theorem SemilinearExtensionData.orbitCommutatorTransport_of_fifthRelation
    {ρ : A →* MulAut K} {R : Subgroup K} {t z : K} {b : R} {σ : MulAut K}
    (h : SemilinearExtensionData ρ R t z b σ) (g : A) (_hg : g ≠ 1)
    (hrel : ρ (g^4) (b : K) /
      (ρ (g^0) (b : K) * ρ (g^1) (b : K) * ρ (g^2) (b : K) * ρ (g^3) (b : K)) ∈
        commutator K) :
    Nonempty (OrbitCommutatorTransport
      (fun i : Fin 4 => QuotientGroup.mk' (center K) (ρ (g^i.val) (b : K)))
      (QuotientGroup.mk' (center K) t)) := by
  let q := QuotientGroup.mk' (center K)
  let B : ℕ → K := fun n => ρ (g^n) (b : K)
  let U : ℕ → K ⧸ center K := fun n => q (B n)
  let D := (commutator R).map R.subtype
  let _ : IsElementaryAbelian 2 D := h.derived_elementary
  have hDZ : ⁅D, (⊤ : Subgroup K)⁆ ≤ center K := by
    rw [h.center_eq]
    exact h.derived_commutator.le
  obtain ⟨hc, he⟩ := centralQuotient_rightComm_laws D h.derived_eq.ge hDZ
  have hcentral (x : K) (hx : x ∈ D) : q x ∈ center (K ⧸ center K) := by
    apply mem_center_iff.mpr
    intro w
    induction w using QuotientGroup.induction_on with | H w =>
      apply commutatorElement_eq_one_iff_mul_comm.mp
      change ⁅q w, q x⁆ = 1
      rw [← map_commutatorElement]
      apply (QuotientGroup.eq_one_iff _).mpr
      apply hDZ
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator (mem_top w) hx
  have hcongr {x y : K} (hxy : x/y ∈ D) (w : K ⧸ center K) :
      rightComm (q x) w = rightComm (q y) w := by
    apply rc_congr_left hc
    rw [← map_div]
    exact hcentral _ hxy
  obtain ⟨a, hn, hseed⟩ := exists_seed_normalized_symmetry ρ R t z b σ h
  let s := ρ a * σ
  let F := quotientCenterAut (ρ g)
  let S := quotientCenterAut s
  have hF (n) : F (U n) = U (n+1) := by
    change q (ρ g (ρ (g^n) (b : K))) = q (ρ (g^(n+1)) (b : K))
    rw [pow_succ', map_mul]
    rfl
  have hFT : F (q t) = q t := by
    change q (ρ g t) = q t
    rw [h.root_fixed]
  have hg5 : g^5 = 1 := by rw [← h.actor_card]; exact pow_card_eq_one'
  have hperiod (n) : U (n+5) = U n := by
    simp only [U, B, pow_add, hg5, mul_one]
  have hs (i) : s (B i) / B (2*i) ∈ D := by
    have hh := hn.symmetry_orbit_coset hseed (g^i)
    simpa only [B, D, s, ← pow_mul, Nat.mul_comm i 2] using hh
  have hS (i j) : S (rightComm (U i) (U j)) = rightComm (U (2*i)) (U (2*j)) := by
    rw [rc_map S]
    change rightComm (q (s (B i))) (q (s (B j))) = _
    rw [hcongr (hs i), rc_symm he, hcongr (hs j), rc_symm he]
  have hST (i) : S (rightComm (U i) (q t)) = rightComm (U (2*i)) (q t) := by
    change S (rightComm (q (B i)) (q t)) = _
    rw [← rc_map q]
    change q (s (rightComm (B i) t)) = _
    rw [hn.root_displacement_equivariant, rc_map q, hcongr (hs i)]
  have hrelation (x) : rightComm (U 4) x = rightComm (U 0 * U 1 * U 2 * U 3) x := by
    change rightComm (q (B 4)) x = _
    have hh : B 4 / (B 0 * B 1 * B 2 * B 3) ∈ D := by
      change _ ∈ (commutator R).map R.subtype
      rw [h.derived_eq]
      exact hrel
    rw [hcongr hh]
    simp only [map_mul, U]
  exact transport_algebra hc he U (q t) F S hF hFT hperiod hS hST hrelation

end ReeTwo
