/-
The normalized-partner correction is adapted from work Copyright (c) 2026
Gerald Höhn. All rights reserved. ATLAS revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
That portion is covered by the ATLAS Research and Attribution License 1.0
(LICENSES/ATLAS.txt).
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.SplitOddCentralizers.IsometryQuotients.Quotient
public import Theory.SpecificGroups.ClassicalOrthogonal.RankOneComparison.Image

/-!
# The ternary full isometry quotient

Elementary SL₂ conjugation is transitive on singular lines. A Siegel correction
then reduces an isometry, modulo the elementary subgroup, to one scaling the
standard hyperbolic pair. On its perpendicular line the square is identity;
on the pair its square is the image of a diagonal SL₂ matrix. Thus the full
isometry quotient has exponent two, without a Witt-index-two hypothesis or
perfectness. This includes Ω₃(3).

Source: GLS3 §2.7. The normalized-partner correction reuses the proof of the
private correction in CFSG's `SplitOdd/ReflectionGeneration/JointGeneration`,
adapted from Gerald Höhn's ATLAS `QuadraticPairTransport.lean`, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917. That portion is covered by the
ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
-/

@[expose] public noncomputable section
universe u
open Theory.AlgebraicGroup
namespace ClassicalOrthogonal.Fundamental.SplitOddBlocks.IsometryQuotients.RankOne
open ClassicalOrthogonal.Quadratic ClassicalOrthogonal.ReflectionGeneration
open ClassicalOrthogonal.RankOneComparison Matrix
attribute [local instance] elementary_normal
variable {F : Type u} [Field F]

private abbrev eVec : VectorB 1 F := (e 0, 0)
private abbrev fVec : VectorB 1 F := (f 0, 0)
private abbrev zVec : VectorB 1 F := (0, 1)

private theorem vector_expansion (v : VectorB 1 F) :
    v = v.1 (.inl 0) • eVec + v.1 (.inr 0) • fVec + v.2 • zVec := by
  apply Prod.ext
  · ext i
    rcases i with i | i <;> fin_cases i <;> simp [eVec, fVec, zVec, e, f]
  · simp [eVec, fVec, zVec]

private theorem linear_ext (g h : VectorB 1 F →ₗ[F] VectorB 1 F)
    (he : g eVec = h eVec) (hf : g fVec = h fVec) (hz : g zVec = h zVec) : g = h := by
  apply LinearMap.ext
  intro v
  rw [vector_expansion v]
  simp only [map_add, map_smul, he, hf, hz]

private theorem polar_e (x : VectorB 1 F) :
    (formB 1 F).polarBilin x eVec = x.1 (.inr 0) := by
  rw [polarB_apply, polarD_e]
  simp only [mul_zero, add_zero]

private theorem polar_f (x : VectorB 1 F) :
    (formB 1 F).polarBilin x fVec = x.1 (.inl 0) := by
  rw [polarB_apply, polarD_f]
  simp only [mul_zero, add_zero]

private theorem diagonal_action (c : F) (hc : c ≠ 0) :
    (toOrthogonal (SpecialLinearGroup.diag2 c hc)).val eVec = c^2 • eVec ∧
    (toOrthogonal (SpecialLinearGroup.diag2 c hc)).val fVec = (c⁻¹)^2 • fVec ∧
    (toOrthogonal (SpecialLinearGroup.diag2 c hc)).val zVec = zVec := by
  constructor
  · apply Prod.ext
    · ext i
      rcases i with i | i <;> fin_cases i <;>
        simp [eVec, e, toOrthogonal, onB, coordinates, kernelAction, kernelMap,
          SpecialLinearGroup.diag2_coe', Matrix.adjugate_fin_two, pow_two]
    · simp [eVec, e, toOrthogonal, onB, coordinates, kernelAction, kernelMap,
        SpecialLinearGroup.diag2_coe', Matrix.adjugate_fin_two]
  constructor
  · apply Prod.ext
    · ext i
      rcases i with i | i <;> fin_cases i <;>
        simp [fVec, f, toOrthogonal, onB, coordinates, kernelAction, kernelMap,
          SpecialLinearGroup.diag2_coe', Matrix.adjugate_fin_two, pow_two]
    · simp [fVec, f, toOrthogonal, onB, coordinates, kernelAction, kernelMap,
        SpecialLinearGroup.diag2_coe', Matrix.adjugate_fin_two]
  · apply Prod.ext
    · ext i
      rcases i with i | i <;> fin_cases i <;>
        simp [zVec, toOrthogonal, onB, coordinates, kernelAction, kernelMap,
          SpecialLinearGroup.diag2_coe', Matrix.adjugate_fin_two]
    · simp [zVec, toOrthogonal, onB, coordinates, kernelAction, kernelMap,
        SpecialLinearGroup.diag2_coe', Matrix.adjugate_fin_two, hc]

private theorem pair_scaling_square_mem (g : quadraticIsometrySubgroup (formB 1 F))
    (c : F) (hc : c ≠ 0) (he : g.val eVec = c • eVec)
    (hf : g.val fVec = c⁻¹ • fVec) : g^2 ∈ elementarySubgroup (formB 1 F) := by
  let Q := formB 1 F
  have hye : (g.val zVec).1 (.inr 0) = 0 := by
    have h := isometry_polar Q (isometryCarrierEquiv Q g) zVec eVec
    change Q.polarBilin (g.val zVec) (g.val eVec) = Q.polarBilin zVec eVec at h
    rw [he, map_smul] at h
    change c * Q.polarBilin (g.val zVec) eVec = Q.polarBilin zVec eVec at h
    rw [polar_e, polar_e] at h
    exact (mul_eq_zero.mp h).resolve_left hc
  have hxf : (g.val zVec).1 (.inl 0) = 0 := by
    have h := isometry_polar Q (isometryCarrierEquiv Q g) zVec fVec
    change Q.polarBilin (g.val zVec) (g.val fVec) = Q.polarBilin zVec fVec at h
    rw [hf, map_smul] at h
    change c⁻¹ * Q.polarBilin (g.val zVec) fVec = Q.polarBilin zVec fVec at h
    rw [polar_f, polar_f] at h
    exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero hc)
  let s := (g.val zVec).2
  have hz : g.val zVec = s • zVec := by
    calc
      g.val zVec = _ := vector_expansion (g.val zVec)
      _ = s • zVec := by rw [hye, hxf, zero_smul, zero_smul, zero_add, zero_add]
  have hs : s ^ 2 = 1 := by
    have h := isometry_preserves Q g zVec
    rw [hz, Q.map_smul] at h
    have hqz : Q zVec = 1 := by simp [Q, zVec]
    rw [hqz] at h
    simpa only [smul_eq_mul, mul_one, pow_two] using h
  have heq : g^2 = toOrthogonal (SpecialLinearGroup.diag2 c hc) := by
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    apply linear_ext
    · change g.val (g.val eVec) = _
      rw [he, map_smul, he, smul_smul, ← pow_two]
      exact (diagonal_action c hc).1.symm
    · change g.val (g.val fVec) = _
      rw [hf, map_smul, hf, smul_smul, ← pow_two]
      exact (diagonal_action c hc).2.1.symm
    · change g.val (g.val zVec) = _
      rw [hz, map_smul, hz, smul_smul, ← pow_two, hs, one_smul]
      exact (diagonal_action c hc).2.2.symm
  rw [heq]
  exact toOrthogonal_mem_elementary _

private theorem fixing_first_transport {V : Type u} [AddCommGroup V] [Module F V]
    (Q : QuadraticForm F V) (e f v : V) (he : Q e=0) (hf : Q f=0)
    (hv : Q v=0) (hef : Q.polarBilin e f=1) (hev : Q.polarBilin e v=1) :
    ∃ k : quadraticIsometrySubgroup Q, k ∈ elementarySubgroup Q ∧ k.val e=e ∧ k.val f=v := by
  let s := split Q e f he hf hef
  let w := (s v).2
  have hw := (mem_complement Q e f w.val).mp w.prop
  have hew : Q.polarBilin e w.val=0 := (polar_swap Q e w.val).trans hw.1
  have hfw : Q.polarBilin f w.val=0 := (polar_swap Q f w.val).trans hw.2
  have hve : Q.polarBilin v e=1 := (polar_swap Q v e).trans hev
  have hfe : Q.polarBilin f e=1 := (polar_swap Q f e).trans hef
  have ha : Q.polarBilin v f = -Q w.val := by
    have h := form_split Q e f he hf hef v
    change Q v=Q.polarBilin v f * Q.polarBilin v e+Q w.val at h
    rw [hv,hve,mul_one] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  have hn : Q.polarBilin e (-w.val)=0 := by rw [map_neg,hew,neg_zero]
  refine ⟨siegelElement Q e (-w.val) he hn, siegelElement_mem Q e (-w.val) he hn,
    siegel_fix Q e (-w.val) he hn,?_⟩
  have hd := s.symm_apply_apply v
  change Q.polarBilin v f • e+Q.polarBilin v e • f+w.val=v at hd
  rw [ha,hve,one_smul] at hd
  change siegel Q e (-w.val) f=v
  rw [← hd]
  simp only [siegel,map_neg,hfw,hfe,Q.map_neg,neg_zero,zero_smul,one_smul,mul_one]
  module


/-- The full rank-one isometry quotient has exponent two, even at the ternary endpoint. -/
theorem quotient_square (x : ElementaryQuotient (formB 1 F)) : x ^ 2 = 1 := by
  let Q := formB 1 F
  let π := elementaryProjection Q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (elementarySubgroup Q) x
  have hene : (eVec : VectorB 1 F) ≠ 0 := by
    intro h
    have hh := congrArg (fun v : VectorB 1 F => v.1 (.inl 0)) h
    simp [e] at hh
  have hge : g.val eVec ≠ 0 := fun h => hene (g.val.injective (h.trans (map_zero g.val).symm))
  have hqe : Q eVec = 0 := by simp [Q, eVec, e]
  have hqf : Q fVec = 0 := by simp [Q, fVec, f]
  have hpair : Q.polarBilin eVec fVec = 1 := by
    change (formB 1 F).polarBilin eVec fVec = 1
    rw [polar_f]
    simp [e]
  obtain ⟨a, c, hc, ha⟩ := singular_line_orbit (g.val eVec) hge
    ((isometry_preserves Q g eVec).trans hqe)
  let A := toOrthogonal a
  let k := A⁻¹ * g
  have hke : k.val eVec = c • eVec := by
    change A.val.symm (g.val eVec) = c • eVec
    rw [ha, map_smul, LinearEquiv.symm_apply_apply]
  have hkv : Q (c • k.val fVec) = 0 := by
    rw [Q.map_smul, isometry_preserves Q k, hqf, smul_zero]
  have hpev : Q.polarBilin eVec (c • k.val fVec) = 1 := by
    have h := isometry_polar Q (isometryCarrierEquiv Q k) eVec fVec
    change Q.polarBilin (k.val eVec) (k.val fVec) = _ at h
    rw [hke, map_smul, LinearMap.smul_apply, hpair] at h
    simpa only [map_smul] using h
  obtain ⟨r, hr, hre, hrf⟩ := fixing_first_transport Q eVec fVec (c • k.val fVec)
    hqe hqf hkv hpair hpev
  let t := r⁻¹ * k
  have hte : t.val eVec = c • eVec := by
    change r.val.symm (k.val eVec) = _
    rw [hke, map_smul, ← hre, LinearEquiv.symm_apply_apply, hre]
  have htf : t.val fVec = c⁻¹ • fVec := by
    change r.val.symm (k.val fVec) = _
    apply r.val.injective
    rw [LinearEquiv.apply_symm_apply, map_smul, hrf, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have ht := pair_scaling_square_mem t c hc hte htf
  have hA : π A = 1 := (QuotientGroup.eq_one_iff A).mpr (toOrthogonal_mem_elementary a)
  have hrπ : π r = 1 := (QuotientGroup.eq_one_iff r).mpr hr
  have hπ : π g = π t := by
    change π g = π (r⁻¹ * (A⁻¹ * g))
    rw [map_mul, map_mul, map_inv, map_inv, hA, hrπ, inv_one, one_mul, one_mul]
  change π g ^ 2 = 1
  rw [hπ, ← map_pow]
  exact (QuotientGroup.eq_one_iff (t^2)).mpr ht

/-- Rank-one elementary index is prime to every odd prime. -/
theorem index_coprime [Finite F] (p : ℕ) (hp : Odd p) :
    Nat.Coprime p (elementarySubgroup (formB 1 F)).index := by
  have : Finite (quadraticIsometrySubgroup (formB 1 F)) :=
    Finite.of_injective
      (fun g : quadraticIsometrySubgroup (formB 1 F) => (g.val : VectorB 1 F → VectorB 1 F))
      (fun _ _ h => Subtype.ext (LinearEquiv.ext (congrFun h)))
  have htwo : IsPGroup 2 (ElementaryQuotient (formB 1 F)) :=
    isPGroup_iff_pow_pow_eq_one.mpr (fun x => ⟨1, by simpa using quotient_square x⟩)
  obtain ⟨n, hn⟩ := htwo.exists_card_dvd_pow
  exact (hp.coprime_two_right.pow_right n).coprime_dvd_right hn

end ClassicalOrthogonal.Fundamental.SplitOddBlocks.IsometryQuotients.RankOne
