module

public import Stellmacher.Recognition.FongWreathedInducedCharacters
public import Stellmacher.Recognition.FongWreathedRationalConstituents
public import Stellmacher.Recognition.FongWreathedFusionLocal

/-!
# Fong's actual rational exceptional-character packet

The first induced function has values zero and four, so its norm four gives
principal coefficient one. Its support contains no element conjugate to its
inverse: an inverting conjugator must normalize the recovered cyclic group
of order eight, where the linear character alpha gives a contradiction.
Products of two involutions therefore miss that support. This proves the
involution-pair vanishing required by the rational-constituent theorem.

Thus the rational four-character packet, with actual irreducible functions
and equations (8),(9), exists for every height-two wreathed Sylow presentation
in a finite simple group. Block membership and contribution bounds are
subsequent steps, not replacement hypotheses in this construction.

Source: P. Fong, Some Sylow subgroups of order 32 and a characterization of
U(3,3), J. Algebra 6 (1967), printed p.72, equations (8),(9).
-/

public section
open scoped BigOperators
open Theory.Character
namespace Stellmacher.Recognition.FongWreathedInduction
noncomputable section
attribute [local instance] Fintype.ofFinite
variable {G : Type*} [Group G] [Finite G]

/-- The {0,4}-valued first function has principal coefficient one. -/
theorem actualInducedOne_principal (S : Sylow 2 G)
    (P : ABG.Wreathed.Presentation S 2) :
    scalarProduct G (actualInducedOne S P) 1 = 1 := by
  have hn := (actual_induced_gram_data S P).2.2.1
  have hm (g : G) : actualInducedOne S P g * star (actualInducedOne S P g) =
      4 * actualInducedOne S P g := by
    rcases (actualInducingData S P).inducedOne_eq_four_or_zero
      (actualInducingData_hasSpecialSupport S P) g with h | h
    · change actualInducedOne S P g = 4 at h
      rw [h]; norm_num
    · change actualInducedOne S P g = 0 at h
      rw [h]; norm_num
  simp only [scalarProduct, hm, ← Finset.mul_sum] at hn
  simp only [scalarProduct, Pi.one_apply, star_one, mul_one]
  linear_combination hn / 4

namespace InducingData
omit [Finite G] in
/-- The actual special support contains no real element. -/
theorem support_not_isConj_inv (d : InducingData G) (S : Sylow 2 G)
    (P : ABG.Wreathed.Presentation S 2) (hd : d.IsActual S P)
    (h : d.H) (hh : h ∈ d.support) : ¬ IsConj (h : G) (h : G)⁻¹ := by
  intro hc
  obtain ⟨g, hg⟩ := isConj_iff.mp hc
  have hp : g * ((h : G) ^ Nat.card d.U) * g⁻¹ =
      ((h : G) ^ Nat.card d.U)⁻¹ := by
    have he := map_pow (MulAut.conj g) (h : G) (Nat.card d.U)
    change g * (h : G) ^ Nat.card d.U * g⁻¹ =
      (g * (h : G) * g⁻¹) ^ Nat.card d.U at he
    simpa only [hg, inv_pow] using he
  have hgH : g ∈ d.H := by
    rw [hd.1, ← hd.2.1, Subgroup.mem_normalizer_iff_map_conj_eq,
      ← d.support_power_generates_ambient h hh, MonoidHom.map_zpowers]
    change Subgroup.zpowers (g * (h : G) ^ Nat.card d.U * g⁻¹) = _
    rw [hp, Subgroup.zpowers_inv]
  have he : d.alpha h = d.alpha h⁻¹ := by
    have heq : (⟨g, hgH⟩ : d.H) * h * (⟨g, hgH⟩ : d.H)⁻¹ = h⁻¹ :=
      Subtype.ext hg
    calc
      d.alpha h = d.alpha h * d.alpha ((⟨g, hgH⟩ : d.H) * (⟨g, hgH⟩ : d.H)⁻¹) := by simp
      _ = d.alpha ((⟨g, hgH⟩ : d.H) * h * (⟨g, hgH⟩ : d.H)⁻¹) := by
        simp only [map_mul]
        ring
      _ = d.alpha h⁻¹ := congrArg d.alpha heq
  have hs : d.alpha h * d.alpha h = 1 := by
    calc
      d.alpha h * d.alpha h = d.alpha h * d.alpha h⁻¹ := congrArg (d.alpha h * ·) he
      _ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  obtain ⟨i, hi, u, rfl⟩ := hh
  simp only [map_mul, map_pow, d.alpha_f, d.alpha_U, mul_one] at hs
  have hi2 : (Complex.I ^ i.val) ^ 2 = -1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, Complex.I_sq, hi.neg_one_pow]
  rw [← pow_two, hi2] at hs
  norm_num at hs
end InducingData

/-- Products of involutions miss the support, so their pairing vanishes. -/
theorem actualInducedOne_involutionPair (S : Sylow 2 G)
    (P : ABG.Wreathed.Presentation S 2) :
    scalarProduct G (actualInducedOne S P)
      (fun g => (involutionPairCount g : ℂ)) = 0 := by
  rw [scalarProduct_involutionPairCount_eq_sum]
  have hz (a b : G) (ha : orderOf a = 2) (hb : orderOf b = 2) :
      actualInducedOne S P (a * b) = 0 := by
    apply (actualInducingData S P).inducedOne_supported
    rintro ⟨h, hh, hc⟩
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left (by
      simpa only [ha, pow_two] using pow_orderOf_eq_one a)
    have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_left (by
      simpa only [hb, pow_two] using pow_orderOf_eq_one b)
    have hab : IsConj (a * b) (a * b)⁻¹ := isConj_iff.mpr ⟨a, by
      rw [mul_inv_rev, hai, hbi]
      have haa : a * a = 1 := by
        simpa only [ha, pow_two] using pow_orderOf_eq_one a
      simp only [← mul_assoc, haa, one_mul]⟩
    have hinv : IsConj ((a * b)⁻¹) (h : G)⁻¹ := by
      obtain ⟨g, hg⟩ := isConj_iff.mp hc.symm
      exact isConj_iff.mpr ⟨g, by
        simpa only [mul_inv_rev, inv_inv, mul_assoc] using congrArg Inv.inv hg⟩
    exact (actualInducingData S P).support_not_isConj_inv S P
      (actualInducingData_isActual S P) h hh (hc.trans (hab.trans hinv))
  have hs : (∑ p : {a : G // orderOf a = 2} × {a : G // orderOf a = 2},
      actualInducedOne S P (p.1 * p.2)) = 0 :=
    Finset.sum_eq_zero fun p _ => hz _ _ p.1.property p.2.property
  rw [hs, mul_zero]

/-- Actual rational irreducibles with the signed decomposition and (8),(9). -/
theorem actual_rational_constituents [IsSimpleGroup G] (S : Sylow 2 G)
    (P : ABG.Wreathed.Presentation S 2) :
    Nonempty (FongRationalConstituents (actualInducedOne S P)
      ((FongWreathedIntrinsic.J P : S) : G)) := by
  obtain ⟨h₁, _, hn, _, _, hd, _, hJ, _⟩ := actual_induced_gram_data S P
  exact fong_rational_constituents h₁ (actualInducedOne_integerValued S P)
    (FongWreathedIntrinsic.J P : S)
    ((Subgroup.orderOf_coe _).trans (FongWreathedIntrinsic.J_orderOf P))
    (FongWreathedIntrinsic.isConj_involution_J S P)
    (actualInducedOne_principal S P) hn hd hJ (actualInducedOne_involutionPair S P)
end
end Stellmacher.Recognition.FongWreathedInduction
