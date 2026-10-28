module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ClassDistributions.NormalizerFusion.Actors
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ElementCentralizers

/-!
# The remaining order-four fusions from the elementary normalizer

An actual normalizer conjugator carrying `a` to `d` transports `Ea` to `Ed`.
In `Ea`, the order-four elements with square `z 0` form the local class of
`z 3 * a`; the other order-four elements form that of `z 1 * a`.
The conjugator carries `z 0` to either `z 2` or `z 0 * z 2`, but cannot
fix it, since `a` and `d` are not conjugate in the marked centralizer.
Comparing the three nontrivial squares in `Ed` proves the requested fusion
and separates the other two elements by their distinct ambient classes.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 5, pp.9–10. This uses the actual action on `E`
and avoids the full conjugacy-class table of its normalizer.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification
open LocalModelDichotomy
namespace CaseII.Distribution

local instance : DecidableEq TwistedModel := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) SemidirectProduct.ext_iff.symm
local instance : Fintype TwistedModel := Fintype.ofEquiv
  (BinaryFour × SymmetricFour) SemidirectProduct.equivProd.symm

private def cosetConjugator (v : BinaryFour) (i : Fin 2) : TwistedModel :=
  SemidirectProduct.inl v * b ^ i.val

private theorem Ea_four_classes (x : TwistedModel) (hx : x.right = a.right)
    (hx2 : x ^ 2 ≠ 1) :
    (x ^ 2 = z 0 → IsConj x (z 3 * a)) ∧
      (x ^ 2 ≠ z 0 → IsConj x (z 1 * a)) := by
  have h : ∀ x : TwistedModel, x.right = a.right → x ^ 2 ≠ 1 →
      ∃ v : BinaryFour, ∃ i : Fin 2,
        (x ^ 2 = z 0 → cosetConjugator v i * x * (cosetConjugator v i)⁻¹ = z 3 * a) ∧
        (x ^ 2 ≠ z 0 → cosetConjugator v i * x * (cosetConjugator v i)⁻¹ = z 1 * a) := by
    decide +kernel
  obtain ⟨v, i, h0, h1⟩ := h x hx hx2
  exact ⟨fun hx0 => isConj_iff.mpr ⟨_, h0 hx0⟩,
    fun hx0 => isConj_iff.mpr ⟨_, h1 hx0⟩⟩

universe u
variable {G : Type u} [Group G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

private theorem transport_Ed_to_Ea (n : G)
    (hn : n ∈ normalizer (E D k : Set G))
    (ha : (MulAut.conj n) (into D k a) = into D k d)
    (x : TwistedModel) (hx : x.right = d.right) :
    ∃ y : TwistedModel, y.right = a.right ∧
      (MulAut.conj n) (into D k y) = into D k x := by
  have hv : x * d⁻¹ ∈ modelE := by
    change x.right * d.right⁻¹ = 1
    rw [hx, mul_inv_cancel]
  have hvE : into D k (x * d⁻¹) ∈ E D k := by
    rw [← modelE_map D k]
    exact mem_map_of_mem _ hv
  have hwE : n⁻¹ * into D k (x * d⁻¹) * n ∈ E D k :=
    (mem_normalizer_iff''.mp hn _).mp hvE
  rw [← modelE_map D k] at hwE
  obtain ⟨v, hv, he⟩ := hwE
  refine ⟨v * a, ?_, ?_⟩
  · change v.right * a.right = a.right
    change v.right = 1 at hv
    rw [hv, one_mul]
  · have he' : (MulAut.conj n) (into D k v) = into D k (x * d⁻¹) := by
      simp only [MulAut.conj_apply, he, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
    rw [map_mul, map_mul, he', ha, ← map_mul]
    simp only [inv_mul_cancel_right]

variable [Finite G]

private theorem actor_conjugator_moves_z (n : G)
    (hn : n ∈ normalizer (E D k : Set G))
    (ha : (MulAut.conj n) (into D k a) = into D k d) :
    (MulAut.conj n) (into D k (z 0)) = into D k (z 2) ∨
      (MulAut.conj n) (into D k (z 0)) = into D k (z 0 * z 2) := by
  let e := MulAut.conj n
  have hnotfix : e (into D k (z 0)) ≠ into D k (z 0) := by
    intro h
    have hnC : n ∈ D.centralizer := by
      apply mem_centralizer_singleton_iff.mpr
      rw [← into_z_zero D k]
      calc
        _ = (n * into D k (z 0) * n⁻¹) * n := by group
        _ = into D k (z 0) * n := congrArg (· * n) h
    obtain ⟨v, hv⟩ := k.surjective ⟨n, hnC⟩
    have hvn : into D k v = n := congrArg Subtype.val hv
    have hvad : v * a * v⁻¹ = d := by
      apply into_injective D k
      simpa only [map_mul, map_inv, hvn, MulAut.conj_apply] using ha
    have hh : ∀ v : TwistedModel, v * a * v⁻¹ ≠ d := by decide +kernel
    exact hh v hvad
  have hzE : into D k (z 0) ∈ E D k := by
    rw [← modelE_map D k]
    exact mem_map_of_mem _ (z_mem_modelE 0)
  have hwE : e (into D k (z 0)) ∈ E D k :=
    (mem_normalizer_iff.mp hn _).mp hzE
  rw [← modelE_map D k] at hwE
  obtain ⟨v, hv, he⟩ := hwE
  have hcomm : v * d = d * v := by
    apply into_injective D k
    have hc := ((z_zero_mem_center.comm a).map (into D k)).map e.toMonoidHom
    have hea : e (into D k a) = into D k d := ha
    simpa only [map_mul, he, MulEquiv.coe_toMonoidHom, hea] using hc.eq
  have hfixed : ∀ v : TwistedModel, v.right = 1 → v * d = d * v →
      v = 1 ∨ v = z 0 ∨ v = z 2 ∨ v = z 0 * z 2 := by decide +kernel
  rcases hfixed v hv hcomm with h | h | h | h
  · have hz : into D k (z 0) = 1 := e.injective (he.symm.trans (by rw [h, map_one]) |>.trans e.map_one.symm)
    have hm : z 0 = 1 := into_injective D k (hz.trans (map_one _).symm)
    have hne : z 0 ≠ 1 := by decide +kernel
    exact (hne hm).elim
  · exact (hnotfix (he.symm.trans (by rw [h]))).elim
  · exact Or.inl (he.symm.trans (by rw [h]))
  · exact Or.inr (he.symm.trans (by rw [h]))

omit [Finite G] in
private theorem Ed_four_classes (n : G)
    (hn : n ∈ normalizer (E D k : Set G))
    (ha : (MulAut.conj n) (into D k a) = into D k d)
    (x : TwistedModel) (hx : x.right = d.right) (hx2 : x ^ 2 ≠ 1) :
    ((into D k x) ^ 2 = (MulAut.conj n) (into D k (z 0)) →
      IsConj (into D k x) (into D k (z 3 * a))) ∧
    ((into D k x) ^ 2 ≠ (MulAut.conj n) (into D k (z 0)) →
      IsConj (into D k x) (into D k (z 1 * a))) := by
  obtain ⟨y, hy, he⟩ := transport_Ed_to_Ea D k n hn ha x hx
  have hy2 : y ^ 2 ≠ 1 := by
    intro h
    apply hx2
    apply into_injective D k
    rw [map_pow, ← he, ← map_pow, ← map_pow, h, map_one, map_one]
  have hsq : (into D k x) ^ 2 = (MulAut.conj n) (into D k (z 0)) ↔ y ^ 2 = z 0 := by
    rw [← he, ← map_pow, ← map_pow]
    exact (MulAut.conj n).injective.eq_iff.trans (into_injective D k).eq_iff
  have hxy : IsConj (into D k x) (into D k y) :=
    (isConj_iff.mpr ⟨n, he⟩).symm
  exact ⟨fun h => hxy.trans ((into D k).map_isConj ((Ea_four_classes y hy hy2).1 (hsq.mp h))),
    fun h => hxy.trans ((into D k).map_isConj ((Ea_four_classes y hy hy2).2 (fun h' => h (hsq.mpr h'))))⟩

/-- A normalizer conjugator of `a` and `d` determines the remaining ambient
order-four fusion and nonfusion by its action on their squares. -/
public theorem remaining_four_fusion_of_actor_conjugator
    (n : G) (hn : n ∈ normalizer (E D k : Set G))
    (ha : (MulAut.conj n) (into D k a) = into D k d) :
    IsConj (into D k (z 1 * a)) (into D k (z 1 * d)) ∧
      ¬ IsConj (into D k (z 3 * d)) (into D k (z 1 * z 3 * d)) := by
  have hp : (z 1 * d) ^ 2 = z 0 ∧ (z 3 * d) ^ 2 = z 2 ∧
      (z 1 * z 3 * d) ^ 2 = z 0 * z 2 := by decide +kernel
  have h0 := Ed_four_classes D k n hn ha (z 1 * d) (by decide +kernel) (by decide +kernel)
  have h1 := Ed_four_classes D k n hn ha (z 3 * d) (by decide +kernel) (by decide +kernel)
  have h2 := Ed_four_classes D k n hn ha (z 1 * z 3 * d) (by decide +kernel) (by decide +kernel)
  have hn01 : into D k (z 0) ≠ into D k (z 2) := by
    intro h
    have hh : z 0 ≠ z 2 := by decide +kernel
    exact hh (into_injective D k h)
  have hn02 : into D k (z 0) ≠ into D k (z 0 * z 2) := by
    intro h
    have hh : z 0 ≠ z 0 * z 2 := by decide +kernel
    exact hh (into_injective D k h)
  have hn12 : into D k (z 2) ≠ into D k (z 0 * z 2) := by
    intro h
    have hh : z 2 ≠ z 0 * z 2 := by decide +kernel
    exact hh (into_injective D k h)
  rcases actor_conjugator_moves_z D k n hn ha with hz | hz
  · rw [← map_pow, hp.1, hz] at h0
    rw [← map_pow, hp.2.1, hz] at h1
    rw [← map_pow, hp.2.2, hz] at h2
    have hf := (h0.2 hn01).symm
    refine ⟨hf, ?_⟩
    intro h
    exact four_not_fused D k (((h1.1 rfl).symm.trans h).trans ((h2.2 hn12.symm).trans hf))
  · rw [← map_pow, hp.1, hz] at h0
    rw [← map_pow, hp.2.1, hz] at h1
    rw [← map_pow, hp.2.2, hz] at h2
    have hf := (h0.2 hn02).symm
    refine ⟨hf, ?_⟩
    intro h
    exact four_not_fused D k (((h2.1 rfl).symm.trans h.symm).trans ((h1.2 hn12).trans hf))

/-- Janko's remaining order-four fusions, obtained from the genuine
involution-normalizer data with no order-three fusion premise. -/
public theorem remaining_four_fusion_of_involution_normalizers [IsSimpleGroup G]
    (h2 : InvolutionNormalizerData D k) :
    IsConj (into D k (z 1 * a)) (into D k (z 1 * d)) ∧
      ¬ IsConj (into D k (z 3 * d)) (into D k (z 1 * z 3 * d)) := by
  obtain ⟨n, hn, ha⟩ := normalizer_a_d_conjugate D k h2.normalizer_E
  exact remaining_four_fusion_of_actor_conjugator D k n hn ha

end CaseII.Distribution
end Theory.GroupTheory.HeldM22A10.M22Identification
