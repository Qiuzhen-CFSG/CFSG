module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.Boundary
public import Theory.Character.SimpleFaithfulCharacter
public import Theory.Character.CharacterKernel

/-!
# Restriction positivity and faithful involution traces

The trivial constituent in restriction to the actual elementary group E16
has nonnegative multiplicity. Since its fifteen nonidentity elements fuse,
this gives degree + 15 times the involution value ≥ 0. Simplicity makes every
nonprincipal irreducible faithful, so its value at the distinguished involution
is strictly less than its degree. These inequalities exclude spurious small
rows left by divisibility alone.

Source: ordinary restriction and character kernels, applied to Janko (1968),
Sections 6--7.
-/

open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite
namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21.SmallDegrees
open LocalModelDichotomy CharacterOrder
variable {G : Type*} [Group G] [Finite G]

/-- The E16 fixed-space multiplicity is nonnegative, not merely integral. -/
public theorem E_fixed_nonnegative (D : LocalData G) (k : TwistedModel ≃* D.centralizer)
    (L : LocalAnalysisData D k) {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ)
    (t : ℤ) (ht : χ D.z = (t : ℂ)) : 0 ≤ (hχ.degree : ℤ) + 15 * t := by
  classical
  let E := CaseII.E D k
  let : Fintype E := Fintype.ofFinite E
  let : IsElementaryAbelian 2 E := L.E_elementary
  have hc : IsCharacter χ := by
    obtain ⟨n, ρ, _, rfl⟩ := hχ
    exact ⟨n, ρ, rfl⟩
  have hf : IsClassFunction χ := by
    obtain ⟨n, ρ, _, rfl⟩ := hχ
    exact ρ.char_conj
  have he (a : E) : χ (a : G) = if a = 1 then χ 1 else χ D.z := by
    split_ifs with ha
    · simp [ha]
    · have hao : orderOf (a : G) = 2 := by
        apply orderOf_eq_prime
        · exact elemPow_eq_one_of_isElementaryAbelian (a : G) a.property
        · intro heq
          exact ha (Subtype.ext heq)
      obtain ⟨g, hg⟩ := isConj_iff.mp (L.involution_fusion a hao)
      rw [← hg]
      exact (hf a g).symm
  have hs : (∑ a : E, χ (a : G)) = ((hχ.degree : ℤ) + 15 * t : ℤ) := by
    simp_rw [he]
    simp [Finset.sum_ite, Finset.filter_ne', Finset.filter_eq', ← Nat.card_eq_fintype_card,
      show Nat.card E = 16 from L.E_card, hχ.degree_eq, ht]
  obtain ⟨m, hm⟩ := (isCharacter_comp_hom E.subtype hc).scalarProduct_nat isCharacter_one
  have hm' : ((hχ.degree : ℤ) + 15 * t : ℂ) = 16 * m := by
    simp only [scalarProduct, Pi.one_apply, star_one, mul_one] at hm
    change (Nat.card E : ℂ)⁻¹ * (∑ a : E, χ (a : G)) = (m : ℂ) at hm
    rw [hs, show Nat.card E = 16 from L.E_card] at hm
    push_cast at hm
    linear_combination 16 * hm
  have hm'' : (hχ.degree : ℤ) + 15 * t = 16 * m := by exact_mod_cast hm'
  omega

/-- At the nonidentity involution, faithfulness makes the trace strictly
smaller than the degree. -/
public theorem involution_lt_degree [IsSimpleGroup G] (D : LocalData G)
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ) (hnp : χ ≠ 1)
    (t : ℤ) (ht : χ D.z = (t : ℂ)) : t < (hχ.degree : ℤ) := by
  obtain ⟨m, ρ, hρ, hr, hinj⟩ := hχ.exists_faithful_of_ne_one hnp
  have hd : hχ.degree = m := by
    have hh := (congrFun hr 1).symm.trans hχ.degree_eq
    simpa using hh.symm
  have hnorm := finite_order_end_norm_trace_le_finrank (ρ D.z)
    (orderOf_pos D.z).ne' (by rw [← map_pow, pow_orderOf_eq_one, map_one])
  have ht' : LinearMap.trace ℂ (Fin m → ℂ) (ρ D.z) = (t : ℂ) := by
    simpa only [hr, Representation.character] using ht
  have hle : t ≤ (hχ.degree : ℤ) := by
    rw [ht'] at hnorm
    have hh : (t : ℝ) ≤ m := (Complex.re_le_norm (t : ℂ)).trans (by simpa using hnorm)
    rw [hd]
    exact_mod_cast hh
  apply lt_of_le_of_ne hle
  intro heq
  have hz : D.z ∈ ρ.ker := (ρ.mem_ker_iff_character_eq_degree D.z).mpr (by
    rw [← hr, ht, heq, hχ.degree_eq]
    simp)
  have hz1 : D.z = 1 := hinj ((MonoidHom.mem_ker.mp hz).trans ρ.map_one.symm)
  have ho := D.z_order
  simp [hz1] at ho

end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21.SmallDegrees
