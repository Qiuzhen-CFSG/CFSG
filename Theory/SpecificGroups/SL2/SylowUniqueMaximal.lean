module

public import Theory.SpecificGroups.SL2.BorelSmallInvariant.Basic
public import Theory.Order.UniqueMaximalOver

/-!
# Unique maximal overgroups of defining-characteristic Sylow subgroups of SL₂

An overgroup of the upper root group that contains a matrix outside the Borel
is the full group. Multiply that matrix by an upper transvection to zero its
upper-left entry; conjugation then supplies every lower transvection. The two
root groups generate SL₂. Sylow conjugacy transports this calculation to any
Sylow subgroup in the defining characteristic.

The matrix argument works over every field and includes SL₂(2). Source
application: Aschbacher–Smith, combined manuscript (1 March 2004), the group-list
calculation in E.6.14, printed p.251. No subgroup classification is used.
-/

open Matrix Subgroup
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F]
local notation "u" => SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one
local notation "v" => SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) one_ne_zero
open SpecialLinearGroup

private theorem zero_conj_upper {g : SL(2, F)} (hg : g.val 0 0 = 0) (t : F) :
    g * u t * g⁻¹ = v (-g.val 1 0 ^ 2 * t) := by
  have hd : -(g.val 0 1 * g.val 1 0) = 1 := by
    simpa only [det_fin_two, hg, zero_mul, zero_sub] using g.property
  have key : g * u t = v (-g.val 1 0 ^ 2 * t) * g := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [mul_apply, Fin.sum_univ_two, transvection_coe, hg]
    linear_combination -g.val 1 0 * t * hd
  rw [key, mul_assoc, mul_inv_cancel, mul_one]

/-- Every proper subgroup containing the full upper root group lies in its Borel. -/
public theorem overgroup_le_rankOneBorel {K : Subgroup (SL(2, F))}
    (hU : upperUnipotent F ≤ K) (hK : K ≠ ⊤) : K ≤ rankOneBorel F := by
  intro g hgK
  apply (mem_rankOneBorel_iff g).mpr
  by_contra hc
  have hu (t : F) : u t ∈ K := hU ((mem_upperUnipotent F _).mpr ⟨t, rfl⟩)
  let w : SL(2, F) := u (-g.val 0 0 / g.val 1 0) * g
  have hwK : w ∈ K := K.mul_mem (hu _) hgK
  have hw00 : w.val 0 0 = 0 := by
    dsimp [w]
    simp [mul_apply, Fin.sum_univ_two, transvection_coe, hc]
  have hw10 : w.val 1 0 = g.val 1 0 := by
    simp [w, mul_apply, Fin.sum_univ_two, transvection_coe]
  have hv (t : F) : v t ∈ K := by
    have hh := K.mul_mem (K.mul_mem hwK (hu (-t / g.val 1 0 ^ 2))) (K.inv_mem hwK)
    rw [zero_conj_upper hw00, hw10] at hh
    have he : -g.val 1 0 ^ 2 * (-t / g.val 1 0 ^ 2) = t := by field_simp
    rwa [he] at hh
  apply hK
  apply top_unique
  intro A _
  apply Matrix.SL2.transvection_induction (fun A => A ∈ K) ?_ ?_ A
  · intro i j hij t
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hu t
    · exact hv t
    · exact (hij rfl).elim
  · exact fun _ _ => K.mul_mem

/-- The Borel is the unique maximal subgroup above the full upper root group. -/
public theorem upperUnipotent_hasUniqueMaximalOver :
    Order.HasUniqueMaximalOver (upperUnipotent F) ⊤ := by
  have hB : rankOneBorel F ≠ ⊤ := by
    intro he
    have hh : v (1 : F) ∈ rankOneBorel F := he ▸ mem_top _
    have hz := (mem_rankOneBorel_iff _).mp hh
    simp [transvection_coe] at hz
  have hUB : upperUnipotent F ≤ rankOneBorel F := Subgroup.le_normalizer
  have hc : rankOneBorel F ⋖ ⊤ := by
    apply IsCoatom.covBy_top
    apply isCoatom_iff_ge_of_le.mpr
    refine ⟨hB, ?_⟩
    intro K hK hBK
    exact overgroup_le_rankOneBorel (hUB.trans hBK) hK
  refine ⟨lt_of_le_of_lt hUB (lt_top_iff_ne_top.mpr hB), rankOneBorel F, ⟨hUB, hc⟩, ?_⟩
  intro K hK
  exact ((hK.2.eq_or_eq (overgroup_le_rankOneBorel hK.1 hK.2.ne) le_top).resolve_right hB).symm

/-- Every defining-characteristic Sylow subgroup has a unique maximal overgroup. -/
public theorem sylow_hasUniqueMaximalOver [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (S : Sylow p (SL(2, F))) : Order.HasUniqueMaximalOver (S : Subgroup (SL(2, F))) ⊤ := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SL(2, F)) (upperUnipotentSylow F p) S
  have h := (upperUnipotent_hasUniqueMaximalOver (F := F)).map (MulAut.conj g).mapSubgroup
  rw [OrderIso.map_top] at h
  change Order.HasUniqueMaximalOver
    ((g • upperUnipotentSylow F p : Sylow p (SL(2, F))) : Subgroup (SL(2, F))) ⊤ at h
  rwa [hg] at h

end Matrix.SpecialLinearGroup
