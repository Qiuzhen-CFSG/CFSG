module

public import Theory.Representation.BinaryPermutation.FiveSylowQuadratic

/-!
# Quadratic two-subgroups on the five-point core

A Sylow four-group in A₅ acts nonquadratically on the binary permutation
core: the two standard double transpositions have nonzero second displacement
on e₀+e₄. Sylow conjugacy and Lagrange's theorem then bound every quadratic
two-subgroup by order two. An injective equivariant summand transfers this
obstruction to the actual actor image.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 12.6.23, printed p.830, the deduction k=1.
-/

public section

open Subgroup
open scoped Pointwise
namespace BinaryPermutation.FiveQuadraticActors
open Representation.BinaryOffender

private theorem quadratic_map_conj {H W : Type*} [Group H]
    [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) H W} {A : Subgroup H}
    (hA : IsQuadratic ρ A) (g : H) :
    IsQuadratic ρ (A.map (MulAut.conj g).toMonoidHom) := by
  have hinv (v : W) : ρ g⁻¹ (ρ g v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ v
  change ρ (g * a * g⁻¹) (ρ (g * b * g⁻¹) v - v) = ρ (g * b * g⁻¹) v - v
  have h := congrArg (ρ g) (hA a ha b hb (ρ g⁻¹ v))
  have hginv (v : W) : ρ g (ρ g⁻¹ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  simpa only [map_mul, Module.End.mul_apply, map_sub, hinv, hginv] using h

private def testVector : core (Fin 5) :=
  ⟨![1,0,0,0,1], by rw [mem_core]; decide⟩

private theorem klein_not_quadratic :
    ¬ IsQuadratic (alternatingCoreRepresentation (Fin 5)) CubicFixedSpace.Five.klein := by
  intro h
  have he := congrArg (fun x : core (Fin 5) => x.val 0)
    (h _ CubicFixedSpace.Five.first_mem _ CubicFixedSpace.Five.second_mem testVector)
  exact (by decide :
    (alternatingCoreRepresentation (Fin 5) CubicFixedSpace.Five.first
      (alternatingCoreRepresentation (Fin 5) CubicFixedSpace.Five.second testVector -
        testVector)).val 0 ≠
    (alternatingCoreRepresentation (Fin 5) CubicFixedSpace.Five.second testVector -
      testVector).val 0) he

theorem sylow_not_quadratic (P : Sylow 2 (alternatingGroup (Fin 5))) :
    ¬ IsQuadratic (alternatingCoreRepresentation (Fin 5)) (P : Subgroup _) := by
  obtain ⟨Q, hQ⟩ := CubicFixedSpace.Five.klein_isPGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 5)) P Q
  have hp : (P : Subgroup (alternatingGroup (Fin 5))).map
      (MulAut.conj g).toMonoidHom = Q := by
    have h := congrArg (fun S : Sylow 2 (alternatingGroup (Fin 5)) =>
      (S : Subgroup (alternatingGroup (Fin 5)))) hg
    rwa [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
  intro h
  have h' := quadratic_map_conj h g
  rw [hp] at h'
  exact klein_not_quadratic (fun a ha b hb v => h' a (hQ ha) b (hQ hb) v)

theorem card_le_two_of_quadratic (A : Subgroup (alternatingGroup (Fin 5)))
    (hp : IsPGroup 2 A)
    (hq : IsQuadratic (alternatingCoreRepresentation (Fin 5)) A) : Nat.card A ≤ 2 := by
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  have hc := Theory.PSL2.SylowFixedQuotients.alternating_sylow_card P
  have hd : Nat.card A ∣ 4 := by
    rw [← hc]
    exact card_dvd_of_le hP
  have hcases : Nat.card A = 1 ∨ Nat.card A = 2 ∨ Nat.card A = 4 := by
    obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show Nat.card A ∣ 2 ^ 2 from hd)
    interval_cases k <;> simp_all
  rcases hcases with h | h | h
  · omega
  · omega
  · have he := Subgroup.eq_of_le_of_card_ge hP (by omega)
    rw [he] at hq
    exact (sylow_not_quadratic P hq).elim

theorem card_le_four (A : Subgroup (alternatingGroup (Fin 5))) (hp : IsPGroup 2 A) :
    Nat.card A ≤ 4 := by
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  have hc := Theory.PSL2.SylowFixedQuotients.alternating_sylow_card P
  exact (Nat.card_le_card_of_injective (inclusion hP) (inclusion_injective hP)).trans_eq hc

/-- An embedded permutation summand detects the quadratic action of the same actor. -/
theorem image_quadratic_of_embedding {H W : Type*} [Group H]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W) (α : H →* alternatingGroup (Fin 5))
    (j : core (Fin 5) →ₗ[ZMod 2] W) (hj : Function.Injective j)
    (he : ∀ h v, j (alternatingCoreRepresentation (Fin 5) (α h) v) = ρ h (j v))
    (hq : IsQuadratic ρ ⊤) :
    IsQuadratic (alternatingCoreRepresentation (Fin 5)) α.range := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ v
  apply hj
  rw [he, map_sub, he]
  exact hq a (mem_top _) b (mem_top _) (j v)

end BinaryPermutation.FiveQuadraticActors
