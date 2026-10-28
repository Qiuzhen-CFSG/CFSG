module

public import Theory.SpecificGroups.PSU3.UniversalCover.Projection
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import BenderSuzuki.External.Huppert.II.theorem_10_12
public import Theory.GroupTheory.PerfectCentralCoverExistence

/-!
# Excluding primes detected by the cyclic unitary torus

Huppert's cyclic torus in PSU₃(q) has index `q³(q³+1)`, including when the
scalar center has order three. An odd prime dividing `q-1` is prime to this
index, so its Sylow subgroups are cyclic. Transfer excludes that prime from
every finite perfect central-cover kernel, in particular the literal universal
kernel. The change-of-form equivalence retains the original field involution.

Source: Huppert, *Endliche Gruppen I*, II.10.12; Aschbacher–Smith I.1.2–I.1.3,
printed p.407 (PDF p.418); GLS3, Theorem 6.1.4. This supplies the `q-1` branch
of the nondefining-characteristic upper bound, not the full multiplier theorem.
-/

public section

open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External PerfectCentralCovering
open HermitianForm.OddPrimeSylow.NormalizedOuter

namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.EvenKernelBound.CyclicTorus

universe u v
variable {F : Type u} [Field F] [Finite F] (J : HermitianForm 3 F)

private theorem exists_standard_torus (q : ℕ)
    (hcard : Nat.card F = q ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = q)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) :
    ∃ H : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J),
      IsCyclic H ∧ H.index = (q ^ 3 + 1) * q ^ 3 := by
  obtain ⟨_, _, _, _, _, _, ht, _, hG, _⟩ := huppert_II_10_12 J q hcard hfixed hJ
  obtain ⟨R, H, _, _, _, _, _, hc, _, _, _, hH, _⟩ := ht
  have hd : Nat.gcd (q + 1) 3 ∣ q ^ 2 - 1 := by
    have he : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      simpa [mul_comm] using Nat.sq_sub_sq q 1
    rw [he]
    exact dvd_mul_of_dvd_right (Nat.gcd_dvd_left (q + 1) 3) _
  have hi := H.card_mul_index
  rw [hG, Nat.gcd_comm 3 (q + 1), Nat.mul_div_assoc _ hd,
    ← hH, mul_comm _ (Nat.card H)] at hi
  exact ⟨H, hc, Nat.eq_of_mul_eq_mul_left Nat.card_pos hi⟩

private theorem not_dvd_torus_index {q p : ℕ} (hq : 1 < q) (hp : p.Prime)
    (hp2 : p ≠ 2) (hd : p ∣ q - 1) : ¬ p ∣ (q ^ 3 + 1) * q ^ 3 := by
  have hm : q % p = 1 := by
    have he := (Nat.modEq_iff_dvd' (show 1 ≤ q by omega)).mpr hd
    exact Eq.trans (show q % p = 1 % p from he.symm) (Nat.mod_eq_of_lt hp.one_lt)
  have hpgt : 2 < p := by have := hp.two_le; omega
  rw [Nat.dvd_iff_mod_eq_zero]
  simp [Nat.mul_mod, Nat.add_mod, Nat.pow_mod, hm, Nat.mod_eq_of_lt hp.one_lt,
    Nat.mod_eq_of_lt hpgt]

private theorem cyclic_sylow_of_index
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (H : Subgroup G) [IsCyclic H] (hi : ¬ p ∣ H.index) (S : Sylow p G) :
    IsCyclic S := by
  let P : Sylow p H := Classical.choice inferInstance
  let R : Subgroup G := (P : Subgroup H).map H.subtype
  have hR : IsPGroup p R := P.isPGroup'.map H.subtype
  have hindex : ¬ p ∣ R.index := by
    rw [show R.index = (P : Subgroup H).index * H.index from index_map_subtype _]
    exact (Fact.out : p.Prime).not_dvd_mul P.not_dvd_index hi
  let T : Sylow p G := hR.toSylow hindex
  let eP : P ≃* R := (P : Subgroup H).equivMapOfInjective H.subtype H.subtype_injective
  exact isCyclic_of_injective ((S.equiv T).trans eP.symm).toMonoidHom
    ((S.equiv T).trans eP.symm).injective

/-- An odd prime dividing `q-1` has cyclic Sylow subgroups in the actual
projective image, for every nondegenerate Hermitian form. -/
theorem sylow_isCyclic_of_dvd_sub_one
    {q p : ℕ} (hq : 1 < q) (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ q - 1)
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q)
    (S : Sylow p (ProjectiveSpecialUnitaryMatrixGroup J)) : IsCyclic S := by
  let : Fact p.Prime := ⟨hp⟩
  have hfixed := card_fixed J hcard hconj
  obtain ⟨e⟩ := FormTransport.exists_projectiveEquiv J q hcard hfixed
  obtain ⟨H, hc, hi⟩ := exists_standard_torus (FormTransport.standardForm J) q
    hcard hfixed rfl
  let := hc
  have hindex : ¬ p ∣ H.index := hi ▸ not_dvd_torus_index hq hp hp2 hd
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hc' := cyclic_sylow_of_index H hindex S'
  change IsCyclic ((S : Subgroup _).map e.toMonoidHom) at hc'
  let := hc'
  let eS := (S : Subgroup _).equivMapOfInjective e.toMonoidHom e.injective
  exact isCyclic_of_injective eS.toMonoidHom eS.injective

/-- The `q-1` branch is excluded from every finite perfect central kernel. -/
theorem not_dvd_cover_kernel_of_dvd_sub_one
    {q p : ℕ} (hq : 1 < q) (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ q - 1)
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q)
    {E : Type v} [Group E] [Finite E]
    (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ p ∣ Nat.card f.toMonoidHom.ker := by
  let : Fact p.Prime := ⟨hp⟩
  exact f.not_dvd_card_multiplier_of_isCyclic_sylow
    (sylow_isCyclic_of_dvd_sub_one J hq hp hp2 hd hcard hconj)

/-- Application to the literal universal projection at every characteristic-two
source parameter. This is an exclusion from the whole kernel order. -/
theorem not_dvd_universal_kernel_of_dvd_sub_one
    {n p : ℕ} (hn : 2 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : p ∣ 2 ^ n - 1)
    (hcard : Nat.card F = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) :
    ¬ p ∣ Nat.card (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker := by
  have hq : 2 < 2 ^ n := lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
    (Nat.pow_le_pow_right (by decide) hn)
  let := projective_isQuasisimple J hq hcard hconj
  exact not_dvd_cover_kernel_of_dvd_sub_one J (by omega) hp hp2 hd hcard hconj
    (universalCover _)

end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.EvenKernelBound.CyclicTorus
