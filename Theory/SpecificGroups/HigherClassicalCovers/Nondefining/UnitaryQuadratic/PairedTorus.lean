module

public import Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryQuadratic.PairedTorus.Coefficients
public import Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryQuadratic.PairedTorus.PrimaryBound
public import Theory.GroupTheory.PerfectCentralCoverThreeCycleNorm

/-!
# Paired unitary tori and perfect central covers

The reciprocal torus and pair swap are transported from the hyperbolic form
to the supplied nondegenerate Hermitian form by actual projective basis
isomorphisms. The full primary coefficient group supplies both generators
and their odd exponent. The covering application uses the literal transported
subgroup and its index.

For every odd prime r dividing p−1, the exact special unitary order bounds
the r-part of the projective group. The full torus order then gives its
prime-to-r index. Thus every finite perfect central cover of the original
projective group has kernel of order prime to r, including r = 3 and all
higher r-power coefficients. No multiplier, covering lift or universal-cover
assertion is used to construct the torus.

Source: Aschbacher–Smith A.2.17, printed p.39, and the perfect-cover
conventions I.1.1–I.1.4, printed pp.407–408.
-/

public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups PerfectCentralCovering
open Theory.SpecificGroups.ClassicalUnitary
open OddFourRanks.Defining ProjectiveKernel

namespace Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryQuadratic.PairedTorus

variable {F : Type*} [Field F] [Finite F]

local instance finiteProjective (J : HermitianForm 4 F) :
    Finite (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : Finite (GL (Fin 4) F) := Finite.of_injective Units.val Units.val_injective
  exact Finite.of_surjective (project J) (project_surjective J)

/-- The full torus order converts the ambient primary bound into its literal prime-to-r index. -/
theorem primary_index_of_card_bound {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (J : HermitianForm 4 F) (hF : Nat.card F = p ^ 2)
    (hc : ∀ x, J.conj x = x ^ p) (hr : r ≠ 2)
    (hb : ¬ r * primaryExponent p r ^ 2 ∣
      Nat.card (ProjectiveSpecialUnitaryMatrixGroup (hyperbolicForm J))) :
    ¬ r ∣ (primaryProjective J r hc).range.index := by
  intro hd
  apply hb
  rw [← (primaryProjective J r hc).range.card_mul_index, card_primary_range J hF hc hr]
  simpa only [Nat.mul_comm r] using Nat.mul_dvd_mul_left (primaryExponent p r ^ 2) hd

/-- The matrices supply every paired-torus premise in the original form once their index is known. -/
theorem exists_paired_torus_of_primary_index {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (J : HermitianForm 4 F) (hF : Nat.card F = p ^ 2)
    (hc : ∀ x, J.conj x = x ^ p) (hr : r ≠ 2)
    (hi : ¬ r ∣ (primaryProjective J r hc).range.index) :
    ∃ (T : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
      (x y s : ProjectiveSpecialUnitaryMatrixGroup J) (m : ℕ),
      closure ({x,y} : Set _) = T ∧ Commute x y ∧
      s*x*s⁻¹ = y ∧ s*y*s⁻¹ = x ∧ m.Coprime 2 ∧ x ^ m = 1 ∧ ¬ r ∣ T.index := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime_pow (p := p) (f := 2) (by
    simpa only [← Nat.card_eq_fintype_card] using hF)
  obtain ⟨e⟩ := exists_hyperbolic_equiv J hF hc
  let C := rootsOfUnity (primaryExponent p r) F
  have hC : ∀ u : C, J.conj (u.val : F) = (u.val : F) :=
    roots_fixed J (Fact.out : p.Prime).one_lt.le hc (primaryExponent_dvd p r)
  have ho : (Nat.card C).Coprime 2 := by
    rw [card_primary_coefficients hF]
    exact primaryExponent_odd p hr
  obtain ⟨x,y,s,hgen,hxy,hsx,hsy,hx⟩ := exists_pair J C hC
  let T := (projective J C hC).range
  refine ⟨T.map e.toMonoidHom, e x, e y, e s, Nat.card C,
    ?_, hxy.map e.toMonoidHom, ?_, ?_, ho, ?_, ?_⟩
  · simpa only [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
      MulEquiv.coe_toMonoidHom] using congrArg (fun U => U.map e.toMonoidHom) hgen
  · simpa only [map_mul, map_inv] using congrArg e hsx
  · simpa only [map_mul, map_inv] using congrArg e hsy
  · simpa only [map_pow, map_one] using congrArg e hx
  · rwa [Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective]

/-- Every finite perfect central cover has prime-to-r kernel under the single remaining ambient order bound. -/
theorem not_dvd_kernel_of_primary_card_bound {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (J : HermitianForm 4 F) (hF : Nat.card F = p ^ 2)
    (hc : ∀ x, J.conj x = x ^ p) (hr : r ≠ 2)
    (hb : ¬ r * primaryExponent p r ^ 2 ∣
      Nat.card (ProjectiveSpecialUnitaryMatrixGroup (hyperbolicForm J)))
    {E : Type*} [Group E] [Finite E]
    (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ r ∣ Nat.card f.toMonoidHom.ker := by
  obtain ⟨T,x,y,s,m,hgen,hxy,hsx,hsy,hm,hx,hi⟩ :=
    exists_paired_torus_of_primary_index J hF hc hr (primary_index_of_card_bound J hF hc hr hb)
  exact f.not_dvd_kernel_of_swapped_pair_at_prime_index T x y s hgen hxy hsx hsy hm hx hi

/-- The actual paired torus has index prime to every odd split prime of p−1. -/
theorem primary_index {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (J : HermitianForm 4 F) (hF : Nat.card F = p ^ 2)
    (hc : ∀ x, J.conj x = x ^ p) (hr2 : r ≠ 2) (hrp : r ≠ p)
    (hd : r ∣ p - 1) :
    ¬ r ∣ (primaryProjective J r hc).range.index := by
  exact primary_index_of_card_bound J hF hc hr2
    (not_dvd_primary_card_bound J hF hc hr2 hrp hd)

/-- The reciprocal paired torus, its two generators and their ambient swap,
transported to the original form with the prime-to-r index proved. -/
theorem exists_paired_torus_prime_index {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (J : HermitianForm 4 F) (hF : Nat.card F = p ^ 2)
    (hc : ∀ x, J.conj x = x ^ p) (hr2 : r ≠ 2) (hrp : r ≠ p)
    (hd : r ∣ p - 1) :
    ∃ (T : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
      (x y s : ProjectiveSpecialUnitaryMatrixGroup J) (m : ℕ),
      closure ({x,y} : Set _) = T ∧ Commute x y ∧
      s*x*s⁻¹ = y ∧ s*y*s⁻¹ = x ∧ m.Coprime 2 ∧ x ^ m = 1 ∧ ¬ r ∣ T.index := by
  exact exists_paired_torus_of_primary_index J hF hc hr2
    (primary_index J hF hc hr2 hrp hd)

/-- The split-prime branch of the degree-four covering argument in A.2.17:
every finite perfect central cover has kernel prime to each odd prime of p−1. -/
theorem not_dvd_kernel_of_split_prime {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (J : HermitianForm 4 F) (hF : Nat.card F = p ^ 2)
    (hc : ∀ x, J.conj x = x ^ p) (hr2 : r ≠ 2) (hrp : r ≠ p)
    (hd : r ∣ p - 1)
    {E : Type*} [Group E] [Finite E]
    (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ r ∣ Nat.card f.toMonoidHom.ker := by
  obtain ⟨T,x,y,s,m,hgen,hxy,hsx,hsy,hm,hx,hi⟩ :=
    exists_paired_torus_prime_index J hF hc hr2 hrp hd
  exact f.not_dvd_kernel_of_swapped_pair_at_prime_index T x y s hgen hxy hsx hsy hm hx hi

end Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryQuadratic.PairedTorus
