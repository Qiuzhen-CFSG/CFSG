module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.Basic
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFormTransport
public import Theory.GroupTheory.PerfectCentralCoverPrimeReduction

/-!
# Local reductions for even four-dimensional unitary central covers

The standard plane parabolic contains the explicit upper-unitriangular
Sylow two-subgroup, so its index is odd. A section there excludes a double
cover by central transfer. The prime-kernel quotient construction then
reduces an arbitrary central kernel to the double-cover case and the
odd-prime cases. Basis conjugation transports this calculation to the
original Hermitian form while preserving the literal covering kernel.

These are conditional reductions for the vanishing unitary rows of
Aschbacher–Smith I.1.3–4, printed pp.407–408 of `refs/quasithin.pdf`,
and GLS3 §6.1. They do not establish the parabolic sections or the
odd-prime exclusions. In particular the reduction is valid at q = 2,
where its double-cover splitting premise cannot hold for every cover.
The unconditional central-closure application must retain q ≥ 4.
-/

@[expose] public noncomputable section

open BenderSuzuki.MatrixGroups Theory.GroupTheory
open Theory.SpecificGroups.ClassicalUnitary
open PerfectCentralCovering

namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure

universe u
variable {F : Type u} [Field F] [Finite F]

/-- The antidiagonal SU₄ group on the original field and involution. -/
abbrev Standard (J : HermitianForm 4 F) :=
  (UnitaryFourFormTransport.standardForm J).specialSubgroup

/-- The full stabilizer of the standard isotropic coordinate plane. -/
abbrev Plane (J : HermitianForm 4 F) : Subgroup (Standard J) :=
  UnitaryFourFlag.planeParabolicSU F (UnitaryFourFormTransport.standardForm J)

/-- The literal plane parabolic contains the constructed Sylow two-subgroup.
No order formula for SU₄ is required. -/
theorem plane_index_odd [CharP F 2] (J : HermitianForm 4 F) :
    ¬ 2 ∣ (Plane J).index := by
  let S := UnitaryFourSylow.sylow F J.conj J.conj_involutive
  have hS : (S : Subgroup (Standard J)) ≤ Plane J :=
    (UnitaryFourSylow.upper_le_borel F J.conj J.conj_involutive).trans inf_le_right
  exact fun h => S.not_dvd_index (h.trans (Subgroup.index_dvd_of_le hS))

/-- Transfer excludes a double covering that splits over the plane parabolic. -/
theorem not_two_kernel_of_plane_section [CharP F 2] (J : HermitianForm 4 F)
    {E : Type u} [Group E] [Finite E] (c : Cover E (Standard J))
    (s : Plane J →* E) (hs : c.toMonoidHom.comp s = (Plane J).subtype) :
    Nat.card c.toMonoidHom.ker ≠ 2 := by
  intro hc
  exact not_dvd_card_kernel_of_section c (Plane J) (plane_index_odd J) s hs
    (hc ▸ dvd_rfl)

/-- Change basis downstairs, keeping the original covering group upstairs. -/
def standardCover (J : HermitianForm 4 F) (C : Matrix.GeneralLinearGroup (Fin 4) F)
    (hC : J.conjTranspose C.val * J.form * C.val =
      (UnitaryFourFormTransport.standardForm J).form)
    {E : Type u} [Group E] (c : Cover E J.specialSubgroup) :
    Cover E (Standard J) where
  toMonoidHom := (UnitaryFourFormTransport.specialEquiv J C hC).toMonoidHom.comp
    c.toMonoidHom
  surjective := (UnitaryFourFormTransport.specialEquiv J C hC).surjective.comp
    c.surjective
  isPerfect := c.isPerfect
  ker_le_center := by
    rw [MonoidHom.ker_comp_of_injective _ _
      (UnitaryFourFormTransport.specialEquiv J C hC).injective]
    exact c.ker_le_center

omit [Finite F] in
/-- Basis change preserves the literal subgroup of covering-kernel elements. -/
@[simp] theorem standardCover_ker (J : HermitianForm 4 F)
    (C : Matrix.GeneralLinearGroup (Fin 4) F)
    (hC : J.conjTranspose C.val * J.form * C.val =
      (UnitaryFourFormTransport.standardForm J).form)
    {E : Type u} [Group E] (c : Cover E J.specialSubgroup) :
    (standardCover J C hC c).toMonoidHom.ker = c.toMonoidHom.ker :=
  MonoidHom.ker_comp_of_injective _ _
    (UnitaryFourFormTransport.specialEquiv J C hC).injective

omit [Finite F] in
/-- The transported covering map is the same explicit matrix conjugation. -/
@[simp] theorem standardCover_apply (J : HermitianForm 4 F)
    (C : Matrix.GeneralLinearGroup (Fin 4) F)
    (hC : J.conjTranspose C.val * J.form * C.val =
      (UnitaryFourFormTransport.standardForm J).form)
    {E : Type u} [Group E] (c : Cover E J.specialSubgroup) (x : E) :
    ((standardCover J C hC c).toMonoidHom x : Matrix.GeneralLinearGroup (Fin 4) F) =
      C⁻¹ * (c.toMonoidHom x : Matrix.GeneralLinearGroup (Fin 4) F) * C :=
  UnitaryFourFormTransport.specialEquiv_apply J C hC (c.toMonoidHom x)

/-- Arbitrary-form central closure reduces to prime-degree covers of the
antidiagonal model. Both primary exclusions remain explicit here. -/
theorem injective_of_prime_kernel_exclusions (J : HermitianForm 4 F)
    (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (htwo : ∀ (E : Type u) [Group E] [Finite E] (d : Cover E (Standard J)),
      Nat.card d.toMonoidHom.ker ≠ 2)
    (hodd : ∀ (p : ℕ), p.Prime → p ≠ 2 →
      ∀ (E : Type u) [Group E] [Finite E] (d : Cover E (Standard J)),
        Nat.card d.toMonoidHom.ker ≠ p)
    {E : Type u} [Group E] [Finite E] (c : Cover E J.specialSubgroup) :
    Function.Injective c.toMonoidHom := by
  obtain ⟨C, hC⟩ := UnitaryFourFormTransport.exists_standard_basis J n hn hcard hconj
  let d := standardCover J C hC c
  apply c.toMonoidHom.ker_eq_bot_iff.mp
  apply Subgroup.eq_bot_of_card_eq
  by_contra h
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd h
  let : Fact p.Prime := ⟨hp⟩
  have hno : ∀ (D : Type u) [Group D] [Finite D] (e : Cover D (Standard J)),
      Nat.card e.toMonoidHom.ker ≠ p := by
    by_cases hp2 : p = 2
    · subst p
      exact htwo
    · exact hodd p hp hp2
  apply d.not_dvd_card_kernel_of_no_prime_kernel hno
  simpa [d] using hd

/-- A double-cover section on the actual plane parabolic and the odd-prime
exclusions suffice. The reduction also proves characteristic two from the
field cardinality; the two mathematical inputs are not asserted here. -/
theorem injective_of_local_sections (J : HermitianForm 4 F)
    (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (htwo : ∀ (E : Type u) [Group E] [Finite E] (d : Cover E (Standard J)),
      Nat.card d.toMonoidHom.ker = 2 →
        ∃ s : Plane J →* E, d.toMonoidHom.comp s = (Plane J).subtype)
    (hodd : ∀ (p : ℕ), p.Prime → p ≠ 2 →
      ∀ (E : Type u) [Group E] [Finite E] (d : Cover E (Standard J)),
        Nat.card d.toMonoidHom.ker ≠ p)
    {E : Type u} [Group E] [Finite E] (c : Cover E J.specialSubgroup) :
    Function.Injective c.toMonoidHom := by
  let : CharP F 2 := UnitaryFourFormTransport.charP_two n hn hcard
  apply injective_of_prime_kernel_exclusions J n hn hcard hconj _ hodd c
  intro D _ _ d hd
  obtain ⟨s, hs⟩ := htwo D d hd
  exact not_two_kernel_of_plane_section J d s hs hd

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure
