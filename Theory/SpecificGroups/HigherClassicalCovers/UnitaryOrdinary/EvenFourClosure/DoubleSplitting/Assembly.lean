module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.DoubleSplitting.LeviLift

/-!
# Assembling compatible lifts over the unitary plane local

Write each local element as its radical coordinate times its block diagonal
Levi coordinate. An equivariant lift of the radical makes the product of the
two lifted coordinates multiplicative. The Levi lift is constructed without
additional assumptions. The resulting section on the determinant-one local,
whose index in SU₄ is odd, excludes a double cover by central transfer. This
also gives the requested full-plane section and its original transfer consumer.

The radical section remains an explicit premise. These are assembly results
for Aschbacher–Smith I.1.3–4, printed pp.407–408 of `refs/quasithin.pdf`,
and GLS3 §6.1, not an unconditional proof of the unitary multiplier row.
-/

@[expose] public noncomputable section

open BenderSuzuki.MatrixGroups Theory.GroupTheory
open Theory.SpecificGroups.ClassicalUnitary PerfectCentralCovering

namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.DoubleSplitting
universe u
variable {F : Type u} [Field F] [Finite F] [CharP F 2]

/-- The radical coordinate of the actual decomposition into radical and Levi. -/
def radicalPart (J : HermitianForm 4 F) (g : Local J) : Radical J :=
  ⟨g * (levi J (restriction J g))⁻¹, by simp⟩

/-- Multiplication of these coordinates uses the literal conjugation action. -/
theorem radicalPart_mul (J : HermitianForm 4 F) (g h : Local J) :
    radicalPart J (g * h) = radicalPart J g *
      MulAut.conjNormal (levi J (restriction J g)) (radicalPart J h) := by
  apply Subtype.ext
  simp only [radicalPart, map_mul, mul_inv_rev, Subgroup.coe_mul, MulAut.conjNormal_apply]
  group

/-- Compatible radical and Levi lifts give a homomorphism on the whole local. -/
def localSection (J : HermitianForm 4 F)
    {E : Type u} [Group E] (d : Cover E (Standard J))
    (r : Radical J →* E)
    (heq : ∀ (g : Local J) (e : E), d.toMonoidHom e = g →
      ∀ x : Radical J, r (MulAut.conjNormal g x) = e * r x * e⁻¹)
    (l : Matrix.SpecialLinearGroup (Fin 2) F →* E)
    (hl : d.toMonoidHom.comp l = leviInclusion J) : Local J →* E where
  toFun g := r (radicalPart J g) * l (restriction J g)
  map_one' := by
    have h : radicalPart J 1 = 1 := by apply Subtype.ext; simp [radicalPart]
    simp [h]
  map_mul' g h := by
    rw [radicalPart_mul, map_mul r, heq _ (l (restriction J g))
      (DFunLike.congr_fun hl (restriction J g))]
    simp only [map_mul]
    group

/-- The assembled homomorphism lifts the original local subgroup inclusion. -/
theorem localSection_comp (J : HermitianForm 4 F)
    {E : Type u} [Group E] (d : Cover E (Standard J))
    (r : Radical J →* E)
    (hr : d.toMonoidHom.comp r = radicalInclusion J)
    (heq : ∀ (g : Local J) (e : E), d.toMonoidHom e = g →
      ∀ x : Radical J, r (MulAut.conjNormal g x) = e * r x * e⁻¹)
    (l : Matrix.SpecialLinearGroup (Fin 2) F →* E)
    (hl : d.toMonoidHom.comp l = leviInclusion J) :
    d.toMonoidHom.comp (localSection J d r heq l hl) = (Local J).subtype := by
  apply MonoidHom.ext
  intro g
  change d.toMonoidHom (r (radicalPart J g) * l (restriction J g)) = g
  have hr' (x : Radical J) : d.toMonoidHom (r x) = radicalInclusion J x :=
    DFunLike.congr_fun hr x
  have hl' (A : Matrix.SpecialLinearGroup (Fin 2) F) :
      d.toMonoidHom (l A) = leviInclusion J A := DFunLike.congr_fun hl A
  rw [map_mul, hr', hl']
  change ((g * (levi J (restriction J g))⁻¹ : Local J) : Standard J) *
    (levi J (restriction J g) : Standard J) = g
  simp

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.DoubleSplitting

open BenderSuzuki.MatrixGroups Theory.GroupTheory
open Theory.SpecificGroups.ClassicalUnitary PerfectCentralCovering

namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.DoubleSplitting
universe u
variable {F : Type u} [Field F] [Finite F] [CharP F 2]

omit [Field F] [Finite F] [CharP F 2] in
/-- The source parameter excludes the exceptional four-element Levi field. -/
theorem eight_le_card (n : ℕ) (hn : 2 ≤ n)
    (hcard : Nat.card F = (2 ^ n) ^ 2) : 8 ≤ Nat.card F := by
  have hpow : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
  norm_num at hpow
  rw [hcard]
  nlinarith

/-- An equivariant radical section excludes the double cover by local transfer,
and therefore supplies the requested full-plane section. This remains conditional
on construction of the radical section. -/
theorem plane_section_of_equivariant_radical_section (J : HermitianForm 4 F)
    (hF : 8 ≤ Nat.card F) {E : Type u} [Group E] [Finite E]
    (d : Cover E (Standard J)) (hd : Nat.card d.toMonoidHom.ker = 2)
    (r : Radical J →* E) (hr : d.toMonoidHom.comp r = radicalInclusion J)
    (heq : ∀ (g : Local J) (e : E), d.toMonoidHom e = g →
      ∀ x : Radical J, r (MulAut.conjNormal g x) = e * r x * e⁻¹) :
    ∃ s : Plane J →* E, d.toMonoidHom.comp s = (Plane J).subtype := by
  obtain ⟨l, hl⟩ := exists_levi_lift J hF d
  exact (not_two_kernel_of_local_section J d (localSection J d r heq l hl)
    (localSection_comp J d r hr heq l hl) hd).elim

/-- Apply the full-plane transfer consumer with the section just obtained. -/
theorem not_two_kernel_of_equivariant_radical_section (J : HermitianForm 4 F)
    (hF : 8 ≤ Nat.card F) {E : Type u} [Group E] [Finite E]
    (d : Cover E (Standard J))
    (r : Radical J →* E) (hr : d.toMonoidHom.comp r = radicalInclusion J)
    (heq : ∀ (g : Local J) (e : E), d.toMonoidHom e = g →
      ∀ x : Radical J, r (MulAut.conjNormal g x) = e * r x * e⁻¹) :
    Nat.card d.toMonoidHom.ker ≠ 2 := by
  intro hd
  obtain ⟨s, hs⟩ := plane_section_of_equivariant_radical_section J hF d hd r hr heq
  exact not_two_kernel_of_plane_section J d s hs hd

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.DoubleSplitting
