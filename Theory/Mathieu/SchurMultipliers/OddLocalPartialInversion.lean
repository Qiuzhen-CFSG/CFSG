module

public import Theory.GroupTheory.CentralExtensionPartialInversion
public import Theory.Mathieu.SchurMultipliers.FiniteCovers
public import Theory.Mathieu.M23.Properties.PointStabilizer

/-!
# Odd central kernels over M₁₁ and M₂₃

Each actual Mathieu model contains an elementary Sylow subgroup of order nine
with a partial inverter. In M₁₁ the standard generator A fixes V and inverts Y.
For M₂₃ we use the already certified Heisenberg generators a,b and their
simultaneous inverter t in M₂₄. If c=[a,b], then a b⁻¹ c⁻¹ and c generate an
elementary group fixing point 11, and t partially inverts this pair. Conjugation
by b moves the fixed point to Atlas point 24, giving elements of the literal
point stabilizer identified with M₂₃.

The nine coordinate products and their relations are checked in the finite
permutation representations. Partial inversion forces any lifted commutator
to have order dividing both two and three. Central Sylow transfer therefore
excludes three from every finite perfect central kernel. The existing cyclic
Sylow bounds exclude the remaining odd primes. No two-primary multiplier
claim is made.

Source: Aschbacher–Smith I.1.1–I.1.3, printed pp.407–408, with the ordinary
component applications in A.3.6, printed pp.43–46.
-/

public section
noncomputable section
open Subgroup PerfectCentralCovering
open scoped commutatorElement
namespace Sporadic.Mathieu.SchurMultipliers.PartialInversionSource

set_option maxRecDepth 100000

private instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

private abbrev Coordinates := Multiplicative (Fin 3 × Fin 3)

private def pairEval {G : Type*} [Group G] (x y : G) (u : Coordinates) : G :=
  x ^ ((Multiplicative.toAdd u).1 : ℕ) *
    y ^ ((Multiplicative.toAdd u).2 : ℕ)

private def pairHom {G : Type*} [Group G] (x y : G)
    (hmul : ∀ u v, pairEval x y (u * v) = pairEval x y u * pairEval x y v) :
    Coordinates →* G where
  toFun := pairEval x y
  map_one' := by simp [pairEval]
  map_mul' := hmul

private theorem pairHom_range {G : Type*} [Group G] (x y : G)
    (hmul : ∀ u v, pairEval x y (u * v) = pairEval x y u * pairEval x y v) :
    (pairHom x y hmul).range = closure ({x, y} : Set G) := by
  apply le_antisymm
  · rintro g ⟨u, rfl⟩
    have hx : x ∈ closure ({x, y} : Set G) := subset_closure (by simp)
    have hy : y ∈ closure ({x, y} : Set G) := subset_closure (by simp)
    exact (closure ({x, y} : Set G)).mul_mem
      ((closure ({x, y} : Set G)).pow_mem hx _)
      ((closure ({x, y} : Set G)).pow_mem hy _)
  · apply (closure_le (pairHom x y hmul).range).mpr
    intro g hg
    rcases hg with rfl | rfl
    · exact ⟨Multiplicative.ofAdd (1, 0), by simp [pairHom, pairEval]⟩
    · exact ⟨Multiplicative.ofAdd (0, 1), by simp [pairHom, pairEval]⟩

private theorem pairHom_card {G : Type*} [Group G] (x y : G)
    (hmul : ∀ u v, pairEval x y (u * v) = pairEval x y u * pairEval x y v)
    (hinj : Function.Injective (pairEval x y)) :
    Nat.card (pairHom x y hmul).range = 9 := by
  have hi : Function.Injective (pairHom x y hmul) := hinj
  have hb : Function.Bijective (pairHom x y hmul).rangeRestrict :=
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr hi,
      MonoidHom.rangeRestrict_surjective _⟩
  rw [← Nat.card_eq_of_bijective (pairHom x y hmul).rangeRestrict hb]
  change Nat.card (Fin 3 × Fin 3) = 9
  simp

private theorem pair_sylow {G : Type*} [Group G] [Finite G] (x y : G)
    (hmul : ∀ u v, pairEval x y (u * v) = pairEval x y u * pairEval x y v)
    (hinj : Function.Injective (pairEval x y))
    (hthree : 3 ^ (Nat.card G).factorization 3 = 9) :
    ∃ Q : Sylow 3 G, closure ({x, y} : Set G) = (Q : Subgroup G) := by
  let Q : Sylow 3 G := Sylow.ofCard (pairHom x y hmul).range
    ((pairHom_card x y hmul hinj).trans hthree.symm)
  exact ⟨Q, (pairHom_range x y hmul).symm⟩

private def m11XPerm : Equiv.Perm (Fin 11) :=
  List.formPerm [0, 4, 3] * List.formPerm [1, 7, 5] * List.formPerm [2, 10, 6]

private def m11YPerm : Equiv.Perm (Fin 11) :=
  List.formPerm [1, 3, 6] * List.formPerm [2, 7, 11] * List.formPerm [4, 10, 5]

private theorem m11_eval_perm (u : Coordinates) :
    (pairEval m11Sylow3GenY m11CentralizerV u : Equiv.Perm (Fin 11)) =
      pairEval m11XPerm m11YPerm u := by
  change (m11Sylow3GenY : Equiv.Perm (Fin 11)) ^ _ *
    (m11CentralizerV : Equiv.Perm (Fin 11)) ^ _ = _
  rw [m11Sylow3GenY_perm, m11CentralizerV_perm]
  rfl

private theorem m11_perm_mul : ∀ u v : Coordinates,
    pairEval m11XPerm m11YPerm (u * v) =
      pairEval m11XPerm m11YPerm u * pairEval m11XPerm m11YPerm v := by
  decide +kernel

private theorem m11_perm_injective :
    Function.Injective (pairEval m11XPerm m11YPerm) := by
  decide +kernel

private theorem m11_pair_mul (u v : Coordinates) :
    pairEval m11Sylow3GenY m11CentralizerV (u * v) =
      pairEval m11Sylow3GenY m11CentralizerV u *
        pairEval m11Sylow3GenY m11CentralizerV v := by
  apply Subtype.ext
  change (pairEval m11Sylow3GenY m11CentralizerV (u * v) : Equiv.Perm (Fin 11)) =
    (pairEval m11Sylow3GenY m11CentralizerV u : Equiv.Perm (Fin 11)) *
      (pairEval m11Sylow3GenY m11CentralizerV v : Equiv.Perm (Fin 11))
  rw [m11_eval_perm, m11_eval_perm, m11_eval_perm]
  exact m11_perm_mul u v

private theorem m11_pair_injective :
    Function.Injective (pairEval m11Sylow3GenY m11CentralizerV) := by
  intro u v h
  apply m11_perm_injective
  rw [← m11_eval_perm, ← m11_eval_perm]
  exact congrArg (fun g : M11 => (g : Equiv.Perm (Fin 11))) h

private theorem m11_x_cube : m11Sylow3GenY ^ 3 = 1 := by
  apply Subtype.ext
  change (m11Sylow3GenY : Equiv.Perm (Fin 11)) ^ 3 = 1
  rw [m11Sylow3GenY_perm]
  decide +kernel

private theorem m11_pair_commute : Commute m11Sylow3GenY m11CentralizerV := by
  change m11Sylow3GenY * m11CentralizerV = m11CentralizerV * m11Sylow3GenY
  apply Subtype.ext
  change (m11Sylow3GenY : Equiv.Perm (Fin 11)) * (m11CentralizerV : Equiv.Perm (Fin 11)) =
    (m11CentralizerV : Equiv.Perm (Fin 11)) * (m11Sylow3GenY : Equiv.Perm (Fin 11))
  rw [m11Sylow3GenY_perm, m11CentralizerV_perm]
  decide +kernel

private theorem m11_partial_inversion :
    m11GeneratorAInM11 * m11Sylow3GenY * m11GeneratorAInM11⁻¹ = m11Sylow3GenY⁻¹ := by
  apply Subtype.ext
  change m11GeneratorA * (m11Sylow3GenY : Equiv.Perm (Fin 11)) * m11GeneratorA⁻¹ =
    (m11Sylow3GenY : Equiv.Perm (Fin 11))⁻¹
  rw [m11Sylow3GenY_perm]
  decide +kernel

private theorem m11_fixed_generator : Commute m11GeneratorAInM11 m11CentralizerV := by
  change m11GeneratorAInM11 * m11CentralizerV = m11CentralizerV * m11GeneratorAInM11
  apply Subtype.ext
  change m11GeneratorA * (m11CentralizerV : Equiv.Perm (Fin 11)) =
    (m11CentralizerV : Equiv.Perm (Fin 11)) * m11GeneratorA
  rw [m11CentralizerV_perm]
  decide +kernel

/-- Three does not divide the kernel of any finite perfect central cover of M₁₁. -/
theorem m11_cover_kernel_not_three {E : Type*} [Group E] [Finite E]
    (f : Cover E M11) : ¬ 3 ∣ Nat.card f.toMonoidHom.ker := by
  let : Group.IsPerfect E := f.isPerfect
  obtain ⟨Q, hQ⟩ := pair_sylow m11Sylow3GenY m11CentralizerV
    m11_pair_mul m11_pair_injective (by rw [m11_order]; decide +kernel)
  exact CentralExtension.not_dvd_card_kernel_of_partial_inversion
    f.toMonoidHom f.surjective f.ker_le_center Q
    m11Sylow3GenY m11CentralizerV m11GeneratorAInM11 hQ
    (by decide : Nat.Coprime 3 2) m11_x_cube m11_pair_commute
    m11_partial_inversion m11_fixed_generator

open M24ValueBoundParabolics.ThreeModel

private abbrev PointStabilizer := MulAction.stabilizer M24 (24 : Fin 24)

private def m23X24 : M24 := b * (a * b⁻¹ * ⁅a, b⁆⁻¹) * b⁻¹
private def m23Y24 : M24 := b * ⁅a, b⁆ * b⁻¹
private def m23R24 : M24 := b * t * b⁻¹

private def m23XPerm : Equiv.Perm (Fin 24) :=
  List.formPerm [1, 12, 21] * List.formPerm [2, 5, 13] *
    List.formPerm [3, 10, 22] * List.formPerm [6, 23, 15] *
    List.formPerm [8, 9, 14] * List.formPerm [16, 17, 19]
private def m23YPerm : Equiv.Perm (Fin 24) :=
  List.formPerm [1, 5, 19] * List.formPerm [2, 17, 21] *
    List.formPerm [3, 22, 10] * List.formPerm [4, 20, 7] *
    List.formPerm [6, 23, 15] * List.formPerm [12, 13, 16]
private def m23RPerm : Equiv.Perm (Fin 24) :=
  Equiv.swap 1 12 * Equiv.swap 3 15 * Equiv.swap 5 13 * Equiv.swap 6 22 *
    Equiv.swap 9 14 * Equiv.swap 10 23 * Equiv.swap 11 18 * Equiv.swap 16 19

private theorem m23X24_perm : (m23X24 : Equiv.Perm (Fin 24)) = m23XPerm := by
  change bPerm * (aPerm * bPerm⁻¹ * ⁅aPerm, bPerm⁆⁻¹) * bPerm⁻¹ = m23XPerm
  decide +kernel
private theorem m23Y24_perm : (m23Y24 : Equiv.Perm (Fin 24)) = m23YPerm := by
  change bPerm * ⁅aPerm, bPerm⁆ * bPerm⁻¹ = m23YPerm
  decide +kernel
private theorem m23R24_perm : (m23R24 : Equiv.Perm (Fin 24)) = m23RPerm := by
  change bPerm * tPerm * bPerm⁻¹ = m23RPerm
  decide +kernel

private def m23X : PointStabilizer := ⟨m23X24, by
  change (m23X24 : Equiv.Perm (Fin 24)) (24 : Fin 24) = (24 : Fin 24)
  rw [m23X24_perm]
  decide +kernel⟩
private def m23Y : PointStabilizer := ⟨m23Y24, by
  change (m23Y24 : Equiv.Perm (Fin 24)) (24 : Fin 24) = (24 : Fin 24)
  rw [m23Y24_perm]
  decide +kernel⟩
private def m23R : PointStabilizer := ⟨m23R24, by
  change (m23R24 : Equiv.Perm (Fin 24)) (24 : Fin 24) = (24 : Fin 24)
  rw [m23R24_perm]
  decide +kernel⟩

private theorem m23_eval_perm (u : Coordinates) :
    ((pairEval m23X m23Y u : M24) : Equiv.Perm (Fin 24)) =
      pairEval m23XPerm m23YPerm u := by
  change (m23X24 : Equiv.Perm (Fin 24)) ^ _ *
    (m23Y24 : Equiv.Perm (Fin 24)) ^ _ = _
  rw [m23X24_perm, m23Y24_perm]
  rfl

private theorem m23_perm_mul : ∀ u v : Coordinates,
    pairEval m23XPerm m23YPerm (u * v) =
      pairEval m23XPerm m23YPerm u * pairEval m23XPerm m23YPerm v := by
  decide +kernel

private theorem m23_perm_distinguish : ∀ u v : Coordinates,
    pairEval m23XPerm m23YPerm u 1 = pairEval m23XPerm m23YPerm v 1 → u = v := by
  decide +kernel

private theorem m23_pair_mul (u v : Coordinates) :
    pairEval m23X m23Y (u * v) = pairEval m23X m23Y u * pairEval m23X m23Y v := by
  apply Subtype.ext
  apply Subtype.ext
  change ((pairEval m23X m23Y (u * v) : M24) : Equiv.Perm (Fin 24)) =
    ((pairEval m23X m23Y u : M24) : Equiv.Perm (Fin 24)) *
      ((pairEval m23X m23Y v : M24) : Equiv.Perm (Fin 24))
  rw [m23_eval_perm, m23_eval_perm, m23_eval_perm]
  exact m23_perm_mul u v

private theorem m23_pair_injective : Function.Injective (pairEval m23X m23Y) := by
  intro u v h
  apply m23_perm_distinguish u v
  rw [← m23_eval_perm, ← m23_eval_perm]
  exact congrArg (fun g : PointStabilizer => ((g : M24) : Equiv.Perm (Fin 24)) 1) h

private theorem m23_x_cube : m23X ^ 3 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  change (m23X24 : Equiv.Perm (Fin 24)) ^ 3 = 1
  rw [m23X24_perm]
  decide +kernel

private theorem m23_pair_commute : Commute m23X m23Y := by
  change m23X * m23Y = m23Y * m23X
  apply Subtype.ext
  apply Subtype.ext
  change (m23X24 : Equiv.Perm (Fin 24)) * (m23Y24 : Equiv.Perm (Fin 24)) =
    (m23Y24 : Equiv.Perm (Fin 24)) * (m23X24 : Equiv.Perm (Fin 24))
  rw [m23X24_perm, m23Y24_perm]
  decide +kernel

private theorem m23_partial_inversion : m23R * m23X * m23R⁻¹ = m23X⁻¹ := by
  apply Subtype.ext
  apply Subtype.ext
  change (m23R24 : Equiv.Perm (Fin 24)) * (m23X24 : Equiv.Perm (Fin 24)) *
    (m23R24 : Equiv.Perm (Fin 24))⁻¹ = (m23X24 : Equiv.Perm (Fin 24))⁻¹
  rw [m23R24_perm, m23X24_perm]
  decide +kernel

private theorem m23_fixed_generator : Commute m23R m23Y := by
  change m23R * m23Y = m23Y * m23R
  apply Subtype.ext
  apply Subtype.ext
  change (m23R24 : Equiv.Perm (Fin 24)) * (m23Y24 : Equiv.Perm (Fin 24)) =
    (m23Y24 : Equiv.Perm (Fin 24)) * (m23R24 : Equiv.Perm (Fin 24))
  rw [m23R24_perm, m23Y24_perm]
  decide +kernel

/-- Three does not divide the kernel of any finite perfect central cover of M₂₃.
The original cover is transported along the actual point-stabilizer equivalence. -/
theorem m23_cover_kernel_not_three {E : Type*} [Group E] [Finite E]
    (f : Cover E M23) : ¬ 3 ∣ Nat.card f.toMonoidHom.ker := by
  let : Group.IsPerfect E := f.isPerfect
  let e := m23EquivM24PointStabilizer
  have hcard : Nat.card PointStabilizer = 10200960 :=
    (Nat.card_congr e.toEquiv).symm.trans m23_order
  obtain ⟨Q, hQ⟩ := pair_sylow m23X m23Y m23_pair_mul m23_pair_injective
    (by rw [hcard]; decide +kernel)
  let g : E →* PointStabilizer := e.toMonoidHom.comp f.toMonoidHom
  have hg : g.ker = f.toMonoidHom.ker :=
    MonoidHom.ker_comp_of_injective f.toMonoidHom e.toMonoidHom e.injective
  have h := CentralExtension.not_dvd_card_kernel_of_partial_inversion
    g (e.surjective.comp f.surjective) (hg.symm ▸ f.ker_le_center) Q
    m23X m23Y m23R hQ (by decide : Nat.Coprime 3 2)
    m23_x_cube m23_pair_commute m23_partial_inversion m23_fixed_generator
  simpa only [hg] using h

private theorem two_group_of_prime_restriction {K : Type*} [Group K] [Finite K]
    (hthree : ¬ 3 ∣ Nat.card K)
    (hother : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ¬ p ∣ Nat.card K) :
    IsPGroup 2 K := by
  apply (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr
  intro p hp
  obtain ⟨hprime, hdiv, _⟩ := Nat.mem_primeFactors.mp hp
  have heq : p = 2 := by
    by_contra htwo
    by_cases hp3 : p = 3
    · exact hthree (hp3 ▸ hdiv)
    · exact hother p hprime htwo hp3 hdiv
  subst p
  exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_rfl, by decide⟩

/-- Every finite perfect central kernel over M₁₁ is a two-group. -/
theorem m11_cover_kernel_isTwoGroup {E : Type*} [Group E] [Finite E]
    (f : Cover E M11) : IsPGroup 2 f.toMonoidHom.ker := by
  let : Group.IsPerfect E := f.isPerfect
  apply two_group_of_prime_restriction (m11_cover_kernel_not_three f)
  intro p hp h2 h3
  let : Fact p.Prime := ⟨hp⟩
  exact SchurMultipliers.m11_cover_kernel_prime_restriction f h2 h3

/-- Every finite perfect central kernel over M₂₃ is a two-group. -/
theorem m23_cover_kernel_isTwoGroup {E : Type*} [Group E] [Finite E]
    (f : Cover E M23) : IsPGroup 2 f.toMonoidHom.ker := by
  let : Group.IsPerfect E := f.isPerfect
  apply two_group_of_prime_restriction (m23_cover_kernel_not_three f)
  intro p hp h2 h3
  let : Fact p.Prime := ⟨hp⟩
  exact SchurMultipliers.m23_cover_kernel_prime_restriction f h2 h3

end Sporadic.Mathieu.SchurMultipliers.PartialInversionSource
