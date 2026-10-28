module

public import Theory.SpecificGroups.SL2.BorelSmallInvariant.Basic
public import Theory.NumberTheory.BinarySignedTorus
public import Theory.GroupTheory.PResidual.PrimeSetFiniteImage
public import Theory.Representation.HigherFieldBorelFixedSpaces.Extension
public import Theory.Representation.HigherFieldBorelFixedSpaces.Natural


/-!
# The {2,3}-residual of a higher-field rank-one Borel

For |F|=2ⁿ with n>2, a prime divisor greater than three of |Fˣ| supplies
a nonidentity diagonal element in O^{2,3}(B). Commuting that element with
the upper root group puts the whole root group in the residual. Thus the
residual has odd index in SL₂(F) and zero fixed space on the natural plane.

For an arbitrary binary module whose commutator section is this natural
plane, odd-index averaging lifts the fixed-space calculation through the
central layers. No splitting of those layers is assumed. The actor
isomorphism, the marked Borel and one equivariant section identification
are retained in the statement.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
13.6.18, printed p.931 (PDF p.948).
-/

@[expose] public section

open Subgroup Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups commutatorElement

namespace Matrix.SpecialLinearGroup.RankOneResidual
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem prime_order_mem {A : Type*} [Group A] [Finite A]
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (a : A) (ha : orderOf a = p) :
    a ∈ piResidual twoThreePrimes A := by
  apply mem_sInf.mpr
  rintro N ⟨hN, hpi⟩
  let _ := hN
  let q := QuotientGroup.mk' N
  apply (QuotientGroup.eq_one_iff a).mp
  have hd : orderOf (q a) ∣ p := ha ▸ orderOf_map_dvd q a
  rcases (Nat.dvd_prime hp).mp hd with h | h
  · exact orderOf_eq_one_iff.mp h
  · have hpi' := (IsPiGroup_iff _ _).mp hpi ⟨p, hp⟩
      (h ▸ orderOf_dvd_natCard (q a))
    change p = 2 ∨ p = 3 at hpi'
    omega

private theorem prime_in_torus {n : ℕ} (hn : 2 < n) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ p ∣ 2 ^ n - 1 := by
  by_cases hn3 : n = 3
  · subst n
    exact ⟨7, by norm_num, by norm_num, by norm_num⟩
  · exact Nat.BinarySignedTorus.exists_prime_gt_three_dvd_sub (by omega)

omit [CharP F 2] in
/-- A prime-to-six torus element lies in the literal {2,3}-residual. -/
theorem exists_diagonal {n : ℕ} (hn : 2 < n) (hF : Nat.card F = 2 ^ n) :
    ∃ a : Fˣ, (a : F) ≠ 1 ∧
      borelDiagonalHom a ∈ piResidual twoThreePrimes (rankOneBorel F) := by
  obtain ⟨p, hp, hp3, hd⟩ := prime_in_torus hn
  let _ : Fact p.Prime := ⟨hp⟩
  have hd' : p ∣ Nat.card Fˣ := by rwa [Nat.card_units, hF]
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' p hd'
  have hainj : Function.Injective (borelDiagonalHom (F := F)) := by
    intro a b hab
    apply Units.ext
    exact congrArg (fun x : rankOneBorel F => x.val.val 0 0) hab
  have haa : (a : F) ≠ 1 := by
    intro he
    have he' : a = 1 := Units.ext he
    rw [he', orderOf_one] at ha
    omega
  refine ⟨a, haa, prime_order_mem hp hp3 _ ?_⟩
  exact (orderOf_injective borelDiagonalHom hainj a).trans ha

/-- The embedded {2,3}-residual of the standard rank-one Borel. -/
abbrev residual : Subgroup SL(2, F) :=
  (piResidual twoThreePrimes (rankOneBorel F)).map (rankOneBorel F).subtype

/-- The residual contains the full upper root group, not merely an odd torus. -/
theorem upper_le_residual {n : ℕ} (hn : 2 < n) (hF : Nat.card F = 2 ^ n) :
    upperUnipotent F ≤ residual (F := F) := by
  obtain ⟨a, ha, haR⟩ := exists_diagonal hn hF
  have hasq : (a : F) ^ 2 ≠ 1 := by
    intro h
    exact ha ((frobenius_inj F 2) (by simpa [frobenius_def] using h))
  intro x hx
  obtain ⟨t, rfl⟩ := (mem_upperUnipotent F x).mp hx
  refine mem_map.mpr ⟨⟨transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one t,
    upper_mem_rankOneBorel t⟩, ?_, rfl⟩
  apply mem_sInf.mpr
  rintro N ⟨hN, hpi⟩
  have haN := mem_sInf.mp haR N ⟨hN, hpi⟩
  let b := t / ((a : F)^2 - 1)
  let d : rankOneBorel F := borelDiagonalHom a
  let v : rankOneBorel F := ⟨transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one b,
    upper_mem_rankOneBorel b⟩
  have hc : ⁅d, v⁆ ∈ N := by
    simpa only [commutatorElement_def, mul_assoc] using
      N.mul_mem haN (hN.conj_mem _ (N.inv_mem haN) v)
  have he : ⁅d, v⁆ = ⟨transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one t,
      upper_mem_rankOneBorel t⟩ := by
    apply Subtype.ext
    exact commutator_diag2_transvection (a : F) a.ne_zero b t
      (div_mul_cancel₀ t (sub_ne_zero_of_ne hasq)).symm
  exact he ▸ hc

/-- The residual has odd index in the whole SL₂ group. -/
theorem residual_odd_index {n : ℕ} (hn : 2 < n) (hF : Nat.card F = 2 ^ n) :
    Odd (residual (F := F)).index := by
  have h := (upperUnipotentSylow F 2).not_dvd_index
  have hd := Subgroup.index_dvd_of_le (upper_le_residual hn hF)
  have hu : Odd (upperUnipotent F).index := by
    rw [Nat.odd_iff]
    change ¬ 2 ∣ (upperUnipotent F).index at h
    omega
  exact hu.of_dvd_nat hd

open Representation Representation.BinaryOffender Representation.HigherFieldBorelFixedSpaces
variable [Algebra (ZMod 2) F]

omit [CharP F 2] in
/-- The natural section has no nonzero vector fixed by O^{2,3}(B). -/
theorem natural_fixedSpace {n : ℕ} (hn : 2 < n) (hF : Nat.card F = 2 ^ n) :
    fixedSpace (binaryNatural (F := F) 2) (residual (F := F)) = ⊥ := by
  obtain ⟨a, ha, haR⟩ := exists_diagonal hn hF
  apply (Submodule.eq_bot_iff _).mpr
  intro v hv
  exact diagonal_two_fixed_eq_zero a ha v
    (hv ⟨_, mem_map_of_mem (rankOneBorel F).subtype haR⟩)

end Matrix.SpecialLinearGroup.RankOneResidual
namespace Matrix.SpecialLinearGroup.RankOneResidual
open Representation Representation.BinaryOffender Representation.HigherFieldBorelFixedSpaces
variable {F A W : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [Group A] [Finite A] [AddCommGroup W] [Module (ZMod 2) W]

/-- One equivariant identification of the literal section D/C_D(A). -/
structure NaturalSection (ρ : Representation (ZMod 2) A W)
    (D : Submodule (ZMod 2) W) where
  actor : A ≃* SL(2, F)
  invariant : ∀ (a : A) (d : D), ρ a d ∈ D
  coordinates : (D ⧸ ρ.invariants.comap D.subtype) ≃ₗ[ZMod 2] (Fin 2 → F)
  equivariant : ∀ (a : A) (d : D),
    coordinates (Submodule.Quotient.mk (⟨ρ a d, invariant a d⟩ : D)) =
      (actor a).val *ᵥ coordinates (Submodule.Quotient.mk d)

/-- Fixed-space equality for the whole module, including its central layers.
The displacement hypothesis says that A is trivial on W/D. -/
theorem fixedSpace_residual_eq_invariants {n : ℕ} (hn : 2 < n)
    (hF : Nat.card F = 2 ^ n) (ρ : Representation (ZMod 2) A W)
    (D : Submodule (ZMod 2) W) (s : NaturalSection (F := F) ρ D)
    (hquot : ∀ (a : A) (w : W), ρ a w - w ∈ D)
    (B : Subgroup A) (hB : B.map s.actor.toMonoidHom = rankOneBorel F) :
    fixedSpace ρ ((piResidual twoThreePrimes B).map B.subtype) = ρ.invariants := by
  let R := (piResidual twoThreePrimes B).map B.subtype
  have hmap : R.map s.actor.toMonoidHom = residual (F := F) := by
    rw [map_embedded_piResidual, hB]
  have hindex : Odd R.index := by
    rw [← Subgroup.index_map_of_bijective (f := s.actor.toMonoidHom) s.actor.bijective R, hmap]
    exact residual_odd_index hn hF
  let actor := s.actor.toMonoidHom.comp R.subtype
  have hrange : actor.range = residual (F := F) := by
    rw [MonoidHom.range_comp, range_subtype]
    exact hmap
  exact odd_index_fixedSpace_extension_of_model_section ρ (binaryNatural 2)
    R (residual (F := F)) ρ.invariants D hindex hquot le_rfl
    (fun a d => s.invariant a d) actor hrange s.coordinates
    (fun a d => s.equivariant a d) (natural_fixedSpace hn hF)
end Matrix.SpecialLinearGroup.RankOneResidual
