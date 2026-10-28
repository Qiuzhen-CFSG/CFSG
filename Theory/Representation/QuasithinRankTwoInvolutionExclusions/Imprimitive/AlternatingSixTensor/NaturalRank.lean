module

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
public import Theory.SpecificGroups.Alternating.SmallInvolutionCentralizers
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Imprimitive.Split

/-!
# Involution rank in the natural binary A₆-module

The module is the actual even-weight six-point permutation core modulo
constants. Its fifteen nonzero vectors are the duad classes. The double
transposition (01)(23) fixes exactly three duads, so its fixed space has
four elements and dimension two. Rank-nullity gives displacement rank two.
The existing cycle-type theorem for alternating groups of degree at most six
and an explicit intertwiner transport this calculation to every A₆ involution.
Only the fifteen-duad representative calculation uses finite computation.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, §B.3,
G.11.2(10), printed p.364, and the rank exclusion in 6.2.19, printed p.691.
-/

@[expose] public section

namespace Representation.RankTwo.Imprimitive.AlternatingSixTensor
open BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open Theory.SpecificGroups.SymmetricSix (pair)

private def fixedDuads (p : Equiv.Perm (Fin 6)) : Finset Duad :=
  Finset.univ.filter (fun d => pair (p d.val.1) (p d.val.2) = pair d.val.1 d.val.2)

private def representative : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 2 3

private theorem representative_fixedDuads_card : (fixedDuads representative).card = 3 := by
  decide +kernel

private theorem fixed_duad (p : Equiv.Perm (Fin 6)) (d : Duad) :
    naturalRepresentation (Fin 6) p (duadVector d) = duadVector d ↔ d ∈ fixedDuads p := by
  rw [duadVector, pairVector_map, pairVector_eq_iff
    (p.injective.ne (ne_of_lt d.property)) (ne_of_lt d.property)]
  simp [fixedDuads]

private def fixedVector (p : Equiv.Perm (Fin 6)) :
    Option {d : Duad // d ∈ fixedDuads p} →
      LinearMap.ker (naturalRepresentation (Fin 6) p - LinearMap.id)
  | none => 0
  | some d => ⟨duadVector d.val, by
      change naturalRepresentation (Fin 6) p (duadVector d.val) - duadVector d.val = 0
      exact sub_eq_zero.mpr ((fixed_duad p d.val).mpr d.property)⟩

private theorem fixedVector_injective (p : Equiv.Perm (Fin 6)) :
    Function.Injective (fixedVector p) := by
  intro a b h
  have hh := congrArg Subtype.val h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b => exact False.elim (duadVector_ne_zero b.val hh.symm)
  | some a =>
    cases b with
    | none => exact False.elim (duadVector_ne_zero a.val hh)
    | some b => exact congrArg some (Subtype.ext (duadVector_injective hh))

private theorem fixedVector_surjective (p : Equiv.Perm (Fin 6)) :
    Function.Surjective (fixedVector p) := by
  intro v
  rcases vector_cases v.val with h | ⟨d, hd⟩
  · exact ⟨none, Subtype.ext h.symm⟩
  · have hfix : naturalRepresentation (Fin 6) p (duadVector d) = duadVector d := by
      apply sub_eq_zero.mp
      have hv := v.property
      change naturalRepresentation (Fin 6) p v.val - v.val = 0 at hv
      rwa [hd] at hv
    exact ⟨some ⟨d, (fixed_duad p d).mp hfix⟩, Subtype.ext hd.symm⟩

private theorem finrank_representative :
    Module.finrank (ZMod 2)
      (LinearMap.range (naturalRepresentation (Fin 6) representative - LinearMap.id)) = 2 := by
  let p := representative
  have hc : Nat.card (LinearMap.ker (naturalRepresentation (Fin 6) p - LinearMap.id)) = 4 := by
    rw [← Nat.card_congr (Equiv.ofBijective (fixedVector p)
      ⟨fixedVector_injective p, fixedVector_surjective p⟩)]
    rw [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_coe,
      show (fixedDuads p).card = 3 from representative_fixedDuads_card]
  have hk : Module.finrank (ZMod 2)
      (LinearMap.ker (naturalRepresentation (Fin 6) p - LinearMap.id)) = 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
    exact Nat.pow_right_injective (by decide : 1 < 2) hc
  have hh := (naturalRepresentation (Fin 6) p - LinearMap.id).finrank_range_add_finrank_ker
  rw [hk, finrank_natural_even (Fin 6) (by decide)] at hh
  norm_num at hh
  have hr : Module.finrank (ZMod 2)
      (LinearMap.range (naturalRepresentation (Fin 6) p - LinearMap.id)) = 2 := by omega
  exact hr
private def actorEquiv (g : Equiv.Perm (Fin 6)) :
    natural (Fin 6) ≃ₗ[ZMod 2] natural (Fin 6) where
  toLinearMap := naturalRepresentation (Fin 6) g
  invFun := naturalRepresentation (Fin 6) g⁻¹
  left_inv v := by
    change naturalRepresentation (Fin 6) g⁻¹ (naturalRepresentation (Fin 6) g v) = v
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply]
  right_inv v := by
    change naturalRepresentation (Fin 6) g (naturalRepresentation (Fin 6) g⁻¹ v) = v
    simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply]

/-- A nontrivial even involution has rank two on the actual natural quotient. -/
theorem finrank_natural_involution (p : Equiv.Perm (Fin 6))
    (hp : p.sign = 1) (h2 : p * p = 1) (hne : p ≠ 1) :
    Module.finrank (ZMod 2)
      (LinearMap.range (naturalRepresentation (Fin 6) p - LinearMap.id)) = 2 := by
  let a : alternatingGroup (Fin 6) := ⟨p, hp⟩
  have ha : orderOf a = 2 := orderOf_eq_prime
    (Subtype.ext (by simpa [pow_two] using h2))
    (fun h => hne (congrArg Subtype.val h))
  have hct := alternatingGroup.involution_cycleType_of_degree_le_six (by decide) a ha
  have hrep : representative.cycleType = {2, 2} :=
    Equiv.Perm.cycleType_swap_mul_swap_of_nodup (by decide)
  have hconj : IsConj p representative :=
    Equiv.Perm.isConj_of_cycleType_eq (hct.trans hrep.symm)
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  have he := (displacementRangeEquiv (actorEquiv g)
    (naturalRepresentation (Fin 6) p) (naturalRepresentation (Fin 6) representative)
    (by
      intro v
      rw [← hg]
      change naturalRepresentation (Fin 6) (g * p * g⁻¹)
        (naturalRepresentation (Fin 6) g v) =
        naturalRepresentation (Fin 6) g (naturalRepresentation (Fin 6) p v)
      simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel,
        mul_one])).finrank_eq
  exact he.trans finrank_representative
end Representation.RankTwo.Imprimitive.AlternatingSixTensor
