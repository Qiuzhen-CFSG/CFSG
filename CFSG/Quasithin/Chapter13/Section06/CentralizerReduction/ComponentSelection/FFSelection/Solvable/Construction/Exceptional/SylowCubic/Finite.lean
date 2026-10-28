module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Exceptional.SylowCubic.Reduction
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Structure.Basic
/-!
# A kernel-checked certificate for cubic conjugates

The canonical Sylow subgroup is the graph of the sign action on three points.
Its order and Sylow property follow structurally from the existing order-sixteen
Sylow subgroup of S₆ and the cubic kernel. For each nonidentity six-point cubic
and each nonidentity three-point cubic, one of six fixed Sylow words supplies a
commuting conjugate outside the cyclic subgroup of the original element.

The sole exhaustive certificate uses the 720 permutations on six points and the
six permutations on three points. It is checked by kernel reduction, without
native evaluation.
Source motivation: Aschbacher–Smith, B.5.6(4), B.5.7, printed pp.105–106.
-/

public section
open Subgroup
open CFSG.Quasithin.ChapterB.Offenders.Six
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional.SixPoint
namespace SylowCubicCertificate

private def signLift : ℤˣ →* Equiv.Perm (Fin 3) where
  toFun u := if u = 1 then 1 else Equiv.swap 0 1
  map_one' := by simp
  map_mul' := by decide
private lemma sign_signLift (u : ℤˣ) : Equiv.Perm.sign (signLift u) = u := by revert u; decide

private def lift : Equiv.Perm (Fin 6) →* Actor where
  toFun s := ⟨(s, signLift (Equiv.Perm.sign s)), by
    change Equiv.Perm.sign s = Equiv.Perm.sign (signLift (Equiv.Perm.sign s))
    exact (sign_signLift _).symm⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' s t := by apply Subtype.ext; simp
private lemma lift_injective : Function.Injective lift := fun _ _ h => congrArg firstProjection h

private def canonical : Subgroup Actor := (sylow : Subgroup _).map lift
private lemma card_canonical : Nat.card canonical = 16 := by
  unfold canonical
  rw [← Nat.card_congr ((sylow : Subgroup _).equivMapOfInjective lift lift_injective).toEquiv]
  exact card_sylowCarrier
private lemma card_actor : Nat.card Actor = 2160 := by
  have hs : Function.Surjective firstProjection := fun s => ⟨lift s, rfl⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup firstProjection.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective firstProjection hs).toEquiv,
    show Nat.card firstProjection.ker = 3 from card_cubic,
    Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  norm_num [Nat.factorial]
/-- The lift of the standard order-sixteen subgroup of S₆ to the literal parity actor. -/
private def canonicalSylow : Sylow 2 Actor :=
  (IsPGroup.of_card (show Nat.card canonical = 2 ^ 4 from card_canonical)).toSylow (by
    have h := canonical.card_mul_index
    rw [card_canonical, card_actor] at h
    norm_num at h ⊢
    omega)
private def word (i : Fin 16) : Actor := lift (sylowWords i)
private lemma word_mem (i : Fin 16) : word i ∈ canonicalSylow :=
  ⟨sylowWords i, (mem_sylowCarrier_iff _).mpr ⟨i, rfl⟩, rfl⟩
private def candidate (i : Fin 6) : Fin 16 := ![1, 7, 2, 4, 8, 11] i

private def pairConjugate (i : Fin 6) (s : Equiv.Perm (Fin 6)) (t : Equiv.Perm (Fin 3)) :=
  (word (candidate i)).val * (s, t) * (word (candidate i)).val⁻¹

private lemma finite_certificate : ∀ (s : Equiv.Perm (Fin 6)) (t : Equiv.Perm (Fin 3)),
    s ^ 3 = 1 → t ^ 3 = 1 → t ≠ 1 → s = 1 ∨ ∃ i : Fin 6,
    (s, t) * pairConjugate i s t = pairConjugate i s t * (s, t) ∧
    pairConjugate i s t ≠ (s, t) ∧ pairConjugate i s t ≠ (s, t) ^ 2 := by
  decide +kernel

/-- A canonical Sylow conjugate outside the cyclic subgroup commutes with each
order-three seed outside both coordinate kernels. -/
private lemma canonical_commuting_conjugate (r : Actor) (hthree : r ^ 3 = 1)
    (hfirst : firstProjection r ≠ 1) (hsecond : secondProjection r ≠ 1) :
    ∃ p ∈ canonicalSylow, r * (p * r * p⁻¹) = (p * r * p⁻¹) * r ∧
      p * r * p⁻¹ ≠ r ∧ p * r * p⁻¹ ≠ r ^ 2 := by
  have hs : firstProjection r ^ 3 = 1 := by rw [← map_pow, hthree, map_one]
  have ht : secondProjection r ^ 3 = 1 := by rw [← map_pow, hthree, map_one]
  obtain h | ⟨i, hi, hne, hne2⟩ :=
    finite_certificate (firstProjection r) (secondProjection r) hs ht hsecond
  · exact (hfirst h).elim
  refine ⟨word (candidate i), word_mem _, ?_, ?_, ?_⟩
  · exact Subtype.ext hi
  · intro h
    exact hne (congrArg Subtype.val h)
  · intro h
    exact hne2 (congrArg Subtype.val h)

/-- One Sylow subgroup admits the six-word commuting-conjugate certificate. -/
public theorem exists_sylow_commuting_conjugates : ∃ P : Sylow 2 Actor,
    ∀ r : Actor, r ^ 3 = 1 → firstProjection r ≠ 1 → secondProjection r ≠ 1 →
    ∃ p ∈ P, r * (p * r * p⁻¹) = (p * r * p⁻¹) * r ∧
      p * r * p⁻¹ ≠ r ∧ p * r * p⁻¹ ≠ r ^ 2 :=
  ⟨canonicalSylow, canonical_commuting_conjugate⟩

end SylowCubicCertificate
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional.SixPoint
