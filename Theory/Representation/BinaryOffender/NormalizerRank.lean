module

public import Theory.Representation.BinaryOffender.CentralKernelImage
public import Theory.Representation.BinaryIrreducibleRank
/-!
# Involutions in an FF linear normalizer

Schur's lemma excludes centralizing involutions in the full linear normalizer
of an irreducible binary action. Consequently each elementary abelian
2-subgroup embeds by conjugation in the automorphism group of the actual
image. An FF offender therefore contains an involution whose fixed codimension
is at most that automorphism group's two-rank.

These are intrinsic reductions for the full normalizer used in
Aschbacher–Smith B.1.13, printed p.73. They apply without identifying its
generalized Fitting subgroup and without a classification hypothesis.
-/

public section
open Subgroup
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Conjugation on the actual image is faithful on elementary two-subgroups. -/
theorem normalizer_elementary_conjugation_injective (hi : ρ.IsIrreducible)
    (E : Subgroup (linearNormalizer ρ)) [IsElementaryAbelian 2 E] :
    Function.Injective ((actionImage ρ).normalizerMonoidHom.comp E.subtype) := by
  let τ : Representation (ZMod 2) (Module.End (ZMod 2) V)ˣ V := Units.coeHom _
  let : Representation.IsIrreducible (τ.comp (actionImage ρ).subtype) := imageRepresentation_isIrreducible ρ hi
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro e he
  apply Subtype.ext
  apply Subtype.ext
  apply BinaryIrreducibleCentralizer.centralizing_square_one_eq_one τ (actionImage ρ)
    (fun _ _ h => Units.ext h)
  · have h2 : (e : linearNormalizer ρ) ^ 2 = 1 :=
      elemPow_eq_one_of_isElementaryAbelian (e : linearNormalizer ρ) e.property
    exact congrArg (fun x : linearNormalizer ρ => x.val) h2
  · change (e : linearNormalizer ρ) ∈ (actionImage ρ).normalizerMonoidHom.ker at he
    rw [Subgroup.normalizerMonoidHom_ker] at he
    exact he


/-- Bound the two-rank of the full normalizer, allowing a nonfaithful original action. -/
theorem primeRank_linearNormalizer_le [FiniteDimensional (ZMod 2) V]
    (hi : ρ.IsIrreducible) :
    primeRank 2 (linearNormalizer ρ) ≤ primeRank 2 (MulAut (actionImage ρ)) := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective
    (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  apply (primeRank_le_iff_elementary_card_le (linearNormalizer ρ)).mpr
  intro E hE
  let : IsElementaryAbelian 2 E := hE
  let f := (actionImage ρ).normalizerMonoidHom.comp E.subtype
  have hf : Function.Injective f := normalizer_elementary_conjugation_injective ρ hi E
  have he : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hc := (primeRank_le_iff_elementary_card_le (MulAut (actionImage ρ))).mp le_rfl f.range he
  exact (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).le.trans hc

/-- An FF normalizer supplies an actual involution of bounded fixed codimension. -/
theorem exists_small_displacement_involution [FiniteDimensional (ZMod 2) V]
    (hi : ρ.IsIrreducible) (hff : IsFFModule (normalizerRepresentation ρ)) :
    ∃ t : linearNormalizer ρ, t ≠ 1 ∧ t ^ 2 = 1 ∧
      fixedCodim (normalizerRepresentation ρ) (zpowers t) ≤
        primeRank 2 (MulAut (actionImage ρ)) := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective
    (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  obtain ⟨A, hA⟩ := hff
  let : IsElementaryAbelian 2 A := hA.1.2
  obtain ⟨t, ht, ht1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1.1
  refine ⟨t, ht1, elemPow_eq_one_of_isElementaryAbelian t ht, ?_⟩
  have hc := (primeRank_le_iff_elementary_card_le (linearNormalizer ρ)).mp
    (primeRank_linearNormalizer_le ρ hi) A hA.1.2
  have hr : rank A ≤ primeRank 2 (MulAut (actionImage ρ)) := by
    have hh := Nat.log_mono_right (b := 2) hc
    simpa only [rank, Nat.log_pow (by decide : 1 < 2)] using hh
  have hle : fixedSpace (normalizerRepresentation ρ) A ≤
      fixedSpace (normalizerRepresentation ρ) (zpowers t) := by
    intro v hv a
    exact hv ⟨a, (zpowers_le.mpr ht) a.property⟩
  have hfix := Submodule.finrank_mono hle
  have ha := fixedCodim_add_finrank (normalizerRepresentation ρ) A
  have ht' := fixedCodim_add_finrank (normalizerRepresentation ρ) (zpowers t)
  have ho := hA.2
  omega
end Representation.BinaryOffender
