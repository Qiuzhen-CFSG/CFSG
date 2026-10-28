module

public import Theory.Representation.BinaryOffender.NormalizerExtension
public import Theory.Representation.BinaryIrreducibleRank
public import Theory.Representation.Quotient
public import Theory.Representation.NormalInvariants
public import Theory.GroupAction.PerfectCentralQuotient

/-!
# Full linear normalizers and perfect central quotients

For a faithful irreducible binary action of a perfect group R, conjugation
embeds every elementary two-subgroup of the full linear normalizer into
Aut(R/Z(R)). Schur's lemma removes the centralizing kernel, and perfectness
removes the kernel of automorphism descent through the center. Thus an FF
offender supplies an actual normalizer involution with displacement bounded
by the two-rank of the automorphism group of any specified central quotient.

The acting group and binary vector space are unchanged. In particular this
does not replace the full normalizer by its subgroup of inner automorphisms.
This is the overgroup reduction for the cross-characteristic argument in
Guralnick–Malle, Classification of 2F-modules I, §2 and Proposition 4.6,
used by Aschbacher–Smith B.1.13 (printed pp.73–74).
-/

public section
namespace Representation.BinaryOffender.PerfectNormalizer
open Subgroup
variable {R S V : Type*} [Group R] [Group S]
  [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) R V) (hf : Function.Injective ρ)

/-- The faithful actor identified with its literal linear image. -/
@[expose] noncomputable def imageEquiv : R ≃* actionImage ρ :=
  MonoidHom.ofInjective (fun _ _ h => hf (congrArg Units.val h))

/-- Conjugation by the full normalizer on the given central quotient. -/
@[expose] noncomputable def quotientAction (e : R ⧸ center R ≃* S) :
    linearNormalizer ρ →* MulAut S :=
  (MulAut.centralQuotientAction e).comp
    ((MulAut.congr (imageEquiv ρ hf).symm).toMonoidHom.comp
      (actionImage ρ).normalizerMonoidHom)

private theorem image_conjugation_injective (hi : ρ.IsIrreducible)
    (A : Subgroup (linearNormalizer ρ)) [IsElementaryAbelian 2 A] :
    Function.Injective ((actionImage ρ).normalizerMonoidHom.comp A.subtype) := by
  let τ : Representation (ZMod 2) (Module.End (ZMod 2) V)ˣ V := Units.coeHom _
  let : IsIrreducible (τ.comp (actionImage ρ).subtype) :=
    (irreducible_comp_surjective_iff (actionHom ρ)
      ρ.asGroupHom.rangeRestrict_surjective (imageRepresentation ρ)).mp hi
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro a ha
  apply Subtype.ext
  apply Subtype.ext
  apply BinaryIrreducibleCentralizer.centralizing_square_one_eq_one τ (actionImage ρ)
    (fun _ _ h => Units.ext h)
  · exact congrArg (fun x : linearNormalizer ρ => x.val)
      (elemPow_eq_one_of_isElementaryAbelian (a : linearNormalizer ρ) a.property)
  · change (a : linearNormalizer ρ) ∈ (actionImage ρ).normalizerMonoidHom.ker at ha
    rw [Subgroup.normalizerMonoidHom_ker] at ha
    exact ha

/-- Elementary two-subgroups act faithfully on the specified central quotient,
including when their elements induce outer automorphisms. -/
theorem quotientAction_injective_on_elementary [Group.IsPerfect R]
    (hi : ρ.IsIrreducible) (e : R ⧸ center R ≃* S)
    (A : Subgroup (linearNormalizer ρ)) [IsElementaryAbelian 2 A] :
    Function.Injective ((quotientAction ρ hf e).comp A.subtype) :=
  (MulAut.centralQuotientAction_injective e).comp
    ((MulAut.congr (imageEquiv ρ hf).symm).injective.comp
      (image_conjugation_injective ρ hi A))

include hf in
/-- The faithful nontrivial irreducible component fixes no vector, when
regarded as the literal subgroup of its full linear normalizer. -/
theorem fixedSpace_image_eq_bot [Nontrivial R] (hi : ρ.IsIrreducible) :
    fixedSpace (normalizerRepresentation ρ)
      ((actionImage ρ).subgroupOf (linearNormalizer ρ)) = ⊥ := by
  let := hi
  have hzero : Representation.invariants (ρ.comp (⊤ : Subgroup R).subtype) = ⊥ := by
    by_contra hn
    have hk := Representation.le_ker_of_normal_invariants_ne_bot ρ (⊤ : Subgroup R) hn
    obtain ⟨r, hr⟩ := exists_ne (1 : R)
    exact hr (hf ((hk (mem_top r)).trans (map_one ρ).symm))
  apply le_bot_iff.mp
  intro v hv
  have hvr : v ∈ Representation.invariants (ρ.comp (⊤ : Subgroup R).subtype) := by
    intro r
    let a : linearNormalizer ρ :=
      ⟨ρ.asGroupHom r, (actionImage ρ).le_normalizer ⟨r, rfl⟩⟩
    exact hv ⟨a, ⟨r, rfl⟩⟩
  simpa only [hzero, Submodule.mem_bot] using hvr

variable [Group.IsPerfect R] [Finite S] [FiniteDimensional (ZMod 2) V]

include hf in
/-- The full normalizer has two-rank at most the automorphism group of R/Z(R). -/
theorem primeRank_le (hi : ρ.IsIrreducible) (e : R ⧸ center R ≃* S) :
    primeRank 2 (linearNormalizer ρ) ≤ primeRank 2 (MulAut S) := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective
    (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  apply (primeRank_le_iff_elementary_card_le (linearNormalizer ρ)).mpr
  intro A hA
  let : IsElementaryAbelian 2 A := hA
  let f := (quotientAction ρ hf e).comp A.subtype
  have hfi : Function.Injective f := quotientAction_injective_on_elementary ρ hf hi e A
  have he : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hc := (primeRank_le_iff_elementary_card_le (MulAut S)).mp le_rfl f.range he
  exact (Nat.card_congr (MonoidHom.ofInjective hfi).toEquiv).le.trans hc

include hf in
/-- An FF offender in the literal full normalizer gives an involution with
displacement bounded by the automorphism rank of the specified simple quotient. -/
theorem exists_small_involution (hi : ρ.IsIrreducible)
    (e : R ⧸ center R ≃* S) (hff : IsFFModule (normalizerRepresentation ρ)) :
    ∃ t : linearNormalizer ρ, t ≠ 1 ∧ t ^ 2 = 1 ∧
      fixedCodim (normalizerRepresentation ρ) (zpowers t) ≤ primeRank 2 (MulAut S) := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective
    (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  obtain ⟨A, hA⟩ := hff
  let : IsElementaryAbelian 2 A := hA.1.2
  obtain ⟨t, ht, ht1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1.1
  refine ⟨t, ht1, elemPow_eq_one_of_isElementaryAbelian t ht, ?_⟩
  have hc := (primeRank_le_iff_elementary_card_le (linearNormalizer ρ)).mp
    (primeRank_le ρ hf hi e) A hA.1.2
  have hr : rank A ≤ primeRank 2 (MulAut S) := by
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

end Representation.BinaryOffender.PerfectNormalizer
