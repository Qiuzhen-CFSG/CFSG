module

public import Theory.Representation.BinaryOffender.NormalizerRank
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Theory.Representation.FixedSpaceCodimension
public import Theory.Representation.NormalInvariants
public import Theory.GroupTheory.PrimeRankCentralCover

/-!
# Degree bounds from conjugates in a full linear normalizer

The fixed spaces of conjugate cyclic subgroups have equal codimension. If a
finite family of them generates a subgroup containing an actor with no fixed
vectors, the codimension of their intersection bounds the module dimension.
For a faithful irreducible binary actor, the actor inside its full linear
normalizer has no fixed vectors. The small-displacement involution supplied by
an FF offender therefore gives a degree bound from any conjugate-generation
bound.

The final two lemmas descend the automorphism rank through an arbitrary
quasisimple central cover to an actual specified quotient. In particular they
do not replace the full linear normalizer with an almost simple group.

Source application: Aschbacher–Smith, B.1.13, printed pp.73–74 of the combined
1 March 2004 manuscript. These are general reductions, not the sporadic
representation bounds cited there from Guralnick–Malle, *Classification of
2F-modules, II*, Table 2, DOI 10.1515/9783110198126.117.
-/

public section
open Subgroup
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- The literal action image, regarded as a subgroup of its full normalizer. -/
@[expose] def normalizerActor (ρ : Representation (ZMod 2) G V) :
    Subgroup (linearNormalizer ρ) :=
  (actionImage ρ).subgroupOf (linearNormalizer ρ)

/-- A faithful irreducible nontrivial actor has no fixed vectors in the normalizer action. -/
theorem fixedSpace_normalizerActor_eq_bot [Nontrivial G]
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (hi : ρ.IsIrreducible) :
    fixedSpace (normalizerRepresentation ρ) (normalizerActor ρ) = ⊥ := by
  let := hi
  have hzero : fixedSpace ρ ⊤ = ⊥ := by
    by_contra hn
    have hk := ρ.le_ker_of_normal_invariants_ne_bot ⊤ hn
    obtain ⟨g, hg⟩ := exists_ne (1 : G)
    apply hg
    apply hf
    exact (MonoidHom.mem_ker.mp (hk (mem_top g))).trans (map_one ρ).symm
  apply le_bot_iff.mp
  intro v hv
  apply hzero.le
  intro g
  let a : linearNormalizer ρ :=
    ⟨ρ.asGroupHom g, (actionImage ρ).le_normalizer ⟨g, rfl⟩⟩
  exact hv ⟨a, ⟨g, rfl⟩⟩

/-- Conjugate generation bounds dimension by the number of conjugates times displacement. -/
theorem finrank_le_card_mul_fixedCodim_of_conjugates
    [FiniteDimensional (ZMod 2) V] {ι : Type*} [Fintype ι]
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G)
    (hfix : fixedSpace ρ L = ⊥) (t : G) (g : ι → G)
    (hgen : L ≤ ⨆ i, (zpowers t).map (MulAut.conj (g i)).toMonoidHom) :
    Module.finrank (ZMod 2) V ≤ Fintype.card ι * fixedCodim ρ (zpowers t) := by
  let X (i : ι) := (zpowers t).map (MulAut.conj (g i)).toMonoidHom
  have hz : fixedSpace ρ (⨆ i, X i) = ⊥ := by
    apply le_bot_iff.mp
    rw [← hfix]
    exact ρ.invariants_comp_subtype_antitone hgen
  have he : fixedSpace ρ (⨆ i, X i) = ⨅ i, fixedSpace ρ (X i) :=
    ρ.invariants_comp_iSup X
  have hd := Submodule.finrank_quotient_iInf_le_sum (fun i => fixedSpace ρ (X i))
  rw [← he, hz, Submodule.finrank_quotient] at hd
  simp only [finrank_bot, Nat.sub_zero] at hd
  change Module.finrank (ZMod 2) V ≤ ∑ i, fixedCodim ρ (X i) at hd
  simpa only [X, fixedCodim_map_conj, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Nat.cast_id] using hd

/-- An FF full normalizer turns a conjugate-generation bound into a degree bound. -/
theorem finrank_le_of_ff_normalizer_conjugates [Nontrivial G]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (hi : ρ.IsIrreducible) (k r : ℕ)
    (hr : primeRank 2 (MulAut (actionImage ρ)) ≤ r)
    (hgen : ∀ t : linearNormalizer ρ, t ≠ 1 → t ^ 2 = 1 →
      ∃ g : Fin k → linearNormalizer ρ,
        normalizerActor ρ ≤ ⨆ i, (zpowers t).map (MulAut.conj (g i)).toMonoidHom)
    (hff : IsFFModule (normalizerRepresentation ρ)) :
    Module.finrank (ZMod 2) V ≤ k * r := by
  obtain ⟨t, ht, ht2, hd⟩ := exists_small_displacement_involution ρ hi hff
  obtain ⟨g, hg⟩ := hgen t ht ht2
  have hb := finrank_le_card_mul_fixedCodim_of_conjugates
    (normalizerRepresentation ρ) (normalizerActor ρ)
    (fixedSpace_normalizerActor_eq_bot ρ hf hi) t g hg
  have hb' : Module.finrank (ZMod 2) V ≤ k *
      fixedCodim (normalizerRepresentation ρ) (zpowers t) := by
    simpa only [Fintype.card_fin] using hb
  exact hb'.trans (Nat.mul_le_mul_left k (hd.trans hr))
end Representation.BinaryOffender

namespace Representation.BinaryOffender
open Theory.GroupTheory
variable {G V S : Type*} [Group G] [Finite G] [IsQuasisimple G] [Group S]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- The automorphism rank of a central-kernel image is bounded by that of its named quotient. -/
theorem primeRank_actionImage_le_central_quotient
    (ρ : Representation (ZMod 2) G V) (hk : ρ.ker ≤ center G)
    (e : G ⧸ center G ≃* S) :
    primeRank 2 (MulAut (actionImage ρ)) ≤ primeRank 2 (MulAut S) := by
  let : Finite S := Finite.of_surjective e e.surjective
  let := actionImage_quasisimple_of_central_kernel ρ hk
  let e' := (simpleQuotientEquivImage ρ hk).symm.trans e
  have hr := automorphism_primeRank_le_quotient_center (E := actionImage ρ) 2
  rw [primeRank_equiv 2 (MulAut.congr e')] at hr
  exact hr

/-- A strict displacement gap excludes FF, with all model bounds still explicit. -/
theorem not_ff_of_central_quotient_displacement
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hi : ρ.IsIrreducible)
    (hk : ρ.ker ≤ center G) (e : G ⧸ center G ≃* S) (r : ℕ)
    (hr : primeRank 2 (MulAut S) ≤ r)
    (hd : ∀ t : linearNormalizer ρ, t ≠ 1 → t ^ 2 = 1 →
      r < fixedCodim (normalizerRepresentation ρ) (zpowers t)) :
    ¬ IsFFModule (normalizerRepresentation ρ) := by
  intro hff
  obtain ⟨t, ht, ht2, hsmall⟩ := exists_small_displacement_involution ρ hi hff
  exact (not_lt_of_ge
    (hsmall.trans ((primeRank_actionImage_le_central_quotient ρ hk e).trans hr)))
      (hd t ht ht2)
end Representation.BinaryOffender
