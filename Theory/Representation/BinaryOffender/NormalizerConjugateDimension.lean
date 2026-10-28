module

public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.NormalizerRank
public import Theory.Representation.NormalInvariants
public import Theory.GroupTheory.PrimeRankCentralCover

/-!
# Dimension bounds from conjugates in a binary linear normalizer

If a subgroup with no common nonzero fixed vector is generated inside the
closure of finitely many actors, the module injects into the product of the
quotients by their fixed spaces. Its dimension is therefore bounded by the
sum of their fixed codimensions. For conjugate actors these codimensions agree.

An FF full linear normalizer supplies an involution of small fixed codimension.
Combining these observations bounds the dimension by the number of conjugates
times the automorphism two-rank. For a finite quasisimple actor, faithful
central-quotient descent permits the rank to be computed on its actual simple
quotient, including nontrivial central covers.

This is an auxiliary reduction for the representation exclusion in
Aschbacher–Smith B.1.13, printed pp.73–74 / PDF pp.84–85 of
`refs/quasithin.pdf`. The conjugate-generation and numerical rank hypotheses
remain explicit; this module asserts no sporadic module classification.
-/

public section
open Subgroup
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Embed in the product of the quotients by the generating actors' fixed spaces. -/
theorem finrank_le_sum_fixedCodim_of_generators
    (ρ : Representation (ZMod 2) G V) (H : Subgroup G)
    (hfix : fixedSpace ρ H = ⊥) {ι : Type*} [Fintype ι] (a : ι → G)
    (hgen : H ≤ closure (Set.range a)) :
    Module.finrank (ZMod 2) V ≤ ∑ i, fixedCodim ρ (zpowers (a i)) := by
  let f := LinearMap.pi (fun i => (fixedSpace ρ (zpowers (a i))).mkQ)
  have hinj : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply le_bot_iff.mp
    intro v hv
    have ha (i : ι) : ρ (a i) v = v := by
      apply (mem_fixedSpace_zpowers_iff ρ (a i) v).mp
      apply (Submodule.Quotient.mk_eq_zero _).mp
      exact congrFun hv i
    have hall (g : G) (hg : g ∈ closure (Set.range a)) : ρ g v = v := by
      induction hg using Subgroup.closure_induction with
      | mem x hx => obtain ⟨i, rfl⟩ := hx; exact ha i
      | one => simp
      | mul x y _ _ hx hy => simp only [map_mul, Module.End.mul_apply, hy, hx]
      | inv x _ hx =>
        have he := congrArg (ρ x⁻¹) hx
        simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
          map_one, Module.End.one_apply] using he.symm
    have hvfix : v ∈ fixedSpace ρ H := fun g => hall g (hgen g.property)
    simpa only [hfix] using hvfix
  have hd := LinearMap.finrank_le_finrank_of_injective hinj
  simpa only [Module.finrank_pi_fintype, fixedCodim] using hd

/-- Conjugate actors all contribute the same fixed codimension. -/
theorem finrank_le_mul_fixedCodim_of_conjugates
    (ρ : Representation (ZMod 2) G V) (H : Subgroup G)
    (hfix : fixedSpace ρ H = ⊥) (t : G) {n : ℕ} (c : Fin n → G)
    (hgen : H ≤ closure (Set.range fun i => c i * t * (c i)⁻¹)) :
    Module.finrank (ZMod 2) V ≤ n * fixedCodim ρ (zpowers t) := by
  simpa only [fixedCodim_zpowers_conj, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] using
      finrank_le_sum_fixedCodim_of_generators ρ H hfix
        (fun i => c i * t * (c i)⁻¹) hgen

omit [FiniteDimensional (ZMod 2) V] in
/-- A faithful irreducible action of a nontrivial group has no common fixed vector. -/
theorem invariants_eq_bot_of_faithful_irreducible [Nontrivial G]
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (hi : ρ.IsIrreducible) : ρ.invariants = ⊥ := by
  let := hi
  by_contra hn
  have hn' : Representation.invariants (ρ.comp (⊤ : Subgroup G).subtype) ≠ ⊥ := by
    intro hh
    apply hn
    have he : ρ.invariants = Representation.invariants (ρ.comp (⊤ : Subgroup G).subtype) := by
      ext v
      exact ⟨fun h x => h x, fun h x => h ⟨x, mem_top x⟩⟩
    exact he.trans hh
  have hk := Representation.le_ker_of_normal_invariants_ne_bot ρ ⊤ hn'
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  exact hg (hf ((MonoidHom.mem_ker.mp (hk (mem_top g))).trans (map_one ρ).symm))

/-- The number of conjugates is measured in the actual linear group. -/
@[expose] def NormalizerConjugateGenerationBound
    (ρ : Representation (ZMod 2) G V) (n : ℕ) : Prop :=
  ∀ t : linearNormalizer ρ, t ≠ 1 → t ^ 2 = 1 →
    ∃ c : Fin n → (Module.End (ZMod 2) V)ˣ,
      actionImage ρ ≤ closure (Set.range fun i => c i * t.val * (c i)⁻¹)

/-- An FF normalizer and a conjugate-generation bound give a dimension bound. -/
theorem finrank_le_of_ff_linear_conjugate_generation [Nontrivial G]
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (hi : ρ.IsIrreducible) {n r : ℕ}
    (hgen : NormalizerConjugateGenerationBound ρ n)
    (hr : primeRank 2 (MulAut (actionImage ρ)) ≤ r)
    (hff : IsFFModule (normalizerRepresentation ρ)) :
    Module.finrank (ZMod 2) V ≤ n * r := by
  let τ : Representation (ZMod 2) (Module.End (ZMod 2) V)ˣ V := Units.coeHom _
  have hfix : fixedSpace τ (actionImage ρ) = ⊥ := by
    have he : fixedSpace τ (actionImage ρ) = ρ.invariants := by
      ext v
      constructor
      · intro h g
        exact h ⟨ρ.asGroupHom g, ⟨g, rfl⟩⟩
      · rintro h ⟨_, g, rfl⟩
        exact h g
    rw [he, invariants_eq_bot_of_faithful_irreducible ρ hf hi]
  obtain ⟨t, ht, ht2, hd⟩ := exists_small_displacement_involution ρ hi hff
  obtain ⟨c, hc⟩ := hgen t ht ht2
  have hdim := finrank_le_mul_fixedCodim_of_conjugates τ (actionImage ρ) hfix t.val c hc
  have he : fixedCodim τ (zpowers t.val) =
      fixedCodim (normalizerRepresentation ρ) (zpowers t) := by
    rw [fixedCodim_zpowers_eq_displacement_rank, fixedCodim_zpowers_eq_displacement_rank]
    rfl
  rw [he] at hdim
  exact hdim.trans (Nat.mul_le_mul_left n (hd.trans hr))

/-- The rank bound may be supplied on the actual simple central quotient. -/
theorem finrank_le_of_ff_normalizer_central_quotient
    [Finite G] [Theory.GroupTheory.IsQuasisimple G]
    {S : Type*} [Group S]
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (hi : ρ.IsIrreducible) (e : G ⧸ center G ≃* S) {n r : ℕ}
    (hgen : NormalizerConjugateGenerationBound ρ n)
    (hr : primeRank 2 (MulAut S) ≤ r)
    (hff : IsFFModule (normalizerRepresentation ρ)) :
    Module.finrank (ZMod 2) V ≤ n * r := by
  let : Finite S := Finite.of_surjective e e.surjective
  have hk : ρ.ker ≤ center G := by
    rw [(MonoidHom.ker_eq_bot_iff ρ).mpr hf]
    exact bot_le
  let := actionImage_quasisimple_of_central_kernel ρ hk
  let : IsSimpleGroup (G ⧸ center G) := Theory.GroupTheory.IsQuasisimple.simple
  let : Nontrivial G := (QuotientGroup.mk'_surjective (center G)).nontrivial
  let e' := (simpleQuotientEquivImage ρ hk).symm.trans e
  have hb := Theory.GroupTheory.automorphism_primeRank_le_quotient_center
    (E := actionImage ρ) 2
  rw [Theory.GroupTheory.primeRank_equiv 2 (MulAut.congr e')] at hb
  exact finrank_le_of_ff_linear_conjugate_generation ρ hf hi hgen (hb.trans hr) hff

end Representation.BinaryOffender
