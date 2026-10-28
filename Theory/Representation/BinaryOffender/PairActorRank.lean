module
public import Theory.Representation.BinaryOffender.SquarePreserving
public import Theory.SpecificGroups.PSL2.BinaryAutomorphismRank
public import Theory.GroupTheory.PrimeRankProduct

/-!
# The full elementary actor on two irreducible normal factors

Conjugation on the two factors together is faithful on every elementary
binary actor: its common kernel centralizes the irreducible join, so binary
Schur's lemma makes that kernel trivial. Both projections may have nonzero
kernels. The product automorphism rank bounds the original entire actor.

For the preserving normalizer of an SL₂(2ⁿ) square this gives rank at most 2n.
The Chapter D Hermitian multiplicity argument uses that full-actor bound.
Source: Aschbacher--Smith D.3.7, printed pp.198--199, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace Representation.BinaryIrreducibleCentralizer
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]

omit [Finite G] in
/-- Both conjugation maps together retain the entire elementary actor. -/
theorem pair_elementary_conjugation_injective
    (ρ : Representation (ZMod 2) G V) (L K : Subgroup G) [L.Normal] [K.Normal]
    [IsIrreducible (ρ.comp (L ⊔ K).subtype)] (hf : Function.Injective ρ)
    (A : Subgroup G) [IsElementaryAbelian 2 A] :
    Function.Injective (((MulAut.conjNormal : G →* MulAut L).prod
      (MulAut.conjNormal : G →* MulAut K)).comp A.subtype) := by
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  apply Subtype.ext
  apply centralizing_square_one_eq_one ρ (L ⊔ K) hf
    (elemPow_eq_one_of_isElementaryAbelian a.val a.property)
  have hL : a.val ∈ centralizer (L : Set G) := by
    rw [←MulAut.conjNormal_ker_eq_centralizer]
    exact congrArg Prod.fst ha
  have hK : a.val ∈ centralizer (K : Set G) := by
    rw [←MulAut.conjNormal_ker_eq_centralizer]
    exact congrArg Prod.snd ha
  have hl : L ≤ centralizer ({a.val} : Set G) := by
    intro l hl z hz
    simpa only [Set.mem_singleton_iff.mp hz] using (hL l hl).symm
  have hk : K ≤ centralizer ({a.val} : Set G) := by
    intro k hk z hz
    simpa only [Set.mem_singleton_iff.mp hz] using (hK k hk).symm
  intro g hg
  exact (sup_le hl hk hg a.val rfl).symm

/-- Bound the entire actor by the sum of the two automorphism ranks. -/
theorem pair_elementary_rank_le
    (ρ : Representation (ZMod 2) G V) (L K : Subgroup G) [L.Normal] [K.Normal]
    [IsIrreducible (ρ.comp (L ⊔ K).subtype)] (hf : Function.Injective ρ)
    (A : Subgroup G) [IsElementaryAbelian 2 A] :
    rank A ≤ primeRank 2 (MulAut L) + primeRank 2 (MulAut K) := by
  let f := ((MulAut.conjNormal : G →* MulAut L).prod
    (MulAut.conjNormal : G →* MulAut K)).comp A.subtype
  have hfi := pair_elementary_conjugation_injective ρ L K hf A
  let : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hc := (primeRank_le_iff_elementary_card_le (MulAut L × MulAut K)).mp
    le_rfl f.range (inferInstance : IsElementaryAbelian 2 f.range)
  rw [←Nat.card_congr (MonoidHom.ofInjective hfi).toEquiv,primeRank_prod_eq_add] at hc
  have hh := Nat.log_mono_right (b := 2) hc
  simpa only [rank,Nat.log_pow (by decide : 1 < 2)] using hh
end Representation.BinaryIrreducibleCentralizer

open scoped MatrixGroups
namespace Representation.BinaryOffender.SquarePreserving
variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- Neither factor need detect the full actor for the bound 2n. -/
theorem even_elementary_rank_le
    (σ : Representation (ZMod 2) (SL(2,F) × SL(2,F)) V)
    (hi : σ.IsIrreducible) (hf : Function.Injective σ)
    (n : ℕ) (hn : 2 ≤ n) (hF : Nat.card F=2^n)
    (A : Subgroup (group σ)) [IsElementaryAbelian 2 A] : rank A ≤ 2*n := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective
    (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  let : IsIrreducible ((action σ).comp (left σ ⊔ right σ).subtype) :=
    pair_irreducible σ hi hf
  have hh := BinaryIrreducibleCentralizer.pair_elementary_rank_le
    (action σ) (left σ) (right σ) (action_faithful σ) A
  rw [←primeRank_equiv 2 (MulAut.congr (leftEquiv σ hf)),
    ←primeRank_equiv 2 (MulAut.congr (rightEquiv σ hf))] at hh
  have hb := Theory.PSL2.BinaryAutomorphismRank.sl2_automorphism_two_rank_le hn hF
  omega

omit [Finite F] [CharP F 2] [FiniteDimensional (ZMod 2) V] in
/-- The common normalizer of the two factor images normalizes their full image. -/
theorem group_le_linearNormalizer
    (σ : Representation (ZMod 2) (SL(2,F) × SL(2,F)) V) :
    group σ ≤ linearNormalizer σ := by
  have htop : (⊤ : Subgroup SL(2,F)).prod (⊥ : Subgroup SL(2,F)) ⊔
      (⊥ : Subgroup SL(2,F)).prod (⊤ : Subgroup SL(2,F)) = ⊤ := by
    apply top_unique
    rintro ⟨x,y⟩ _
    rw [show (x,y) = (x,1) * (1,y) by simp]
    exact Subgroup.mul_mem _ (mem_sup_left ⟨mem_top _,rfl⟩)
      (mem_sup_right ⟨rfl,mem_top _⟩)
  have hgen : leftImage σ ⊔ rightImage σ = actionImage σ := by
    rw [leftImage,rightImage,←Subgroup.map_sup,htop,←MonoidHom.range_eq_map]
    rfl
  have h := normalizer_inf_normalizer_le_normalizer_sup (leftImage σ) (rightImage σ)
  rw [hgen] at h
  exact h

/-- Inclusion preserves the original linear operator exactly. -/
@[expose] def toNormalizer
    (σ : Representation (ZMod 2) (SL(2,F) × SL(2,F)) V) :
    group σ →* linearNormalizer σ := inclusion (group_le_linearNormalizer σ)
end Representation.BinaryOffender.SquarePreserving
