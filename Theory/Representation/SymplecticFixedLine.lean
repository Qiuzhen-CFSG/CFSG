module
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank.SourceBound
public import Theory.Representation.BinaryIrreducibleCentralizer
public import Theory.Representation.FiniteSchurIntertwiner
public import Theory.Representation.BinaryOffender.Defs
public import Theory.ElementaryAbelian.Quotient

/-!
# Coefficient fields for maximum-rank symplectic actors

A maximum-rank elementary binary actor on a normal faithful irreducible
symplectic component acts by inner automorphisms. Schur's lemma then makes
that actor linear over every commuting coefficient field of the component.
A nonzero fixed line over F₂ forces such a field to have order at most two.

This uses Thompson's inner-action theorem in the concrete Sp₄ model.
The actual G.9 and marked source consumers are in the CFSG library.
-/

@[expose] public noncomputable section
open Subgroup Representation Theory.GroupTheory
namespace Representation.SymplecticFixedLine
variable {D V K : Type*} [Group D] [Finite D]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [Field K] [Finite K] [CharP K 2]

omit [FiniteDimensional (ZMod 2) V] in
/-- A maximum-rank actor on a faithful irreducible normal Sp₄ has inner action. -/
theorem maximal_actor_inner
    (ρ : Representation (ZMod 2) D V) (H A : Subgroup D) [H.Normal]
    [IsIrreducible (ρ.comp H.subtype)] (hf : Function.Injective ρ)
    [IsElementaryAbelian 2 A]
    (e : H ≃* Matrix.symplecticGroup (Fin 2) K)
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (hcard : Nat.card A = 2 ^ (3*n)) :
    A.map (Theory.SpecificGroups.SymplecticFour.ThompsonInner.action H e) ≤
      MulAut.innerSubgroup (Matrix.symplecticGroup (Fin 2) K) := by
  have hbound (E : Subgroup D) (hE : IsElementaryAbelian 2 E) :
      Nat.card E ≤ 2 ^ (3*n) := by
    let := hE
    have hEH : E ≤ normalizer (H : Set D) := by
      rw [normalizer_eq_top_iff.mpr inferInstance]
      exact le_top
    let f := H.normalizerMonoidHom.comp (Subgroup.inclusion hEH)
    have hfi : Function.Injective f :=
      BinaryIrreducibleCentralizer.elementary_conjugation_injective ρ H hf E hEH
    let : IsElementaryAbelian 2 f.range :=
      IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
    have hr : primeRank 2 (MulAut H) ≤ 3*n := by
      rw [primeRank_equiv 2 (MulAut.congr e)]
      exact Theory.SpecificGroups.SymplecticFour.EvenTwoRank.automorphism_rank_le hK hn
    have hb := (primeRank_le_iff_elementary_card_le (MulAut H)).mp hr f.range inferInstance
    exact (Nat.card_congr (MonoidHom.ofInjective hfi).toEquiv).le.trans hb
  obtain ⟨S,hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  apply Theory.SpecificGroups.SymplecticFour.ThompsonInner.maxElementary_action_inner
    H e (by omega) hK S A
  refine ⟨hAS,inferInstance,?_⟩
  intro E _ hE
  rw [hcard]
  exact hbound E hE

omit [Finite D] [Finite K] [CharP K 2] in
/-- Inner actors preserve a larger coefficient field on an irreducible module. -/
theorem coefficient_linear_of_inner
    [Module K V] [SMulCommClass K (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (H A : Subgroup D) [H.Normal]
    [IsIrreducible (ρ.comp H.subtype)]
    (e : H ≃* Matrix.symplecticGroup (Fin 2) K)
    (hH : ∀ (h : H) (c : K) (v : V), ρ h (c • v) = c • ρ h v)
    (ha : A.map (Theory.SpecificGroups.SymplecticFour.ThompsonInner.action H e) ≤
      MulAut.innerSubgroup (Matrix.symplecticGroup (Fin 2) K)) :
    ∀ (a : A) (c : K) (v : V), ρ a (c • v) = c • ρ a v := by
  intro a c v
  let f := Theory.SpecificGroups.SymplecticFour.ThompsonInner.action H e
  obtain ⟨x,hx⟩ := ha (mem_map_of_mem f a.property)
  let h := e.symm x
  have hh : f (h : D) = f a := by
    rw [Theory.SpecificGroups.SymplecticFour.ThompsonInner.action_on_K]
    simpa only [h,e.apply_symm_apply] using hx
  have hc : (h : D)⁻¹ * (a : D) ∈ centralizer (H : Set D) := by
    rw [← Theory.SpecificGroups.SymplecticFour.ThompsonInner.action_ker_eq H e]
    change f ((h : D)⁻¹ * (a : D)) = 1
    rw [map_mul,map_inv,hh,inv_mul_cancel]
  have hlin := FiniteSchurIntertwiner.map_smul (ρ.comp H.subtype) hH
    (ρ ((h : D)⁻¹ * (a : D))) (fun k w => by
      have he := congrArg (fun z : D => ρ z w) (hc k k.property)
      simpa only [map_mul,Module.End.mul_apply,MonoidHom.comp_apply,Subgroup.coe_subtype] using he.symm) c v
  have he := congrArg (ρ (h : D)) hlin
  rw [hH h] at he
  simpa only [← Module.End.mul_apply,← map_mul,mul_inv_cancel_left] using he

/-- Scalar transport along actual natural coordinates. -/
abbrev coordinateModule {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [Module K W] [SMulCommClass K (ZMod 2) W]
    (c : V ≃ₗ[ZMod 2] W) : Module K V := by
  let : SMul K V := ⟨fun a v => c.symm (a • c v)⟩
  exact Function.Injective.module K c.toAddEquiv.toAddMonoidHom c.injective (by
    intro a v
    exact c.apply_symm_apply _)

omit [Finite D] [Finite K] [CharP K 2] in
/-- A nonzero binary fixed line cannot be linear over a field larger than F₂. -/
theorem card_le_two_of_fixed_line
    [Module K V] [SMulCommClass K (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (A : Subgroup D)
    (hlin : ∀ (a : A) (c : K) (v : V), ρ a (c • v) = c • ρ a v)
    (v : V) (hv : v ≠ 0)
    (hfix : BinaryOffender.fixedSpace ρ A = Submodule.span (ZMod 2) {v}) :
    Nat.card K ≤ 2 := by
  have hvfix : v ∈ BinaryOffender.fixedSpace ρ A :=
    hfix ▸ Submodule.mem_span_singleton_self v
  let f : K → BinaryOffender.fixedSpace ρ A := fun c => ⟨c • v,by
    intro a
    change ρ a (c • v) = c • v
    rw [hlin,show ρ a v = v from hvfix a]⟩
  have hfi : Function.Injective f := by
    intro a b he
    exact smul_left_injective K hv (congrArg Subtype.val he)
  let : Finite V := Module.finite_of_finite (ZMod 2)
  have hc := Nat.card_le_card_of_injective f hfi
  rw [hfix,Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := Submodule.span (ZMod 2) {v}),
    finrank_span_singleton hv,Nat.card_zmod,pow_one] at hc
  exact hc

end Representation.SymplecticFixedLine
