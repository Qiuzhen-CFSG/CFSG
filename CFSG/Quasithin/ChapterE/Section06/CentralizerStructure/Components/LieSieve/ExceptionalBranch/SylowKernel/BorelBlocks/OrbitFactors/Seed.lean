module

public import Theory.SpecificGroups.Alternating.FiveBorelOvergroups
public import Theory.GroupTheory.PResidual.Defs
public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour

open Subgroup
open scoped commutatorElement
/-!
# Intrinsic facts about an exceptional Borel seed

The A₅ Sylow-normalizer theorem supplies an actual five-point stabilizer.
In that concrete group the elements with square one form a normal
four-group P. Kernel-checked finite calculations prove that the center is
trivial, that every element is a product of two elements with cube one,
and that [P,K] = P. Thus K is two-perfect and K/P has prime order three.
These facts are transported along the prescribed Borel equivalence.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed p.248; the concrete normalizer identification is provided by
`Theory.SpecificGroups.Alternating.FiveBorelOvergroups`.
-/

namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.ExceptionalBranch.SylowKernel.BorelBlocks.OrbitFactors
private abbrev A5 := alternatingGroup (Fin 5)
private abbrev H (i : Fin 5) := MulAction.stabilizer A5 i
private instance (i : Fin 5) : DecidablePred (· ∈ H i) := fun x => inferInstanceAs (Decidable (x.val i = i))

private def P (i : Fin 5) : Subgroup (H i) where
  carrier := {x | x ^ 2 = 1}
  one_mem' := one_pow 2
  mul_mem' := by
    have hc : ∀ i (x y : H i), x ^ 2 = 1 → y ^ 2 = 1 → (x * y) ^ 2 = 1 := by
      decide +kernel
    exact hc i
  inv_mem' := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [inv_pow, hx, inv_one]
private instance (i : Fin 5) : DecidablePred (· ∈ P i) := fun x => inferInstanceAs (Decidable (x ^ 2 = 1))
private instance (i : Fin 5) : (P i).Normal := by
  constructor
  intro x hx g
  change (g * x * g⁻¹) ^ 2 = 1
  change x ^ 2 = 1 at hx
  simp only [conj_pow, hx, mul_one, mul_inv_cancel]

private theorem P_card (i : Fin 5) : Nat.card (P i) = 4 := by
  rw [Nat.card_eq_fintype_card]
  have hc : ∀ i, Fintype.card (P i) = 4 := by decide +kernel
  exact hc i

private theorem H_card (i : Fin 5) : Nat.card (H i) = 12 := by
  rw [Nat.card_eq_fintype_card]
  have hc : ∀ i, Fintype.card (H i) = 12 := by decide +kernel
  exact hc i

private theorem P_nontrivial (i : Fin 5) : P i ≠ ⊥ := by
  intro he
  have hc := P_card i
  rw [he, Nat.card_eq_fintype_card] at hc
  simp at hc

private theorem P_two (i : Fin 5) : IsPGroup 2 (P i) := by
  apply isPGroup_iff_pow_pow_eq_one.mpr
  intro x
  exact ⟨1, Subtype.ext x.property⟩

private theorem H_center (i : Fin 5) : center (H i) = ⊥ := by
  have hc : ∀ i (a : H i), (∀ b : H i, b * a = a * b) → a = 1 := by
    decide +kernel
  exact eq_bot_iff.mpr fun x hx => mem_bot.mpr (hc i x (mem_center_iff.mp hx))

private theorem H_twoPerfect (i : Fin 5) : IsPPerfect 2 (H i) := by
  have hc : ∀ i (a : H i), ∃ x y : H i, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y = a := by
    decide +kernel
  intro N hn hp
  let := hn
  let q := QuotientGroup.mk' N
  have kill (x : H i) (hx : x ^ 3 = 1) : q x = 1 := by
    have hq3 : (q x) ^ 3 = 1 := by rw [← map_pow, hx, map_one]
    have ho := hp.orderOf_coprime (by decide : Nat.Coprime 2 3) (q x)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes ho
      (dvd_refl _) (orderOf_dvd_of_pow_eq_one hq3))
  apply top_unique
  intro a _
  obtain ⟨x, y, hx, hy, rfl⟩ := hc i a
  apply (QuotientGroup.eq_one_iff _).mp
  change q (x * y) = 1
  rw [map_mul, kill x hx, kill y hy, one_mul]

set_option synthInstance.maxSize 256 in
private theorem P_commutator (i : Fin 5) : ⁅P i, (⊤ : Subgroup (H i))⁆ = P i := by
  apply le_antisymm (commutator_le_left _ _)
  have hc : ∀ i (a : H i), a ^ 2 = 1 →
      ∃ x y : H i, x ^ 2 = 1 ∧ x * y * x⁻¹ * y⁻¹ = a := by decide +kernel
  intro a ha
  obtain ⟨x, y, hx, rfl⟩ := hc i a ha
  exact commutator_mem_commutator hx (mem_top y)

private theorem quotient_card (i : Fin 5) : Nat.card (H i ⧸ P i) = 3 := by
  have hh := (P i).index_mul_card
  rw [P_card, H_card] at hh
  change Nat.card (H i ⧸ P i) * 4 = 12 at hh
  omega


private theorem properties_of_equiv {K : Type*} [Group K] (i : Fin 5) (e : K ≃* H i) :
    IsPPerfect 2 K ∧ center K = ⊥ ∧
      ∃ (R : Subgroup K) (hn : R.Normal),
        letI := hn
        IsSimpleGroup (K ⧸ R) ∧ IsPGroup 2 R ∧ R ≠ ⊥ ∧ ⁅R, (⊤ : Subgroup K)⁆ = R := by
  let R := (P i).comap e.toMonoidHom
  have hm : R.map e.toMonoidHom = P i := map_comap_eq_self_of_surjective e.surjective _
  refine ⟨(H_twoPerfect i).of_surjective e.symm.toMonoidHom e.symm.surjective, ?_,
    R, inferInstance, ?_, (P_two i).comap_of_injective e.toMonoidHom e.injective, ?_, ?_⟩
  · apply eq_bot_iff.mpr
    intro x hx
    have he : e x ∈ center (H i) := by
      apply mem_center_iff.mpr
      intro y
      obtain ⟨z, rfl⟩ := e.surjective y
      simpa only [map_mul] using congrArg e (mem_center_iff.mp hx z)
    rw [H_center, mem_bot] at he
    exact mem_bot.mpr (e.injective (he.trans e.map_one.symm))
  · apply isSimpleGroup_of_prime_card (p := 3)
    change ((P i).comap e.toMonoidHom).index = 3
    rw [index_comap_of_surjective _ e.surjective]
    exact quotient_card i
  · intro he
    apply P_nontrivial i
    rw [← hm, he, Subgroup.map_bot]
  · apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [map_commutator, hm, map_top_of_surjective e.toMonoidHom e.surjective, P_commutator]

/-- The actual A₅ Sylow normalizer satisfies all intrinsic hypotheses of
the short-power factor theorem. -/
public theorem normalizer_seed_properties {K L : Type*} [Group K] [Group L]
    (eL : L ≃* alternatingGroup (Fin 5)) (S : Sylow 2 L)
    (eK : K ≃* normalizer (S : Set L)) :
    IsPPerfect 2 K ∧ center K = ⊥ ∧
      ∃ (R : Subgroup K) (hn : R.Normal),
        letI := hn
        IsSimpleGroup (K ⧸ R) ∧ IsPGroup 2 R ∧ R ≠ ⊥ ∧ ⁅R, (⊤ : Subgroup K)⁆ = R := by
  let : Finite L := Finite.of_equiv (alternatingGroup (Fin 5)) eL.symm.toEquiv
  let T := S.mapSurjective (f := eL.toMonoidHom) eL.surjective
  obtain ⟨i, hi⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer T
  have hm : (normalizer (S : Set L)).map eL.toMonoidHom = H i := by
    change (normalizer ((S : Subgroup L) : Set L)).map eL.toMonoidHom = _
    rw [map_equiv_normalizer_eq]
    exact hi
  exact properties_of_equiv i
    (eK.trans ((eL.subgroupMap (normalizer (S : Set L))).trans (MulEquiv.subgroupCongr hm)))

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.ExceptionalBranch.SylowKernel.BorelBlocks.OrbitFactors
