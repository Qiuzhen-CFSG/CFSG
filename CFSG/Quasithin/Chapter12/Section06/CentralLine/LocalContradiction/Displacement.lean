module
public import Theory.Representation.BinaryPermutation.FiveLowRank
public import CFSG.Quasithin.Chapter12.Section06.Setup
public import Theory.ElementaryAbelian.BinaryRankDifference

/-!
# The marked A₅ displacement obstruction in Lemma 12.6.23

A nonidentity even five-point permutation cannot act with displacement rank
at most one on the binary core: the existing rank-one classification would
make it a transposition. An injective equivariant copy of this core in the
actual conjugation module transfers the bound to that module. In particular
this uses the same ambient actor on both sides of the comparison.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 12.6.23, printed p.830.
-/

public section
namespace CFSG.Quasithin.Chapter12.Section06.CentralLine.LocalContradiction
open Subgroup BinaryPermutation
open scoped IsMulCommutative
variable {G : Type*} [Group G]

private theorem alternating_core_displacement (a : alternatingGroup (Fin 5)) (ha : a ≠ 1) :
    2 ≤ Module.finrank (ZMod 2)
      (coreRepresentation (Fin 5) a.val - LinearMap.id).range := by
  by_contra! hsmall
  rcases FiveLowRank.low_rank a.val (by omega) with hid | ⟨i, j, hij, he⟩
  · exact ha (Subtype.ext hid)
  · have hs := a.property
    rw [Equiv.Perm.mem_alternatingGroup, he, Equiv.Perm.sign_swap hij] at hs
    exact (by decide : (-1 : ℤˣ) ≠ 1) hs

private theorem displacement_le_of_embedding
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) G W) (a : G) (b : alternatingGroup (Fin 5))
    (j : core (Fin 5) →ₗ[ZMod 2] W) (hj : Function.Injective j)
    (heq : ∀ v, j (coreRepresentation (Fin 5) b.val v) = ρ a (j v)) :
    Module.finrank (ZMod 2) (coreRepresentation (Fin 5) b.val - LinearMap.id).range ≤
      Module.finrank (ZMod 2) (ρ a - LinearMap.id).range := by
  let f : (coreRepresentation (Fin 5) b.val - LinearMap.id).range →ₗ[ZMod 2]
      (ρ a - LinearMap.id).range :=
    { toFun := fun v => ⟨j v, by
        obtain ⟨u, hu⟩ := v.property
        refine ⟨j u, ?_⟩
        change ρ a (j u) - j u = j v
        rw [← heq, ← map_sub]
        exact congrArg j hu⟩
      map_add' := fun x y => Subtype.ext (j.map_add x y)
      map_smul' := fun c x => Subtype.ext (j.map_smul c x) }
  exact LinearMap.finrank_le_finrank_of_injective (f := f)
    (fun x y h => Subtype.ext (hj (congrArg Subtype.val h : j x = j y)))

/-- Relative centralizer corank is the dimension of the literal fixed-space quotient. -/
theorem fixed_quotient_finrank [Finite G] {A U : Subgroup G}
    [IsElementaryAbelian 2 U] (hn : A ≤ normalizer (U : Set G)) :
    Module.finrank (ZMod 2) (Vhat A U hn) =
      Nat.log 2 ((centralizer (A : Set G)).relIndex U) := by
  let e : (fixedSeed A U hn).toSubmodule ≃ (ZV A U : Subgroup G) :=
    { toFun := fun v => ⟨v.val.toMul, (mem_fixedSeed_iff A U hn v.val).mp v.property⟩
      invFun := fun v => ⟨Additive.ofMul ⟨v, v.property.1⟩,
        (mem_fixedSeed_iff A U hn _).mpr v.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hU : Nat.card U = 2 ^ Module.finrank (ZMod 2) (Additive U) := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive U)
    change Nat.card U = _ at h
    simpa only [Nat.card_zmod] using h
  have hC : Nat.card (ZV A U) =
      2 ^ Module.finrank (ZMod 2) (fixedSeed A U hn).toSubmodule := by
    rw [← Nat.card_congr e]
    simpa only [Nat.card_zmod] using (Module.natCard_eq_pow_finrank
      (K := ZMod 2) (V := (fixedSeed A U hn).toSubmodule))
  have hd := Submodule.finrank_quotient_add_finrank (fixedSeed A U hn).toSubmodule
  have he := log_card_sub_log_card_eq_log_relIndex U (ZV A U) inf_le_left
  rw [hU, hC, Nat.log_pow Nat.one_lt_two, Nat.log_pow Nat.one_lt_two,
    ZV, inf_relIndex_left] at he
  change Module.finrank (ZMod 2) (Vhat A U hn) + _ = _ at hd
  omega

/-- Every element of A has displacement bounded by the corank of C_U(A).
The action is still conjugation by the original ambient element a. -/
theorem conjugation_displacement_le_centralizer_corank [Finite G]
    {H A U : Subgroup G} [IsElementaryAbelian 2 U]
    (hn : H ≤ normalizer (U : Set G)) (hAH : A ≤ H)
    (a : H) (ha : (a : G) ∈ A) :
    Module.finrank (ZMod 2) (seedRepresentation H U hn a - LinearMap.id).range ≤
      Nat.log 2 ((centralizer (A : Set G)).relIndex U) := by
  have hfix : (fixedSeed A U (hAH.trans hn)).toSubmodule ≤
      (seedRepresentation H U hn a - LinearMap.id).ker := by
    intro v hv
    change seedRepresentation H U hn a v - v = 0
    apply sub_eq_zero.mpr
    change v ∈ (seedRepresentation A U (hAH.trans hn)).invariants at hv
    rw [Representation.mem_invariants] at hv
    exact hv (⟨a, ha⟩ : A)
  have hdim := Submodule.finrank_mono hfix
  have hnull := LinearMap.finrank_range_add_finrank_ker
    (seedRepresentation H U hn a - LinearMap.id)
  have hquot := Submodule.finrank_quotient_add_finrank
    (fixedSeed A U (hAH.trans hn)).toSubmodule
  have he := fixed_quotient_finrank (hAH.trans hn)
  change Module.finrank (ZMod 2) (Vhat A U (hAH.trans hn)) + _ = _ at hquot
  omega

/-- The source comparison on the actual ambient conjugation module U.
The marking is an injective copy of an A₅ summand, not a group-family tag. -/
theorem conjugation_displacement_ge_two [Finite G]
    {H U : Subgroup G} [IsElementaryAbelian 2 U]
    (hn : H ≤ normalizer (U : Set G)) (α : H →* alternatingGroup (Fin 5))
    (j : core (Fin 5) →ₗ[ZMod 2] Additive U) (hj : Function.Injective j)
    (heq : ∀ (h : H) v,
      j (coreRepresentation (Fin 5) (α h).val v) = seedRepresentation H U hn h (j v))
    (a : H) (ha : α a ≠ 1) :
    2 ≤ Module.finrank (ZMod 2) (seedRepresentation H U hn a - LinearMap.id).range :=
  (alternating_core_displacement (α a) ha).trans
    (displacement_le_of_embedding (seedRepresentation H U hn) a (α a) j hj (heq a))

/-- The final local comparison: an index-two fixed subgroup is impossible
for the same actor with nontrivial image on a marked A₅ summand. Only this
actor must be in A₅: the full local quotient may be S₅. -/
theorem centralizer_index_ne_two [Finite G]
    {H A U : Subgroup G} [IsElementaryAbelian 2 U]
    (hn : H ≤ normalizer (U : Set G)) (hAH : A ≤ H)
    (a : H) (ha : (a : G) ∈ A)
    (b : alternatingGroup (Fin 5)) (hb : b ≠ 1)
    (j : core (Fin 5) →ₗ[ZMod 2] Additive U) (hj : Function.Injective j)
    (heq : ∀ v, j (coreRepresentation (Fin 5) b.val v) =
      seedRepresentation H U hn a (j v)) :
    (centralizer (A : Set G)).relIndex U ≠ 2 := by
  intro hindex
  have hlo := (alternating_core_displacement b hb).trans
    (displacement_le_of_embedding (seedRepresentation H U hn) a b j hj heq)
  have hhi := conjugation_displacement_le_centralizer_corank hn hAH a ha
  rw [hindex] at hhi
  norm_num at hhi
  omega

end CFSG.Quasithin.Chapter12.Section06.CentralLine.LocalContradiction
