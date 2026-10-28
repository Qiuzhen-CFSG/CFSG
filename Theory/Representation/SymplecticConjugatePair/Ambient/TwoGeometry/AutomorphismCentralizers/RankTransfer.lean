module

public import Theory.GroupTheory.PrimeRankHom
public import Theory.Quasithin.Rank
public import Theory.GroupAction.AutomorphismFixedResidualTransport
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Centralizer rank from the fixed group

For a centerless finite group, the kernel of the map from an automorphism
centralizer to the outer group embeds in the actual fixed subgroup. When the
outer group is cyclic its contribution to two-rank is at most one.

This is the intrinsic rank transfer used in Aschbacher–Smith H.7, printed
p.389. No fixed-group identification or descent hypothesis enters this step.
-/

public noncomputable section

open Subgroup Theory.GroupTheory
namespace SymplecticConjugatePair.Ambient.AutomorphismCentralizers

variable {G : Type*} [Group G] [Finite G]

/-- The actual inner intersection of the centralizer embeds in the fixed
subgroup; a cyclic outer quotient contributes at most one to two-rank. -/
theorem centralizer_rank_le_fixed_add_one
    (hi : Function.Injective (MulAut.conj : G →* MulAut G))
    [IsCyclic (MulAut.Outer G)] (a : MulAut G) :
    primeRank 2 (centralizer ({a} : Set (MulAut G))) ≤
      primeRank 2 a.fixedSubgroup + 1 := by
  let C := centralizer ({a} : Set (MulAut G))
  let e : G ≃* MulAut.innerSubgroup G := MonoidHom.ofInjective hi
  let π : C →* MulAut.Outer G :=
    (QuotientGroup.mk' (MulAut.innerSubgroup G)).comp C.subtype
  let j : π.ker →* MulAut.innerSubgroup G := {
    toFun x := ⟨x.val.val, (QuotientGroup.eq_one_iff _).mp x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  let k : π.ker →* G := e.symm.toMonoidHom.comp j
  have hk (x : π.ker) : MulAut.conj (k x) = x.val.val :=
    congrArg Subtype.val (e.apply_symm_apply (j x))
  let f : π.ker →* a.fixedSubgroup := k.codRestrict _ (fun x => by
    rw [MulAut.mem_fixedSubgroup]
    apply hi
    have he : a * MulAut.conj (k x) * a⁻¹ = MulAut.conj (a (k x)) := by
      ext y
      simp
    rw [← he, hk]
    have hc := mem_centralizer_singleton_iff.mp x.val.property
    rw [← hc, mul_assoc, mul_inv_cancel, mul_one])
  have hf : Function.Injective f := by
    intro x y h
    have hxy := congrArg (fun z : a.fixedSubgroup => MulAut.conj z.val) h
    change MulAut.conj (k x) = MulAut.conj (k y) at hxy
    rw [hk, hk] at hxy
    exact Subtype.ext (Subtype.ext hxy)
  have hker := primeRank_le_of_injective 2 f hf
  have hout : primeRank 2 (MulAut.Outer G) ≤ 1 := by
    let P := Classical.choice (inferInstance : Nonempty (Sylow 2 (MulAut.Outer G)))
    exact P.primeRank_le_one_of_isCyclic inferInstance
  exact (primeRank_le_ker_add π).trans (Nat.add_le_add hker hout)

/-- Conjugate automorphisms have isomorphic fixed groups and equal ranks. -/
theorem fixed_rank_eq_of_isConj {a b : MulAut G} (h : IsConj a b) :
    primeRank 2 a.fixedSubgroup = primeRank 2 b.fixedSubgroup := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have he : ∀ x, c (a x) = b (c x) := by
    intro x
    exact congrArg (fun d : MulAut G => d x) (mul_inv_eq_iff_eq_mul.mp hc)
  exact primeRank_congr 2 (MulAut.fixedSubgroupEquivOfCompatible c a b he)

end SymplecticConjugatePair.Ambient.AutomorphismCentralizers
