module

public import CFSG.Quasithin.Chapter1.Section03.Basic
public import Theory.GroupTheory.CyclicNormalOddQuotient
public import Theory.GroupTheory.PerfectCentralCoverOuter

/-!
# The invariant subgroup in the outer-group inspection

Let N be cyclic and normal in G, and let U be noncyclic with cyclic image
in G/N. The image of U ∩ N in U/Φ(U) is invariant under N_G(U). It is
proper because it is cyclic, and nontrivial because otherwise the cyclic
quotient U/(U ∩ N) would make U/Φ(U), and hence U, cyclic.

The structural condition and the embedding Out(Q) → Out(Q/Z(Q)) then
reduce the first outer-automorphism inspection on printed p.510 to actual
simple-model calculations. No such model calculation is assumed proved here.
Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of 1.3.4.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- The cyclic normal intersection supplies an actual proper nonzero invariant subgroup. -/
theorem exists_invariant_of_cyclic_normal
    (N : Subgroup G) [N.Normal] [IsCyclic N] (U : Subgroup G)
    (hnc : ¬ IsCyclic U) (hc : IsCyclic (U.map (QuotientGroup.mk' N))) :
    ∃ A : Subgroup (U ⧸ frattini U), A ≠ ⊥ ∧ A ≠ ⊤ ∧
      ∀ s : normalizer (U : Set G), ∀ a ∈ A,
        frattiniConjugationAction (normalizer (U : Set G)) U le_rfl s a ∈ A := by
  let f : U →* G ⧸ N := (QuotientGroup.mk' N).comp U.subtype
  let D := f.ker
  let q := QuotientGroup.mk' (frattini U)
  let A := D.map q
  have hD (x : U) : x ∈ D ↔ (x : G) ∈ N := by
    exact QuotientGroup.eq_one_iff (x : G)
  let i : D →* N := (U.subtype.comp D.subtype).codRestrict N
    (fun x => (hD x).mp x.property)
  have hi : Function.Injective i := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : N => (z : G)) hxy
  let : IsCyclic D := isCyclic_of_injective i hi
  let : IsCyclic A := isCyclic_of_surjective (q.subgroupMap D) (q.subgroupMap_surjective D)
  have hfnc := OddInvolutionFrattini.noncyclic_frattini_quotient hnc
  have hAb : A ≠ ⊥ := by
    intro hb
    have hker : f.ker ≤ q.ker := by
      exact (Subgroup.map_eq_bot_iff D).mp hb
    let : IsCyclic f.range := by
      change IsCyclic ((QuotientGroup.mk' N).domRestrict U).range
      rwa [MonoidHom.domRestrict_range]
    let : IsCyclic (U ⧸ f.ker) :=
      isCyclic_of_injective (QuotientGroup.quotientKerEquivRange f).toMonoidHom
        (QuotientGroup.quotientKerEquivRange f).injective
    let t : U ⧸ f.ker →* U ⧸ frattini U := QuotientGroup.lift f.ker q hker
    have ht : Function.Surjective t := by
      intro x
      obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (frattini U) x
      exact ⟨QuotientGroup.mk' f.ker u, rfl⟩
    exact hfnc (isCyclic_of_surjective t ht)
  have hAt : A ≠ ⊤ := by
    intro ht
    apply hfnc
    exact isCyclic_of_surjective A.subtype (fun x =>
      ⟨⟨x, ht.symm ▸ mem_top x⟩, rfl⟩)
  refine ⟨A, hAb, hAt, ?_⟩
  rintro s a ⟨x, hx, rfl⟩
  let _ := conjMulDistribMulActionOfLeNormalizer (normalizer (U : Set G)) U le_rfl
  let y : U := MulDistribMulAction.toMulAut (normalizer (U : Set G)) U s x
  have hy : y ∈ D := by
    apply (hD y).mpr
    exact (inferInstance : N.Normal).conj_mem x ((hD x).mp hx) s
  refine ⟨y, hy, ?_⟩
  exact (quotientAut_apply_mk (frattini U)
    (MulDistribMulAction.toMulAut (normalizer (U : Set G)) U s) x).symm

/-- The structural outer-group condition rules out irreducibility for every Ξ odd group. -/
theorem exists_invariant_of_cyclicNormalOddQuotient
    (hG : HasCyclicNormalOddQuotient G) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (U : Subgroup G) (hU : XiOddQuotient p U) :
    ∃ A : Subgroup (U ⧸ frattini U), A ≠ ⊥ ∧ A ≠ ⊤ ∧
      ∀ s : normalizer (U : Set G), ∀ a ∈ A,
        frattiniConjugationAction (normalizer (U : Set G)) U le_rfl s a ∈ A := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨N, hN, hc, hq⟩ := hG
  let := hN
  let := hc
  exact exists_invariant_of_cyclic_normal N U hU.not_isCyclic
    (hq p hp ho (U.map (QuotientGroup.mk' N)) (hU.isPGroup.map _))

/-- Pull the simple-model structural calculation back to a perfect central cover. -/
theorem cyclicNormalOddQuotient_outer_of_centralQuotient
    {Q S : Type*} [Group Q] [Group S] [Group.IsPerfect Q]
    (e : Q ⧸ center Q ≃* S) (hS : HasCyclicNormalOddQuotient (MulAut.Outer S)) :
    HasCyclicNormalOddQuotient (MulAut.Outer Q) :=
  hS.of_injective (MulAut.centralQuotientOuter e) (MulAut.centralQuotientOuter_injective e)

end CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels
