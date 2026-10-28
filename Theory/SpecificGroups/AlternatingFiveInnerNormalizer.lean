module

public import Theory.SpecificGroups.PSL2.SylowFixedQuotients.Five
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Inner normalizer action on A₅ with abelian ambient two-subgroups

Choose a Sylow two-subgroup P of A and a Sylow two-subgroup S of N_G(A)
containing its image. Since S is abelian, it fixes P pointwise. The checked
A₅ pointwise-fixer theorem makes S act by inner automorphisms on A. Thus
the outer-action image has odd order. Every outer automorphism of A₅ has
square one, so this image is trivial.

The inclusion and the isomorphism A ≃ A₅ are actual group maps. The result
is independent of any classification or simplicity hypothesis on G.
Source application: Aschbacher–Smith, proof of Lemma 1.3.9, printed p.514,
using Proposition A.3.12(8),(15), printed p.47. The automorphism description
of A₅ is the proved GLS3 Theorem 5.2.1 in `Theory.Alternating.Aut`.
-/

open Subgroup
namespace Subgroup

private theorem outer_five_two : IsPGroup 2 (MulAut.Outer (alternatingGroup (Fin 5))) := by
  intro q
  obtain ⟨α, rfl⟩ :=
    QuotientGroup.mk'_surjective (MulAut.innerSubgroup (alternatingGroup (Fin 5))) q
  obtain ⟨σ, rfl⟩ :=
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by decide)
      (by decide)).surjective α
  refine ⟨1, ?_⟩
  simp only [pow_one, ← map_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  have hσ : σ ^ 2 ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup, map_pow]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  exact ⟨⟨σ ^ 2, hσ⟩, MulAut.conjNormal_val.symm⟩

/-- In a finite group with abelian two-subgroups, the normalizer of an actual
A₅ subgroup induces only inner automorphisms on that subgroup. -/
public theorem alternatingFive_normalizerAction_inner {G : Type*} [Group G] [Finite G]
    (hcomm : ∀ R : Subgroup G, IsPGroup 2 R → IsMulCommutative R)
    (A : Subgroup G) (e : A ≃* alternatingGroup (Fin 5))
    (g : normalizer (A : Set G)) : ∃ a : A, A.normalizerMonoidHom g = MulAut.conj a := by
  let N := normalizer (A : Set G)
  let i : A →* N := Subgroup.inclusion A.le_normalizer
  let P : Sylow 2 A := default
  obtain ⟨S, hPS⟩ := (P.isPGroup'.map i).exists_le_sylow
  let R : Subgroup G := (S : Subgroup N).map N.subtype
  let : IsMulCommutative R := hcomm R (S.isPGroup'.map N.subtype)
  let q := (QuotientGroup.mk' (MulAut.innerSubgroup A)).comp A.normalizerMonoidHom
  have hSk : (S : Subgroup N) ≤ q.ker := by
    intro s hs
    have hfix : ∀ x ∈ P, A.normalizerMonoidHom s x = x := by
      intro x hx
      have hxS : i x ∈ S := hPS (mem_map_of_mem i hx)
      let r : R := ⟨s.val, mem_map_of_mem N.subtype hs⟩
      let t : R := ⟨x.val, mem_map_of_mem N.subtype hxS⟩
      have hc : (s : G) * (x : G) = (x : G) * (s : G) :=
        congrArg Subtype.val (mul_comm' r t)
      apply Subtype.ext
      change (s : G) * (x : G) * (s : G)⁻¹ = x
      rw [hc, mul_inv_cancel_right]
    obtain ⟨a, _, ha⟩ := Theory.PSL2.SylowFixedQuotients.fixed_inner_transport e
      (P : Subgroup A)
      (Theory.PSL2.SylowFixedQuotients.alternating_sylow_fixed_inner
        (P.mapSurjective (f := e.toMonoidHom) e.surjective))
      (A.normalizerMonoidHom s) hfix
    change QuotientGroup.mk' (MulAut.innerSubgroup A) (A.normalizerMonoidHom s) = 1
    exact (QuotientGroup.eq_one_iff _).mpr ⟨a, ha.symm⟩
  have ht : IsPGroup 2 (MulAut.Outer A) :=
    outer_five_two.of_injective (MulAut.outerCongr e).toMonoidHom
      (MulAut.outerCongr e).injective
  have hcard : Nat.card q.range = 1 := by
    rcases (ht.to_subgroup q.range).card_eq_or_dvd with h | h
    · exact h
    · exfalso
      apply S.not_dvd_index
      apply h.trans
      rw [← index_ker]
      exact index_dvd_of_le hSk
  have hq : q = 1 := MonoidHom.range_eq_bot_iff.mp (Subgroup.card_eq_one.mp hcard)
  have hg : q g = 1 := by rw [hq]; rfl
  obtain ⟨a, ha⟩ := (QuotientGroup.eq_one_iff _).mp hg
  exact ⟨a, ha.symm⟩

end Subgroup
