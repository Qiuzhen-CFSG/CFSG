module
public import Theory.GroupTheory.TwoOrbitOddPrime.BinaryIndex
public import Theory.GroupTheory.TwoOrbitOddPrime.Residual
public import Theory.GroupTheory.GeneralizedFitting.SylowNormalizedComponent

/-!
# Residuals of exchanged binary components

An exchanged C-component with quasisimple two-core quotient has exactly two
conjugates in odd prime rank at most two. The binary pair index theorem then
identifies its product with O^{p′}, for every odd prime dividing the component.
Perfectness supplies generation by p-elements; no outer-order hypothesis is
needed. The Chapter 14 exchanged-closure consumer retains the actual quotient.

Source: Aschbacher--Smith 1.2.2(a), printed p.504, used in 14.6.14, p.1033.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory.TwoOrbitOddPrime
variable {G : Type*} [Group G] [Finite G]

/-- An exchanged component with quasisimple two-core quotient has exactly two
conjugates under the ambient odd-rank bound. -/
theorem quasisimple_cComponent_normalizer_index_two
    {L : Subgroup G} (hL : L.IsCComponent) [IsQuasisimple (L ⧸ pCore 2 L)]
    (hr : ∀ r : ℕ, r.Prime → Odd r → primeRank r G ≤ 2)
    (t : G) (ht : t ∉ normalizer (L : Set G)) :
    (normalizer (L : Set G)).index = 2 := by
  let : Group.IsNilpotent (pCore 2 G) := pCore_isPGroup.isNilpotent
  let q := QuotientGroup.mk' (pCore 2 G)
  let B := L.map q
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hL)
  have hB : IsComponent (G ⧸ pCore 2 G) B := ⟨(hL.map_quotient _).subnormal,inferInstance⟩
  rcases hB.normal_or_index_two_of_odd_rank_le_two (fun r hp ho => by
    let : Fact r.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup r ho _ pCore_isPGroup).trans (hr r hp ho)) with hn | hi
  · let : L.Normal := cComponent_normal_of_quotient_normal hL _ hn
    exact (ht (L.normalizer_eq_top ▸ mem_top t)).elim
  · exact (cComponent_normalizer_index_quotient hL _).symm.trans hi

/-- The actual exchanged binary pair is O^{p′}, with no outer-order premise. -/
theorem binary_cComponent_pair_eq_primeToResidual
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    {L : Subgroup G} (hL : L.IsCComponent)
    [IsQuasisimple (L ⧸ pCore 2 L)] [IsSimpleGroup (L ⧸ pCore 2 L)]
    (hr : ∀ r : ℕ, r.Prime → Odd r → primeRank r G ≤ 2)
    (t : G) (ht : t ∉ normalizer (L : Set G))
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    (e : (L ⧸ pCore 2 L) ≃* Theory.PSL2.Group F)
    (hd : p ∣ Nat.card (L ⧸ pCore 2 L)) :
    L ⊔ L.conjBy t = primeToResidual p G := by
  have hi := quasisimple_cComponent_normalizer_index_two hL hr t ht
  have hz : center (L ⧸ pCore 2 L) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh : e x ∈ center (Theory.PSL2.Group F) := (centerCongr e ⟨x,hx⟩).property
    rw [GorensteinWalter.psl2_center_eq_bot F,mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  let : Group.IsPerfect L := hL.perfect
  have hperfect : IsPPerfect 2 L := by
    intro N hN hquot
    let := hN
    have hs : Subsingleton (L ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent (L ⧸ N) hquot.isNilpotent
    apply eq_top_iff.mpr
    intro x _
    exact (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)
  have hLR : L ≤ primeToResidual p G := le_primeToResidual_of_eq_top p L
    (primeToResidual_eq_top_of_simple_quotient p 2 (pCore 2 L) pCore_isPGroup hperfect hd)
  let : (L ⊔ L.conjBy t).Normal := TwoOrbitThree.pair_normal_of_index_two L hi t ht
  refine le_antisymm (sup_le hLR ?_) (primeToResidual_le _
    (binary_cComponent_pair_index_coprime p hp hL hi t ht hz hd
      (hr p Fact.out ((Fact.out : p.Prime).odd_of_ne_two hp)) F e))
  rintro x ⟨l,hl,rfl⟩
  exact (inferInstance : (primeToResidual p G).Normal).conj_mem l (hLR hl) t
end Theory.GroupTheory.TwoOrbitOddPrime
