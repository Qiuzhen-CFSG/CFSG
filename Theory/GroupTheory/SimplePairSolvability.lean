module
public import Theory.GroupTheory.UniqueMaximalSimplePair
public import Theory.GroupTheory.NormalizedSupConsequences

/-!
# Solvable proper overgroups of exchanged simple factors

For a proper overgroup of an exchanging subgroup, the projection to each
simple factor normalizes its nontrivial proper intersection with that factor.
It therefore lies in the unique maximal Sylow overgroup. If these two
maxima and the exchanging subgroup are solvable, their normalized product
is solvable and contains the original overgroup.

This is the solvability version of the projection argument in
`SimplePairPrimeSupport`, used for the Bender pair in Aschbacher--Smith
10.3.3, printed p.756. The normal-factor variant uses the ordinary subgroup
product decomposition.
-/

public section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
private theorem pair_product {A B : Subgroup G}
    (hn : B ≤ normalizer (A : Set G)) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  have hh : x ∈ (A : Set G) * (B : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left A B hn]
    exact hx
  exact hh

omit [Finite G] in
private theorem simple_normalizer_lt {A X : Subgroup G} [IsSimpleGroup A]
    (hXA : X ≤ A) (hX : X ≠ ⊥) (hlt : X < A) :
    A ⊓ normalizer (X : Set G) < A := by
  apply lt_of_le_of_ne inf_le_left
  intro he
  have hn : A ≤ normalizer (X : Set G) := he ▸ inf_le_right
  let : (X.subgroupOf A).Normal := (normal_subgroupOf_iff_le_normalizer hXA).mpr hn
  rcases (inferInstance : (X.subgroupOf A).Normal).eq_bot_or_eq_top with hbot | htop
  · have hdis := subgroupOf_eq_bot.mp hbot
    exact hX (bot_unique (by simpa only [inf_of_le_left hXA] using hdis.le_bot))
  · exact hlt.not_ge (subgroupOf_eq_top.mp htop)

private theorem pair_factor_bound {A B S V P : Subgroup G} [IsSimpleGroup A]
    (hc : B ≤ centralizer (A : Set G))
    (hu : Order.HasUniqueMaximalOver (A ⊓ S) A)
    (hP : A ⊓ S ≤ P ∧ P ⋖ A) (hne : A ⊓ S ≠ ⊥)
    (hSV : S ≤ V) (hVA : A ⊓ V < A)
    {a b : G} (ha : a ∈ A) (hb : b ∈ B) (hab : a * b ∈ V) : a ∈ P := by
  have hXA : A ⊓ V ≠ ⊥ := fun he => hne (bot_unique ((inf_le_inf_left A hSV).trans_eq he))
  have hN : A ⊓ normalizer ((A ⊓ V : Subgroup G) : Set G) ≤ P := by
    apply hu.le_maximal hP
    · refine le_inf inf_le_left ?_
      exact (le_inf (inf_le_left.trans A.le_normalizer)
        ((inf_le_right.trans hSV).trans V.le_normalizer)).trans inf_normalizer_le_normalizer_inf
    · exact simple_normalizer_lt inf_le_left hXA hVA
  apply hN
  refine ⟨ha, ?_⟩
  have hbN : b ∈ normalizer ((A ⊓ V : Subgroup G) : Set G) :=
    (centralizer_le_normalizer _) ((centralizer_le inf_le_left) (hc hb))
  have hABN : A ⊔ B ≤ normalizer (A : Set G) :=
    sup_le A.le_normalizer (hc.trans (centralizer_le_normalizer (A : Set G)))
  have habAB : a * b ∈ A ⊔ B := mul_mem_sup ha hb
  have habN : a * b ∈ normalizer ((A ⊓ V : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨hABN habAB, V.le_normalizer hab⟩
  change a ∈ normalizer ((A ⊓ V : Subgroup G) : Set G)
  simpa only [mul_inv_cancel_right] using
    (normalizer ((A ⊓ V : Subgroup G) : Set G)).mul_mem habN ((normalizer ((A ⊓ V : Subgroup G) : Set G)).inv_mem hbN)

omit [Finite G] in
private theorem maximal_conj {A B S P Q : Subgroup G}
    (hB : Order.HasUniqueMaximalOver (B ⊓ S) B)
    (hP : A ⊓ S ≤ P ∧ P ⋖ A) (hQ : B ⊓ S ≤ Q ∧ Q ⋖ B)
    (s : G) (hs : s ∈ S) (hAB : A.map (MulAut.conj s).toMonoidHom = B) :
    P.map (MulAut.conj s).toMonoidHom = Q := by
  apply hB.2.unique _ hQ
  constructor
  · have hmap := map_mono (f := (MulAut.conj s).toMonoidHom) hP.1
    rw [map_inf _ _ _ (MulAut.conj s).injective, hAB] at hmap
    have hS : S.map (MulAut.conj s).toMonoidHom = S :=
      mem_normalizer_iff_map_conj_eq.mp (S.le_normalizer hs)
    simpa only [hS] using hmap
  · have hc := (apply_covBy_apply_iff (MulAut.conj s).mapSubgroup).mpr hP.2
    change P.map (MulAut.conj s).toMonoidHom ⋖ A.map (MulAut.conj s).toMonoidHom at hc
    rwa [hAB] at hc

/-- Solvable factor maxima give solvability of every proper overgroup of
the exchanging solvable subgroup. -/
theorem isSolvable_of_simple_pair_proper_overgroup
    (A B S V : Subgroup G) [IsSimpleGroup A] [IsSimpleGroup B]
    (hc : B ≤ centralizer (A : Set G))
    (hA : Order.HasUniqueMaximalOver (A ⊓ S) A)
    (hB : Order.HasUniqueMaximalOver (B ⊓ S) B)
    (hneA : A ⊓ S ≠ ⊥) (hneB : B ⊓ S ≠ ⊥)
    (hperm : ∀ s ∈ S,
      (A.map (MulAut.conj s).toMonoidHom = A ∧ B.map (MulAut.conj s).toMonoidHom = B) ∨
      (A.map (MulAut.conj s).toMonoidHom = B ∧ B.map (MulAut.conj s).toMonoidHom = A))
    (hswap : ∃ s ∈ S, A.map (MulAut.conj s).toMonoidHom = B)
    (hAp : ∀ P : Subgroup G, A ⊓ S ≤ P → P < A → Group.IsSolvable P)
    (hBp : ∀ Q : Subgroup G, B ⊓ S ≤ Q → Q < B → Group.IsSolvable Q)
    [Group.IsSolvable S]
    (hSV : S ≤ V) (hV : V < (A ⊔ B) ⊔ S) : Group.IsSolvable V := by
  obtain ⟨P, hP, _⟩ := hA.2
  obtain ⟨Q, hQ, _⟩ := hB.2
  have hSPQ : S ≤ normalizer ((P ⊔ Q : Subgroup G) : Set G) := by
    intro s hs
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (P ⊔ Q).map (MulAut.conj s).toMonoidHom = P ⊔ Q
    rw [map_sup]
    rcases hperm s hs with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [maximal_conj hA hP hP s hs ha, maximal_conj hB hQ hQ s hs hb]
    · rw [maximal_conj hB hP hQ s hs ha, maximal_conj hA hQ hP s hs hb, sup_comm]
  have hSAB : S ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
    intro s hs
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (A ⊔ B).map (MulAut.conj s).toMonoidHom = A ⊔ B
    rw [map_sup]
    rcases hperm s hs with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ha, hb]
    · rw [ha, hb, sup_comm]
  have hbound (V : Subgroup G) (hSV : S ≤ V) (hV : V < (A ⊔ B) ⊔ S) :
      V ≤ (P ⊔ Q) ⊔ S := by
    obtain ⟨s, hs, hAB⟩ := hswap
    have hVN : V.map (MulAut.conj s).toMonoidHom = V :=
      mem_normalizer_iff_map_conj_eq.mp (V.le_normalizer (hSV hs))
    have hVA : A ⊓ V < A := by
      apply lt_of_le_of_ne inf_le_left
      intro he
      have hAV : A ≤ V := he ▸ inf_le_right
      have hBV : B ≤ V := by
        rw [← hAB, ← hVN]
        exact map_mono hAV
      exact hV.not_ge (sup_le (sup_le hAV hBV) hSV)
    have hVB : B ⊓ V < B := by
      apply lt_of_le_of_ne inf_le_left
      intro he
      have hBV : B ≤ V := he ▸ inf_le_right
      have hAV : A ≤ V := (MulAut.conj s).mapSubgroup.le_iff_le.mp (by
        change A.map (MulAut.conj s).toMonoidHom ≤ V.map (MulAut.conj s).toMonoidHom
        rwa [hAB, hVN])
      exact hV.not_ge (sup_le (sup_le hAV hBV) hSV)
    intro v hv
    obtain ⟨x, hx, t, ht, hxt⟩ := pair_product hSAB (hV.le hv)
    obtain ⟨a, ha, b, hb, hab⟩ := pair_product (hc.trans (centralizer_le_normalizer _)) hx
    have hxV : x ∈ V := by
      have h := V.mul_mem hv (V.inv_mem (hSV ht))
      rwa [← hxt, mul_inv_cancel_right] at h
    have habV : a * b ∈ V := hab ▸ hxV
    have haP := pair_factor_bound hc hA hP hneA hSV hVA ha hb habV
    have hbQ := pair_factor_bound (le_centralizer_iff.mp hc) hB hQ hneB hSV hVB hb ha (by
      have hc' : b * a = a * b := (hc hb a ha).symm
      rwa [hc'])
    rw [← hxt, ← hab]
    exact mul_mem_sup (mul_mem_sup haP hbQ) ht
  let := hAp P hP.1 hP.2.lt
  let := hBp Q hQ.1 hQ.2.lt
  have hQP : Q ≤ normalizer (P : Set G) :=
    ((hQ.2.le.trans hc).trans (centralizer_le hP.2.le)).trans (centralizer_le_normalizer _)
  let := Group.isSolvable_sup_of_normalizes P Q hQP
  let := Group.isSolvable_sup_of_normalizes (P ⊔ Q) S hSPQ
  exact Group.isSolvable_of_isSolvable_injective
    (f := inclusion (hbound V hSV hV)) (inclusion_injective _)

omit [Finite G] in
/-- Proper overgroups of a solvable normalizing supplement are solvable when
proper overgroups of its intersection with the normal factor are solvable. -/
theorem isSolvable_proper_overgroup_of_normalizes
    (A S V : Subgroup G) [Group.IsSolvable S]
    (hn : S ≤ normalizer (A : Set G))
    (hA : ∀ P : Subgroup G, A ⊓ S ≤ P → P < A → Group.IsSolvable P)
    (hSV : S ≤ V) (hV : V < A ⊔ S) : Group.IsSolvable V := by
  have hVA : V ⊓ A < A := by
    apply lt_of_le_of_ne inf_le_right
    intro he
    exact hV.not_ge (sup_le (he ▸ inf_le_left) hSV)
  let := hA (V ⊓ A) (le_inf (inf_le_right.trans hSV) inf_le_left) hVA
  have hSn : S ≤ normalizer ((V ⊓ A : Subgroup G) : Set G) :=
    (le_inf (hSV.trans V.le_normalizer) hn).trans inf_normalizer_le_normalizer_inf
  have he : V = (V ⊓ A) ⊔ S := by
    apply le_antisymm
    · intro x hx
      obtain ⟨a, ha, s, hs, has⟩ := pair_product hn (hV.le hx)
      have haV : a ∈ V := by
        have h := V.mul_mem hx (V.inv_mem (hSV hs))
        rwa [← has, mul_inv_cancel_right] at h
      rw [← has]
      exact mul_mem_sup ⟨haV, ha⟩ hs
    · exact sup_le inf_le_left hSV
  rw [he]
  exact Group.isSolvable_sup_of_normalizes _ _ hSn

end Subgroup
