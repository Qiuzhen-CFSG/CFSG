module
public import Theory.GroupTheory.UniqueMaximalSimplePair

/-!
# Prime support in proper overgroups of an exchanged simple pair

A proper overgroup of the exchanging subgroup has proper intersection with each
simple factor. The projection onto either factor normalizes that nontrivial
intersection, so it lies in the factor's unique maximal overgroup. Thus prime
support in the two factor maxima and in the exchanging subgroup bounds prime
support in every proper overgroup.

Source application: Aschbacher–Smith, The Classification of Quasithin Groups,
10.2.3, printed pp.744–745, for the exchanged A₅ pair.
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

/-- Prime support of the two factor maxima bounds every proper overgroup of
an exchanging subgroup. The integer `p` may be composite. -/
theorem isPGroup_of_simple_pair_proper_overgroup
    (p : ℕ) (A B S V : Subgroup G) [IsSimpleGroup A] [IsSimpleGroup B]
    (hc : B ≤ centralizer (A : Set G))
    (hA : Order.HasUniqueMaximalOver (A ⊓ S) A)
    (hB : Order.HasUniqueMaximalOver (B ⊓ S) B)
    (hneA : A ⊓ S ≠ ⊥) (hneB : B ⊓ S ≠ ⊥)
    (hperm : ∀ s ∈ S,
      (A.map (MulAut.conj s).toMonoidHom = A ∧ B.map (MulAut.conj s).toMonoidHom = B) ∨
      (A.map (MulAut.conj s).toMonoidHom = B ∧ B.map (MulAut.conj s).toMonoidHom = A))
    (hswap : ∃ s ∈ S, A.map (MulAut.conj s).toMonoidHom = B)
    (hAp : ∀ P : Subgroup G, A ⊓ S ≤ P → P < A → IsPGroup p P)
    (hBp : ∀ Q : Subgroup G, B ⊓ S ≤ Q → Q < B → IsPGroup p Q)
    (hSp : IsPGroup p S)
    (hSV : S ≤ V) (hV : V < (A ⊔ B) ⊔ S) : IsPGroup p V := by
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
  have hPp := hAp P hP.1 hP.2.lt
  have hQp := hBp Q hQ.1 hQ.2.lt
  have hQP : Q ≤ normalizer (P : Set G) :=
    ((hQ.2.le.trans hc).trans (centralizer_le hP.2.le)).trans (centralizer_le_normalizer _)
  exact ((hPp.to_sup_of_normal_left' hQp hQP).to_sup_of_normal_left' hSp hSPQ).to_le
    (hbound V hSV hV)

end Subgroup
