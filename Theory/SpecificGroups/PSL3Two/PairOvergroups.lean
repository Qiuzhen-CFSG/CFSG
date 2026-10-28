module
public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.UniqueMaximalSimplePair
public import Theory.GroupTheory.GeneralizedFitting.ComponentSwapNormSylow

/-!
# Proper Sylow overgroups in the exchanged linear-three pair

For a proper Sylow overgroup V, each simple factor meets V in a nontrivial
proper subgroup. The projection of V into that factor normalizes this
intersection. Its normalizer is proper by simplicity and contains a full
Sylow two-subgroup, so the binary parabolic calculation gives only primes
two and three. The exchanging subgroup permutes these two normalizers.
This bounds all of V, and the bound lifts through the original two-core.

Unlike the A₅ calculation, this argument permits two maximal parabolics
above the factor Sylow. Source: Aschbacher--Smith,10.2.3(ii), printed p.745.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace Matrix.PSL3Two
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

omit [Finite G] in
private theorem factor_normalizes_intersection {A B V : Subgroup G}
    (hc : B ≤ centralizer (A : Set G))
    {a b : G} (ha : a ∈ A) (hb : b ∈ B) (hab : a * b ∈ V) :
    a ∈ A ⊓ normalizer ((A ⊓ V : Subgroup G) : Set G) := by
  refine ⟨ha, ?_⟩
  have hbN : b ∈ normalizer ((A ⊓ V : Subgroup G) : Set G) :=
    (Subgroup.centralizer_le_normalizer _) ((centralizer_le inf_le_left) (hc hb))
  have hABN : A ⊔ B ≤ normalizer (A : Set G) :=
    sup_le A.le_normalizer (hc.trans (Subgroup.centralizer_le_normalizer (A : Set G)))
  have habN : a * b ∈ normalizer ((A ⊓ V : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨hABN (mul_mem_sup ha hb), V.le_normalizer hab⟩
  change a ∈ normalizer ((A ⊓ V : Subgroup G) : Set G)
  simpa only [mul_inv_cancel_right] using
    (normalizer ((A ⊓ V : Subgroup G) : Set G)).mul_mem habN
      ((normalizer ((A ⊓ V : Subgroup G) : Set G)).inv_mem hbN)

omit [Finite G] in
private theorem pair_proper_support
    (p : ℕ) (A B S V : Subgroup G) [IsSimpleGroup A] [IsSimpleGroup B]
    (hc : B ≤ centralizer (A : Set G))
    (hneA : A ⊓ S ≠ ⊥) (hneB : B ⊓ S ≠ ⊥)
    (hperm : ∀ s ∈ S,
      (A.map (MulAut.conj s).toMonoidHom = A ∧ B.map (MulAut.conj s).toMonoidHom = B) ∨
      (A.map (MulAut.conj s).toMonoidHom = B ∧ B.map (MulAut.conj s).toMonoidHom = A))
    (hswap : ∃ s ∈ S, A.map (MulAut.conj s).toMonoidHom = B)
    (hAp : ∀ P : Subgroup G, A ⊓ S ≤ P → P < A → IsPGroup p P)
    (hBp : ∀ Q : Subgroup G, B ⊓ S ≤ Q → Q < B → IsPGroup p Q)
    (hSp : IsPGroup p S)
    (hSV : S ≤ V) (hV : V < (A ⊔ B) ⊔ S) : IsPGroup p V := by
  let P := A ⊓ normalizer ((A ⊓ V : Subgroup G) : Set G)
  let Q := B ⊓ normalizer ((B ⊓ V : Subgroup G) : Set G)
  have hconj (X Y : Subgroup G) (s : G) (hs : s ∈ S)
      (hXY : X.map (MulAut.conj s).toMonoidHom = Y) :
      (X ⊓ normalizer ((X ⊓ V : Subgroup G) : Set G)).map (MulAut.conj s).toMonoidHom =
        Y ⊓ normalizer ((Y ⊓ V : Subgroup G) : Set G) := by
    have hVN : V.map (MulAut.conj s).toMonoidHom = V :=
      mem_normalizer_iff_map_conj_eq.mp (V.le_normalizer (hSV hs))
    rw [map_inf _ _ _ (MulAut.conj s).injective,
      map_normalizer_eq_of_bijective _ (MulAut.conj s).bijective,
      map_inf _ _ _ (MulAut.conj s).injective, hXY,
      hVN]
  have hSPQ : S ≤ normalizer ((P ⊔ Q : Subgroup G) : Set G) := by
    intro s hs
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (P ⊔ Q).map (MulAut.conj s).toMonoidHom = P ⊔ Q
    rw [Subgroup.map_sup]
    rcases hperm s hs with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · rw [hconj A A s hs ha, hconj B B s hs hb]
    · rw [hconj A B s hs ha, hconj B A s hs hb, sup_comm]
  have hSAB : S ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
    intro s hs
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (A ⊔ B).map (MulAut.conj s).toMonoidHom = A ⊔ B
    rw [Subgroup.map_sup]
    rcases hperm s hs with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · rw [ha,hb]
    · rw [ha,hb,sup_comm]
  obtain ⟨s,hs,hAB⟩ := hswap
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
      rwa [hAB,hVN])
    exact hV.not_ge (sup_le (sup_le hAV hBV) hSV)
  have hP : A ⊓ S ≤ P := le_inf inf_le_left
    ((le_inf (inf_le_left.trans A.le_normalizer)
      ((inf_le_right.trans hSV).trans V.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf)
  have hQ : B ⊓ S ≤ Q := le_inf inf_le_left
    ((le_inf (inf_le_left.trans B.le_normalizer)
      ((inf_le_right.trans hSV).trans V.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf)
  have hPp := hAp P hP (simple_normalizer_lt inf_le_left
    (fun he => hneA (bot_unique ((inf_le_inf_left A hSV).trans_eq he))) hVA)
  have hQp := hBp Q hQ (simple_normalizer_lt inf_le_left
    (fun he => hneB (bot_unique ((inf_le_inf_left B hSV).trans_eq he))) hVB)
  have hbound : V ≤ (P ⊔ Q) ⊔ S := by
    intro v hv
    obtain ⟨x,hx,t,ht,hxt⟩ := pair_product hSAB (hV.le hv)
    obtain ⟨a,ha,b,hb,hab⟩ := pair_product (hc.trans (Subgroup.centralizer_le_normalizer _)) hx
    have hxV : x ∈ V := by
      have h := V.mul_mem hv (V.inv_mem (hSV ht))
      rwa [← hxt,mul_inv_cancel_right] at h
    have habV : a * b ∈ V := hab ▸ hxV
    have haP := factor_normalizes_intersection hc ha hb habV
    have hbQ := factor_normalizes_intersection (le_centralizer_iff.mp hc) hb ha (by
      have hc' : b * a = a * b := (hc hb a ha).symm
      rwa [hc'])
    rw [← hxt,← hab]
    exact mul_mem_sup (mul_mem_sup haP hbQ) ht
  have hQP : Q ≤ normalizer (P : Set G) :=
    (((inf_le_left : Q ≤ B).trans hc).trans
      (centralizer_le (inf_le_left : P ≤ A))).trans (Subgroup.centralizer_le_normalizer _)
  exact ((hPp.to_sup_of_normal_left' hQp hQP).to_sup_of_normal_left' hSp hSPQ).to_le hbound

private theorem linearThree_overgroup_six
    (S : Sylow 2 G) (e : G ≃* Matrix.PSL3Two.SL)
    (P : Subgroup G) (hSP : (S : Subgroup G) ≤ P) (hP : P ≠ ⊤) : IsPGroup 6 P := by
  let f := e.trans Matrix.PSL3Two.equiv
  let S' := S.mapSurjective (f := f.toMonoidHom) f.surjective
  have hP' : P.map f.toMonoidHom ≠ ⊤ := by
    intro he
    have hh := congrArg (Subgroup.comap f.toMonoidHom) he
    rw [comap_map_eq_self_of_injective f.injective,comap_top] at hh
    exact hP hh
  obtain ⟨U,W,_,_,_,_,hU,hW,hmax⟩ := Matrix.PSL3Two.sylow_parabolics S'
  obtain ⟨N,hN,hPN⟩ := (eq_top_or_exists_le_coatom (P.map f.toMonoidHom)).resolve_left hP'
  have hd : Nat.card (P.map f.toMonoidHom) ∣ 24 := by
    rcases (hmax N hN).mp ((map_mono hSP).trans hPN) with he | he
    · simpa only [he,hU] using card_dvd_of_le hPN
    · simpa only [he,hW] using card_dvd_of_le hPN
  exact (IsPGroup.of_card_dvd_pow (p := 6) (n := 3) (hd.trans (by decide))).of_equiv
    (P.equivMapOfInjective f.toMonoidHom f.injective).symm

private theorem intersection_overgroup_six
    (S : Sylow 2 G) (A : Subgroup G) (hs : A.IsSubnormal)
    (e : A ≃* Matrix.PSL3Two.SL)
    (P : Subgroup G) (hSP : A ⊓ (S : Subgroup G) ≤ P) (hP : P < A) :
    IsPGroup 6 P := by
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_subnormal A hs
  have hle : (R : Subgroup A) ≤ P.subgroupOf A := by
    rw [hR]
    intro a ha
    exact hSP ⟨a.property,ha⟩
  have hne : P.subgroupOf A ≠ ⊤ := fun he => hP.not_ge (subgroupOf_eq_top.mp he)
  exact (linearThree_overgroup_six R e (P.subgroupOf A) hle hne).of_equiv
    (subgroupOfEquivOfLe hP.le)

private theorem sylow_intersection_ne_bot (S : Sylow 2 G) (A : Subgroup G)
    (hs : A.IsSubnormal) (e : A ≃* Matrix.PSL3Two.SL) :
    A ⊓ (S : Subgroup G) ≠ ⊥ := by
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_subnormal A hs
  have hd : 2 ∣ Nat.card A := by
    rw [Nat.card_congr e.toEquiv,Matrix.PSL3Two.card_SL]
    norm_num
  intro he
  apply P.ne_bot_of_dvd_card hd
  apply (map_eq_bot_iff_of_injective _ A.subtype_injective).mp
  rw [hP,subgroupOf_map_subtype,inf_comm]
  exact he

private theorem simple_pair_proper_six (S : Sylow 2 G) (A : Subgroup G)
    (hA : A.IsCComponent) (e : A ≃* Matrix.PSL3Two.SL)
    (hi : (normalizer (A : Set G)).index = 2)
    (hgen : A ⊔ (S : Subgroup G) = ⊤)
    (V : Subgroup G) (hSV : (S : Subgroup G) ≤ V) (hV : V ≠ ⊤) :
    IsPGroup 6 V := by
  have hs : ¬ (S : Subgroup G) ≤ normalizer (A : Set G) := by
    intro hs
    have hd := index_dvd_of_le hs
    rw [hi] at hd
    exact S.not_dvd_index hd
  obtain ⟨s,hs,hsn⟩ := Set.not_subset.mp hs
  let B := A.map (MulAut.conj s).toMonoidHom
  have hm : B ≠ A := fun he => hsn (mem_normalizer_iff_map_conj_eq.mpr he)
  have hB : B.IsCComponent := hA.map_equiv (MulAut.conj s)
  let eB : B ≃* Matrix.PSL3Two.SL := ((MulAut.conj s).subgroupMap A).symm.trans e
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.Comparisons.Exceptional.psl3Two_simple
  let : IsSimpleGroup Matrix.PSL3Two.SL := Matrix.PSL3Two.equiv.isSimpleGroup
  let : IsSimpleGroup A := e.isSimpleGroup
  let : IsSimpleGroup B := eB.isSimpleGroup
  let := hA.perfect
  have hc : B ≤ centralizer (A : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (by
      rw [commutator_comm]
      exact simple_subnormal_commute_of_ne A B hA.subnormal hB.subnormal hm.symm)
  have htop : (A ⊔ B) ⊔ (S : Subgroup G) = ⊤ :=
    top_unique (hgen ▸ sup_le_sup (le_sup_left : A ≤ A ⊔ B) le_rfl)
  exact pair_proper_support 6 A B (S : Subgroup G) V hc
    (sylow_intersection_ne_bot S A hA.subnormal e)
    (sylow_intersection_ne_bot S B hB.subnormal eB)
    (conjugate_pair_permutation A B (S : Subgroup G) hm.symm
      (fun g _ => NormPair.conjugate_eq_or_eq_of_normalizer_index_two hi hm g) s hs rfl)
    ⟨s,hs,rfl⟩ (intersection_overgroup_six S A hA.subnormal e)
    (intersection_overgroup_six S B hB.subnormal eB)
    (S.isPGroup'.mono (by decide : 2 ∣ 6)) hSV (htop ▸ lt_top_iff_ne_top.mpr hV)

/-- Proper Sylow overgroups in the exchanged SL₃(2) pair have only primes
2 and3, including the full ambient two-core. -/
theorem component_pair_proper_overgroup_six
    (S : Sylow 2 G) (A : Subgroup G) (hA : A.IsCComponent)
    (e : (A ⧸ pCore 2 A) ≃* Matrix.PSL3Two.SL)
    (hi : (normalizer (A : Set G)).index = 2)
    (hgen : A ⊔ (S : Subgroup G) = ⊤)
    (V : Subgroup G) (hSV : (S : Subgroup G) ≤ V) (hV : V ≠ ⊤) :
    IsPGroup 6 V := by
  let : Group.IsNilpotent (pCore 2 G) := pCore_isPGroup.isNilpotent
  let q := QuotientGroup.mk' (pCore 2 G)
  let Abar := A.map q
  let Sbar := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hAb : Abar.IsCComponent := hA.map_quotient (pCore 2 G)
  let eb : Abar ≃* Matrix.PSL3Two.SL := (cComponentTwoCoreQuotientEquiv hA).symm.trans e
  have hib : (normalizer (Abar : Set (G ⧸ pCore 2 G))).index = 2 :=
    (cComponent_normalizer_index_quotient hA (pCore 2 G)).trans hi
  have hgenb : Abar ⊔ (Sbar : Subgroup (G ⧸ pCore 2 G)) = ⊤ := by
    change A.map q ⊔ (S : Subgroup G).map q = ⊤
    rw [← Subgroup.map_sup,hgen,map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  have hk : q.ker ≤ V := by
    rw [QuotientGroup.ker_mk']
    exact (pCore_isPGroup.le_sylow_of_normal S).trans hSV
  have hVb : V.map q ≠ ⊤ := by
    intro he
    have hh := congrArg (Subgroup.comap q) he
    rw [comap_map_eq_self hk,comap_top] at hh
    exact hV hh
  have h6 := simple_pair_proper_six Sbar Abar hAb eb hib hgenb
    (V.map q) (map_mono hSV) hVb
  have hk6 : IsPGroup 6 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.mono (by decide : 2 ∣ 6)
  have h := h6.comap_of_ker_isPGroup q hk6
  rwa [comap_map_eq_self hk] at h

end Matrix.PSL3Two
