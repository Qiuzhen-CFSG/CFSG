module
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.GeneralizedFitting.ComponentSwapNormSylow
public import Theory.GroupTheory.UniqueMaximalSimplePair

/-!
# Proper Sylow overgroups in an exchanged C-component pair

In a pair of commuting simple factors, a coordinate of a proper overgroup
normalizes its nontrivial intersection with that factor. Simplicity makes
this normalizer proper. Thus control of the proper factor overgroups gives
control of the whole proper overgroup; the exchanging element transfers
the bound from one factor to the other.

For a C-component, pass through the actual ambient two-core quotient.
The two-core lies in the specified Sylow, so properness and containment
lift back without any splitting assumption. This supplies the exchanged
Suzuki component step of Aschbacher--Smith 8.3.7, printed pp.724--725.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem simple_factor_projection_bound
    {A B S M V : Subgroup G} [IsSimpleGroup A]
    (hc : B ≤ centralizer (A : Set G))
    (hne : A ⊓ S ≠ ⊥)
    (hlocal : ∀ U : Subgroup G, A ⊓ S ≤ U → U < A → U ≤ M)
    (hSV : S ≤ V) (hVA : A ⊓ V < A)
    {a b : G} (ha : a ∈ A) (hb : b ∈ B) (hab : a * b ∈ V) : a ∈ M := by
  let U := A ⊓ V
  have hU : U ≠ ⊥ := fun he => hne (bot_unique ((inf_le_inf_left A hSV).trans_eq he))
  have hN : A ⊓ normalizer (U : Set G) < A := by
    apply lt_of_le_of_ne inf_le_left
    intro he
    have hn : A ≤ normalizer (U : Set G) := he ▸ inf_le_right
    let : (U.subgroupOf A).Normal := (normal_subgroupOf_iff_le_normalizer
      (show U ≤ A from inf_le_left)).mpr hn
    rcases (inferInstance : (U.subgroupOf A).Normal).eq_bot_or_eq_top with hbot | htop
    · exact hU (bot_unique (by simpa only [inf_of_le_left (show U ≤ A from inf_le_left)]
        using (subgroupOf_eq_bot.mp hbot).le_bot))
    · exact hVA.not_ge (subgroupOf_eq_top.mp htop)
  have hNM : A ⊓ normalizer (U : Set G) ≤ M := hlocal _
    (le_inf inf_le_left ((le_inf (inf_le_left.trans A.le_normalizer)
      ((inf_le_right.trans hSV).trans V.le_normalizer)).trans
        inf_normalizer_le_normalizer_inf)) hN
  apply hNM
  refine ⟨ha,?_⟩
  have hbN : b ∈ normalizer (U : Set G) :=
    (centralizer_le_normalizer _) ((centralizer_le inf_le_left) (hc hb))
  have habN : a * b ∈ normalizer (U : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨
      (normalizer (A : Set G)).mul_mem (A.le_normalizer ha)
        (centralizer_le_normalizer _ (hc hb)), V.le_normalizer hab⟩
  change a ∈ normalizer (U : Set G)
  simpa only [mul_inv_cancel_right] using
    (normalizer (U : Set G)).mul_mem habN ((normalizer (U : Set G)).inv_mem hbN)

omit [Finite G] in
/-- Proper Sylow overgroups of an exchanged simple pair are controlled by
proper overgroups in its first factor. -/
theorem simple_pair_overgroups_le
    (A B S M : Subgroup G) [IsSimpleGroup A]
    (hc : B ≤ centralizer (A : Set G)) (hne : A ⊓ S ≠ ⊥)
    (hSM : S ≤ M)
    (hlocal : ∀ U : Subgroup G, A ⊓ S ≤ U → U < A → U ≤ M)
    (horbit : ∀ s ∈ S, A.map (MulAut.conj s).toMonoidHom = A ∨
      A.map (MulAut.conj s).toMonoidHom = B)
    (t : G) (ht : t ∈ S) (hAB : A.map (MulAut.conj t).toMonoidHom = B)
    (hneAB : A ≠ B) :
    ∀ V : Subgroup G, S ≤ V → V < (A ⊔ B) ⊔ S → V ≤ M := by
  have hperm := conjugate_pair_permutation A B S hneAB horbit t ht hAB
  have hSMmap : M.map (MulAut.conj t).toMonoidHom = M :=
    mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer (hSM ht))
  have hSmap : S.map (MulAut.conj t).toMonoidHom = S :=
    mem_normalizer_iff_map_conj_eq.mp (S.le_normalizer ht)
  let c := (MulAut.conj t).mapSubgroup
  let : IsSimpleGroup B := ((MulAut.conj t).subgroupMap A |>.trans
    (MulEquiv.subgroupCongr hAB)).symm.isSimpleGroup
  have hneB : B ⊓ S ≠ ⊥ := by
    intro he
    apply hne
    apply map_injective (f := (MulAut.conj t).toMonoidHom) (MulAut.conj t).injective
    rw [map_inf _ _ _ (MulAut.conj t).injective,hAB,hSmap,he,map_bot]
  have hlocalB (U : Subgroup G) (hSU : B ⊓ S ≤ U) (hUB : U < B) : U ≤ M := by
    have hpre : A ⊓ S ≤ c.symm U := c.le_symm_apply.mpr (by
      change (A ⊓ S).map (MulAut.conj t).toMonoidHom ≤ U
      rwa [map_inf _ _ _ (MulAut.conj t).injective,hAB,hSmap])
    have hlt : c.symm U < A := c.symm_apply_lt.mpr (by change U < A.map (MulAut.conj t).toMonoidHom; rwa [hAB])
    have hh := c.monotone (hlocal _ hpre hlt)
    rw [c.apply_symm_apply] at hh
    change U ≤ M.map (MulAut.conj t).toMonoidHom at hh
    rwa [hSMmap] at hh
  have hSAB : S ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
    intro s hs
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (A ⊔ B).map (MulAut.conj s).toMonoidHom = A ⊔ B
    rw [map_sup]
    rcases hperm s hs with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · rw [ha,hb]
    · rw [ha,hb,sup_comm]
  intro V hSV hV
  have hVN : V.map (MulAut.conj t).toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp (V.le_normalizer (hSV ht))
  have hVA : A ⊓ V < A := by
    apply lt_of_le_of_ne inf_le_left
    intro he
    have hAV : A ≤ V := he ▸ inf_le_right
    have hBV : B ≤ V := by
      rw [←hAB,←hVN]
      exact map_mono hAV
    exact hV.not_ge (sup_le (sup_le hAV hBV) hSV)
  have hVB : B ⊓ V < B := by
    have hh := c.strictMono hVA
    change (A ⊓ V).map (MulAut.conj t).toMonoidHom < A.map (MulAut.conj t).toMonoidHom at hh
    rwa [map_inf _ _ _ (MulAut.conj t).injective,hAB,hVN] at hh
  intro v hv
  have hvprod : v ∈ ((A ⊔ B : Subgroup G) : Set G) * (S : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left _ _ hSAB]
    exact hV.le hv
  obtain ⟨x,hx,s,hs,hxs⟩ := hvprod
  change x * s = v at hxs
  have hxprod : x ∈ (A : Set G) * (B : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left _ _ (hc.trans (centralizer_le_normalizer _))]
    exact hx
  obtain ⟨a,ha,b,hb,hab⟩ := hxprod
  change a * b = x at hab
  have hxV : x ∈ V := by
    have hh := V.mul_mem hv (V.inv_mem (hSV hs))
    rwa [←hxs,mul_inv_cancel_right] at hh
  have habV : a * b ∈ V := by rw [hab]; exact hxV
  have haM := simple_factor_projection_bound hc hne hlocal hSV hVA ha hb habV
  have hbM := simple_factor_projection_bound (le_centralizer_iff.mp hc) hneB hlocalB
    hSV hVB hb ha (by rwa [(hc hb a ha).symm])
  rw [←hxs,←hab]
  exact M.mul_mem (M.mul_mem haM hbM) (hSM hs)

/-- In an exchanged C-component pair with simple even two-core quotient,
control of proper factor overgroups controls every proper Sylow overgroup.
The lift uses the original two-core, without assuming it splits. -/
theorem IsCComponent.pair_overgroups_le
    (S : Sylow 2 G) (A M : Subgroup G) (hA : A.IsCComponent)
    [IsSimpleGroup (A ⧸ pCore 2 A)]
    (heven : 2 ∣ Nat.card (A ⧸ pCore 2 A))
    (hi : (normalizer (A : Set G)).index = 2)
    (hgen : A ⊔ (S : Subgroup G) = ⊤) (hSM : (S : Subgroup G) ≤ M)
    (hlocal : ∀ U : Subgroup G, A ⊓ (S : Subgroup G) ≤ U → U < A → U ≤ M) :
    ∀ V : Subgroup G, (S : Subgroup G) ≤ V → V < ⊤ → V ≤ M := by
  let : Group.IsNilpotent (pCore 2 G) := pCore_isPGroup.isNilpotent
  let q := QuotientGroup.mk' (pCore 2 G)
  let Abar := A.map q
  let Sbar := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  let Mbar := M.map q
  have hAb : Abar.IsCComponent := hA.map_quotient (pCore 2 G)
  let e : (A ⧸ pCore 2 A) ≃* Abar := cComponentTwoCoreQuotientEquiv hA
  let : IsSimpleGroup Abar := e.symm.isSimpleGroup
  have hib : (normalizer (Abar : Set (G ⧸ pCore 2 G))).index = 2 :=
    (cComponent_normalizer_index_quotient hA (pCore 2 G)).trans hi
  have hgenb : Abar ⊔ (Sbar : Subgroup (G ⧸ pCore 2 G)) = ⊤ := by
    change A.map q ⊔ (S : Subgroup G).map q = ⊤
    rw [←map_sup,hgen,map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  have hs : ¬ (Sbar : Subgroup (G ⧸ pCore 2 G)) ≤ normalizer (Abar : Set _) := by
    intro hs
    have hd := index_dvd_of_le hs
    rw [hib] at hd
    exact Sbar.not_dvd_index hd
  obtain ⟨s,hs,hsn⟩ := Set.not_subset.mp hs
  let B := Abar.map (MulAut.conj s).toMonoidHom
  have hm : B ≠ Abar := fun he => hsn (mem_normalizer_iff_map_conj_eq.mpr he)
  have hB : B.IsCComponent := hAb.map_equiv (MulAut.conj s)
  let : IsSimpleGroup B := ((MulAut.conj s).subgroupMap Abar).symm.isSimpleGroup
  let := hAb.perfect
  have hc : B ≤ centralizer (Abar : Set _) :=
    commutator_eq_bot_iff_le_centralizer.mp (by
      rw [commutator_comm]
      exact simple_subnormal_commute_of_ne Abar B hAb.subnormal hB.subnormal hm.symm)
  have hne : Abar ⊓ (Sbar : Subgroup _) ≠ ⊥ := by
    obtain ⟨P,hP⟩ := Sbar.exists_subgroupOf_eq_of_subnormal Abar hAb.subnormal
    intro he
    apply P.ne_bot_of_dvd_card (show 2 ∣ Nat.card Abar by rwa [←Nat.card_congr e.toEquiv])
    apply (map_eq_bot_iff_of_injective _ Abar.subtype_injective).mp
    rw [hP,subgroupOf_map_subtype,inf_comm]
    exact he
  have hlocalb (U : Subgroup (G ⧸ pCore 2 G))
      (hSU : Abar ⊓ (Sbar : Subgroup _) ≤ U) (hUA : U < Abar) : U ≤ Mbar := by
    let W := A ⊓ U.comap q
    have hSW : A ⊓ (S : Subgroup G) ≤ W := by
      rintro x ⟨hxA,hxS⟩
      exact ⟨hxA,hSU ⟨mem_map_of_mem q hxA,mem_map_of_mem q hxS⟩⟩
    have hWA : W < A := by
      apply lt_of_le_of_ne inf_le_left
      intro he
      apply hUA.not_ge
      rintro _ ⟨x,hx,rfl⟩
      have hh : x ∈ W := by change x ∈ A ⊓ U.comap q; rw [he]; exact hx
      exact hh.2
    have hWM := hlocal W hSW hWA
    intro x hx
    obtain ⟨a,ha,rfl⟩ := hUA.le hx
    exact mem_map_of_mem q (hWM ⟨ha,hx⟩)
  have hbound := simple_pair_overgroups_le Abar B (Sbar : Subgroup _) Mbar
    hc hne (map_mono hSM) hlocalb
    (fun g _ => NormPair.conjugate_eq_or_eq_of_normalizer_index_two hib hm g)
    s hs rfl hm.symm
  have htop : (Abar ⊔ B) ⊔ (Sbar : Subgroup _) = ⊤ :=
    top_unique (hgenb ▸ sup_le_sup (le_sup_left : Abar ≤ Abar ⊔ B) le_rfl)
  have hk : q.ker ≤ (S : Subgroup G) := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal S
  intro V hSV hV
  have hVb : V.map q < (Abar ⊔ B) ⊔ (Sbar : Subgroup _) := by
    rw [htop]
    apply lt_top_iff_ne_top.mpr
    intro he
    have hh := congrArg (comap q) he
    rw [comap_map_eq_self (hk.trans hSV),comap_top] at hh
    exact hV.ne hh
  have hh := map_le_iff_le_comap.mp (hbound (V.map q) (map_mono hSV) hVb)
  rwa [comap_map_eq_self (hk.trans hSM)] at hh

end Subgroup
