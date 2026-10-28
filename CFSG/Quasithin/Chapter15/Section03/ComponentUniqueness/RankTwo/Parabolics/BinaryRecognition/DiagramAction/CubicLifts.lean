module

public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PCoreSurjective
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Invariant cubic residuals from the rank-two two-core quotient

Given `J = Y ⊔ S` with S a two-group normalizing Y, a marking
`J/O₂(J) ≃ S₃ × S₃` gives two normal cubic axes. Take the embedded
two-residuals of their full preimages. Residual functoriality shows that
these subgroups map onto the axes. The restricted maps have two-group
kernels, which are their full two-cores because the images have odd order.
The same argument gives the join's quotient order nine.

Since Y is normal in J and J/Y is a two-group, both residuals lie in Y.
Their normality in J gives invariance under every element of S. Transport
into the normal ambient subgroup D preserves the actual conjugation action,
two-perfectness, and all three quotient orders.

This is the conditional lifting step used in the last paragraph of the
proof of 15.3.35. The two-core quotient marking is an explicit input; the
passage from the source's `O_{2,Φ}` quotient remains with its assembly owner.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), printed
p.1139; normalization is supplied by 15.3.11(4), printed p.1123.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.BinaryRecognition.DiagramAction.CubicLifts
variable {G H : Type*} [Group G] [Group H]

private theorem core_eq_bot_of_odd [Finite G] (h : Nat.Coprime 2 (Nat.card G)) :
    pCore 2 G = ⊥ := by
  rcases (pCore_isPGroup (p := 2) (G := G)).card_eq_or_dvd with hc | hd
  · exact card_eq_one.mp hc
  · exact ((by decide : 2 ≠ 1) (Nat.eq_one_of_dvd_coprimes h (dvd_refl 2)
      (hd.trans (card_subgroup_dvd_card _)))).elim

private theorem residual_eq_top_of_odd [Finite G] (h : Nat.Coprime 2 (Nat.card G)) :
    pResidual 2 G = ⊤ := by
  apply top_unique
  intro x _
  exact mem_pResidual_of_orderOf_coprime (h.of_dvd_right (orderOf_dvd_natCard x))

private theorem core_quotient_card_map [Finite G] [Finite H]
    (f : G →* H) (hk : IsPGroup 2 f.ker) (A : Subgroup G)
    (hodd : Nat.Coprime 2 (Nat.card (A.map f))) :
    Nat.card (A ⧸ pCore 2 A) = Nat.card (A.map f) := by
  let g := f.subgroupMap A
  have hkg : IsPGroup 2 g.ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  have he : g.ker = pCore 2 A := by
    have h := g.comap_pCore_of_ker_isPGroup (f.subgroupMap_surjective A) hkg
    rwa [core_eq_bot_of_odd hodd, MonoidHom.comap_bot] at h
  exact Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq he.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective g (f.subgroupMap_surjective A))).toEquiv

private theorem residual_lift_image [Finite G] (f : G →* H) (hf : Function.Surjective f)
    (K : Subgroup H) [Finite K] (hodd : Nat.Coprime 2 (Nat.card K)) :
    ((pResidual 2 (K.comap f)).map (K.comap f).subtype).map f = K := by
  rw [map_embedded_pResidual, map_comap_eq_self_of_surjective hf,
    residual_eq_top_of_odd hodd, ← MonoidHom.range_eq_map, range_subtype]

local notation "S3" => Equiv.Perm (Fin 3)
private abbrev C : Subgroup S3 := alternatingGroup (Fin 3)
private abbrev U : Subgroup (S3 × S3) := C.prod ⊥
private abbrev V : Subgroup (S3 × S3) := (⊥ : Subgroup S3).prod C
private theorem card_C : Nat.card C = 3 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide
private theorem card_U : Nat.card U = 3 := by
  rw [Nat.card_congr (prodEquiv C (⊥ : Subgroup S3)).toEquiv, Nat.card_prod,
    card_C, card_bot, mul_one]
private theorem card_V : Nat.card V = 3 := by
  rw [Nat.card_congr (prodEquiv (⊥ : Subgroup S3) C).toEquiv, Nat.card_prod,
    card_C, card_bot, one_mul]
private theorem sup_UV : U ⊔ V = C.prod C := by
  apply le_antisymm (sup_le (prod_mono le_rfl bot_le) (prod_mono bot_le le_rfl))
  intro x hx
  have h1 : (x.1, (1 : S3)) ∈ U ⊔ V := mem_sup_left ⟨hx.1, rfl⟩
  have h2 : ((1 : S3), x.2) ∈ U ⊔ V := mem_sup_right ⟨rfl, hx.2⟩
  simpa using (U ⊔ V).mul_mem h1 h2
private theorem card_UV : Nat.card (U ⊔ V : Subgroup _) = 9 := by
  rw [sup_UV, Nat.card_congr (prodEquiv C C).toEquiv, Nat.card_prod, card_C]

private theorem normal_pair [Finite G] (f : G →* (S3 × S3)) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) :
    ∃ A B : Subgroup G, A.Normal ∧ B.Normal ∧
      IsPPerfect 2 A ∧ IsPPerfect 2 B ∧
      Nat.card (A ⧸ pCore 2 A) = 3 ∧ Nat.card (B ⧸ pCore 2 B) = 3 ∧
      Nat.card ((A ⊔ B : Subgroup G) ⧸ pCore 2 (A ⊔ B : Subgroup G)) = 9 := by
  let A := (pResidual 2 (U.comap f)).map (U.comap f).subtype
  let B := (pResidual 2 (V.comap f)).map (V.comap f).subtype
  have ha : A.map f = U := residual_lift_image f hf U (by rw [card_U]; decide)
  have hb : B.map f = V := residual_lift_image f hf V (by rw [card_V]; decide)
  refine ⟨A, B, inferInstance, inferInstance, isPPerfect_embedded_pResidual 2 _,
    isPPerfect_embedded_pResidual 2 _, ?_, ?_, ?_⟩
  · rw [core_quotient_card_map f hk A (by rw [ha, card_U]; decide), ha, card_U]
  · rw [core_quotient_card_map f hk B (by rw [hb, card_V]; decide), hb, card_V]
  · rw [core_quotient_card_map f hk (A ⊔ B) (by rw [Subgroup.map_sup, ha, hb, card_UV]; decide),
      Subgroup.map_sup, ha, hb, card_UV]

private theorem core_quotient_card_equiv (e : G ≃* H) :
    Nat.card (G ⧸ pCore 2 G) = Nat.card (H ⧸ pCore 2 H) :=
  Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv

private theorem map_conjNormal_eq {X : Type*} [Group X]
    (D J : Subgroup X) [D.Normal] (A : Subgroup J) [A.Normal]
    (s : X) (hs : s ∈ J) :
    ((A.map J.subtype).subgroupOf D).map (MulAut.conjNormal s).toMonoidHom =
      (A.map J.subtype).subgroupOf D := by
  have hn : J ≤ normalizer (A.map J.subtype : Set X) := by
    have h := A.le_normalizer_map J.subtype
    rwa [A.normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at h
  ext x
  rw [mem_map_equiv]
  change ((MulAut.conjNormal s).symm x : X) ∈ A.map J.subtype ↔
    (x : X) ∈ A.map J.subtype
  rw [MulAut.conjNormal_symm_apply]
  simpa only [inv_inv] using (mem_normalizer_iff.mp (hn (J.inv_mem hs)) x).symm

/-- Lift the two cubic axes to two-perfect subgroups of D, with exact
individual and join two-core quotient orders and literal S-invariance.
Only the displayed two-core quotient marking and normalization are needed. -/
theorem exists_invariant_cubic_pair {X : Type*} [Group X] [Finite X]
    (D Y S : Subgroup X) [D.Normal] (hYD : Y ≤ D)
    (hS : IsPGroup 2 S) (hn : S ≤ normalizer (Y : Set X))
    (he : Nonempty (((Y ⊔ S : Subgroup X) ⧸ pCore 2 (Y ⊔ S : Subgroup X)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) :
    ∃ A B : Subgroup D, IsPPerfect 2 A ∧ IsPPerfect 2 B ∧
      Nat.card (A ⧸ pCore 2 A) = 3 ∧ Nat.card (B ⧸ pCore 2 B) = 3 ∧
      Nat.card ((A ⊔ B : Subgroup D) ⧸ pCore 2 (A ⊔ B : Subgroup D)) = 9 ∧
      (∀ s ∈ S, A.map (MulAut.conjNormal s).toMonoidHom = A) ∧
      (∀ s ∈ S, B.map (MulAut.conjNormal s).toMonoidHom = B) := by
  obtain ⟨e⟩ := he
  let J := Y ⊔ S
  let f : J →* (S3 × S3) := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 f.ker := by
    have hker : f.ker = pCore 2 J := by
      ext x
      change e (QuotientGroup.mk' (pCore 2 J) x) = 1 ↔ x ∈ pCore 2 J
      rw [e.map_eq_one_iff]
      exact QuotientGroup.eq_one_iff x
    rw [hker]
    exact pCore_isPGroup
  obtain ⟨A, B, hAn, hBn, hAp, hBp, hcA, hcB, hcAB⟩ := normal_pair f hf hk
  have hYn : (Y.subgroupOf J).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le Y.le_normalizer hn)
  have hJq : IsPGroup 2 (J ⧸ Y.subgroupOf J) := by
    apply isPGroup_quotient_of_sup_eq_top (Y.subgroupOf J) (S.subgroupOf J) hS.comap_subtype
    rw [← subgroupOf_sup (show Y ≤ J from le_sup_left) (show S ≤ J from le_sup_right)]
    exact subgroupOf_self J
  have hres : pResidual 2 J ≤ Y.subgroupOf J := sInf_le ⟨hYn, hJq⟩
  have hAD : A.map J.subtype ≤ D := by
    rintro x ⟨a, ha, rfl⟩
    exact hYD (hres (le_pResidual_of_isPPerfect A hAp ha))
  have hBD : B.map J.subtype ≤ D := by
    rintro x ⟨b, hb, rfl⟩
    exact hYD (hres (le_pResidual_of_isPPerfect B hBp hb))
  let A' := (A.map J.subtype).subgroupOf D
  let B' := (B.map J.subtype).subgroupOf D
  let ea : A' ≃* A := (subgroupOfEquivOfLe hAD).trans
    (A.equivMapOfInjective J.subtype J.subtype_injective).symm
  let eb : B' ≃* B := (subgroupOfEquivOfLe hBD).trans
    (B.equivMapOfInjective J.subtype J.subtype_injective).symm
  have hAB : A' ⊔ B' = ((A ⊔ B).map J.subtype).subgroupOf D := by
    rw [Subgroup.map_sup, subgroupOf_sup hAD hBD]
  let eab : (A' ⊔ B' : Subgroup D) ≃* (A ⊔ B : Subgroup J) :=
    (MulEquiv.subgroupCongr hAB).trans ((subgroupOfEquivOfLe (by
      rw [Subgroup.map_sup]; exact sup_le hAD hBD)).trans
      ((A ⊔ B).equivMapOfInjective J.subtype J.subtype_injective).symm)
  exact ⟨A', B', hAp.of_surjective ea.symm.toMonoidHom ea.symm.surjective,
    hBp.of_surjective eb.symm.toMonoidHom eb.symm.surjective,
    (core_quotient_card_equiv ea).trans hcA, (core_quotient_card_equiv eb).trans hcB,
    (core_quotient_card_equiv eab).trans hcAB,
    fun s hs => map_conjNormal_eq D J A s (mem_sup_right hs),
    fun s hs => map_conjNormal_eq D J B s (mem_sup_right hs)⟩
end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.BinaryRecognition.DiagramAction.CubicLifts
