module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors.Geometry
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.ActorData
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.FactorIdentification.Kernel
public import Theory.SpecificGroups.SymmetricThreeProduct.NormalThreeSubgroups
public import Theory.GroupTheory.PResidual.NormalSubgroup.TwoGroupKernel
public import Theory.GroupTheory.PResidual.PrimeSection

/-!
# Lifting the two normal directions of the rank-two shadow

The genuine projection modulo O₂,Φ(Y₊S) has a two-group kernel in the
order-nine branch. Its restriction to Y₊ has kernel exactly O₂(Y₊), and
its image is the product of the alternating subgroups of S₃ × S₃. This
proves elementary abelianness of the actual two-core quotient.

A normal, S-invariant two-perfect subgroup with three-part three maps
onto one of the two normal axes. Take the preimage of the other axis
inside Y₊ and then its two-residual. Normality and S-invariance survive
this construction, the two-group kernel preserves its three-part, and
two-perfectness lifts generation from the quotient. No complementary
actor or identification of the plane factors is an input.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the
rank-two quotient in 15.3.36 and the actor selections in 15.3.39–40,
printed pp.1135 and 1137–1138.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo
variable {G : Type*} [Group G] [Finite G]

private theorem odd_perfect {D : Type*} [Group D] (h : IsPGroup 3 D) : IsPPerfect 2 D := by
  apply (pResidual_eq_top_iff 2 D).mp
  apply top_unique
  intro x _
  exact mem_pResidual_of_orderOf_coprime (h.orderOf_coprime (by decide : Nat.Coprime 3 2) x).symm

private theorem model_residual : pResidual 2 SymmetricThreeProduct.G =
    SymmetricThreeProduct.threeCore.prod SymmetricThreeProduct.threeCore := by
  let P := SymmetricThreeProduct.threeCore.prod SymmetricThreeProduct.threeCore
  have hcP : Nat.card P = 9 := by rw [Nat.card_eq_fintype_card]; decide
  have hiP : P.index = 4 := by
    have hh := P.card_mul_index
    rw [hcP, SymmetricThreeProduct.card_group] at hh
    omega
  exact pResidual_eq_of_isPPerfect P (odd_perfect (IsPGroup.of_card (n := 2) hcP))
    (IsPGroup.of_card (n := 2) (by rw [← index_eq_card, hiP]; rfl))

/-- The actual rank-two projection has two-group kernel and maps Y onto E9. -/
theorem rankTwoShadow_map_data {Y S : Subgroup G}
    (hY : IsPPerfect 2 Y)
    (hquot : Nat.card (Y ⧸ pCore 2 Y) = 9)
    (hS : IsPGroup 2 S) (hSY : S ≤ normalizer (Y : Set G))
    (hshadow : RankTwoShadow Y S) :
    ∃ f : (Y ⊔ S : Subgroup G) →* SymmetricThreeProduct.G,
      Function.Surjective f ∧ IsPGroup 2 f.ker ∧
      (Y.subgroupOf (Y ⊔ S)).map f =
        SymmetricThreeProduct.threeCore.prod SymmetricThreeProduct.threeCore := by
  obtain ⟨e⟩ := hshadow
  let H := Y ⊔ S
  let f : H →* SymmetricThreeProduct.G :=
    e.toMonoidHom.comp (QuotientGroup.mk' (twoFrattiniCore H))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkf : f.ker = twoFrattiniCore H := by
    ext x
    simp only [MonoidHom.mem_ker, f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      EmbeddingLike.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  refine ⟨f, hf, hkf ▸ rankTwoShadow_kernel_isTwoGroup hquot hS hSY e, ?_⟩
  let : (Y.subgroupOf H).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le Y.le_normalizer hSY)
  have hp : IsPPerfect 2 (Y.subgroupOf H) :=
    hY.of_surjective (subgroupOfEquivOfLe (show Y ≤ H from le_sup_left)).symm.toMonoidHom
      (subgroupOfEquivOfLe (show Y ≤ H from le_sup_left)).symm.surjective
  have hs : Y.subgroupOf H ⊔ S.subgroupOf H = ⊤ := by
    rw [← subgroupOf_sup (show Y ≤ H from le_sup_left) (show S ≤ H from le_sup_right)]
    exact subgroupOf_self _
  rw [← pResidual_eq_of_isPPerfect_sup (Y.subgroupOf H) (S.subgroupOf H)
    hp hS.comap_subtype hs, map_pResidual_of_surjective 2 f hf, model_residual]

private theorem cube_comm : ∀ a b : Equiv.Perm (Fin 3),
    a ^ 3 = 1 → b ^ 3 = 1 → a * b = b * a := by decide +kernel

/-- The rank-two shadow forces elementary abelianness of the actual two-core quotient. -/
theorem rankTwoShadow_quotient_elementary {Y S : Subgroup G}
    (hY : IsPPerfect 2 Y)
    (hquot : Nat.card (Y ⧸ pCore 2 Y) = 9)
    (hS : IsPGroup 2 S) (hSY : S ≤ normalizer (Y : Set G))
    (hshadow : RankTwoShadow Y S) : IsElementaryAbelian 3 (Y ⧸ pCore 2 Y) := by
  obtain ⟨f, _, hk2, hYP⟩ := rankTwoShadow_map_data hY hquot hS hSY hshadow
  let H := Y ⊔ S
  let g := f.comp (inclusion (show Y ≤ H from le_sup_left))
  have hg2 : IsPGroup 2 g.ker := by
    change IsPGroup 2 (f.comp (inclusion (show Y ≤ H from le_sup_left))).ker
    rw [← MonoidHom.comap_ker]
    exact hk2.comap_of_injective _ (inclusion_injective _)
  let P := SymmetricThreeProduct.threeCore.prod SymmetricThreeProduct.threeCore
  have hgP : g.range ≤ P := by
    rintro _ ⟨y, rfl⟩
    change g y ∈ SymmetricThreeProduct.threeCore.prod SymmetricThreeProduct.threeCore
    rw [← hYP]
    exact mem_map.mpr ⟨inclusion le_sup_left y, y.property, rfl⟩
  have hP3 : IsPGroup 3 P := IsPGroup.of_card (n := 2) (by
    rw [Nat.card_eq_fintype_card]; decide)
  have hcore : pCore 2 Y ≤ g.ker := by
    have hd := (pCore_isPGroup (p := 2) (G := Y)).map g |>.disjoint_of_coprime hP3
      (by decide : Nat.Coprime 2 3)
    intro x hx
    apply MonoidHom.mem_ker.mpr
    exact Subgroup.disjoint_def.mp hd (mem_map_of_mem g hx) (hgP ⟨x, rfl⟩)
  have hker : g.ker = pCore 2 Y := le_antisymm (le_sSup ⟨inferInstance, hg2⟩) hcore
  let eY : (Y ⧸ pCore 2 Y) ≃* g.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange g)
  have hcube (x : g.range) : x ^ 3 = 1 := by
    apply Subtype.ext
    exact Prod.ext (hgP x.property).1 (hgP x.property).2
  have hcomm (x y : g.range) : x * y = y * x := by
    apply Subtype.ext
    exact Prod.ext
      (cube_comm _ _ (hgP x.property).1 (hgP y.property).1)
      (cube_comm _ _ (hgP x.property).2 (hgP y.property).2)
  refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
  · intro x y
    apply eY.injective
    simpa only [map_mul] using hcomm (eY x) (eY y)
  · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    apply eY.injective
    simpa only [map_pow, map_one] using hcube (eY x)


private theorem complement_axis (A : Subgroup SymmetricThreeProduct.G) [A.Normal]
    (hp : IsPPerfect 2 A) (hc : 3 ^ (Nat.card A).factorization 3 = 3) :
    ∃ D : Subgroup SymmetricThreeProduct.G, D.Normal ∧ Nat.card D = 3 ∧
      A ⊔ D = SymmetricThreeProduct.threeCore.prod SymmetricThreeProduct.threeCore := by
  have hsup : SymmetricThreeProduct.leftThree ⊔ SymmetricThreeProduct.rightThree =
      SymmetricThreeProduct.threeCore.prod SymmetricThreeProduct.threeCore := by
    apply le_antisymm
    · exact sup_le (fun _ hx => ⟨hx.1, by rw [hx.2]; simp⟩)
        (fun _ hx => ⟨by rw [hx.1]; simp, hx.2⟩)
    · rintro ⟨a,b⟩ ⟨ha,hb⟩
      have h1 : (a,1) ∈ SymmetricThreeProduct.leftThree := ⟨ha, rfl⟩
      have h2 : (1,b) ∈ SymmetricThreeProduct.rightThree := ⟨rfl, hb⟩
      simpa using (SymmetricThreeProduct.leftThree ⊔ SymmetricThreeProduct.rightThree).mul_mem
        (mem_sup_left h1) (mem_sup_right h2)
  rcases SymmetricThreeProduct.normal_twoPerfect_threePart A hp hc with rfl | rfl
  · exact ⟨SymmetricThreeProduct.rightThree, (by unfold SymmetricThreeProduct.rightThree; infer_instance),
      SymmetricThreeProduct.card_rightThree, hsup⟩
  · exact ⟨SymmetricThreeProduct.leftThree, (by unfold SymmetricThreeProduct.leftThree; infer_instance),
      SymmetricThreeProduct.card_leftThree, (sup_comm _ _).trans hsup⟩

/-- Lift the other normal order-three axis through the genuine rank-two projection.
The lifted residual is normal in Y, S-invariant, and generates Y with A. -/
theorem rankTwoShadow_residual_complement {Y S A : Subgroup G}
    (hY : IsPPerfect 2 Y)
    (hquot : Nat.card (Y ⧸ pCore 2 Y) = 9)
    (hS : IsPGroup 2 S) (hSY : S ≤ normalizer (Y : Set G))
    (hshadow : RankTwoShadow Y S)
    (hAY : A ≤ Y) (hAn : (A.subgroupOf Y).Normal)
    (hAS : S ≤ normalizer (A : Set G))
    (hAp : IsPPerfect 2 A) (hA3 : 3 ^ (Nat.card A).factorization 3 = 3) :
    ∃ B : Subgroup G, B ≤ Y ∧ (B.subgroupOf Y).Normal ∧
      S ≤ normalizer (B : Set G) ∧ IsPPerfect 2 B ∧
      3 ^ (Nat.card B).factorization 3 = 3 ∧ Y = A ⊔ B := by
  obtain ⟨f,hf,hk,hYm⟩ := rankTwoShadow_map_data hY hquot hS hSY hshadow
  let H := Y ⊔ S
  have hYH : Y ≤ H := le_sup_left
  have hAH : A ≤ H := hAY.trans hYH
  let Yn := Y.subgroupOf H
  let An := A.subgroupOf H
  let : Yn.Normal := normal_subgroupOf_of_le_normalizer (sup_le Y.le_normalizer hSY)
  let : An.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le ((normal_subgroupOf_iff_le_normalizer hAY).mp hAn) hAS)
  have hYp : IsPPerfect 2 Yn := hY.of_surjective
    (subgroupOfEquivOfLe hYH).symm.toMonoidHom (subgroupOfEquivOfLe hYH).symm.surjective
  have hAmp : IsPPerfect 2 (An.map f) := (hAp.of_surjective
    (subgroupOfEquivOfLe hAH).symm.toMonoidHom (subgroupOfEquivOfLe hAH).symm.surjective).of_surjective
    (f.subgroupMap An) (f.subgroupMap_surjective An)
  let : (An.map f).Normal := Subgroup.Normal.map inferInstance f hf
  have hAm3 : 3 ^ (Nat.card (An.map f)).factorization 3 = 3 := by
    rw [threePart_map_of_twoGroup_kernel f hk,
      Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv]
    exact hA3
  obtain ⟨D,hDn,hD3,hAD⟩ := complement_axis (An.map f) hAmp hAm3
  let := hDn
  have hDP : D ≤ Yn.map f := by rw [hYm, ← hAD]; exact le_sup_right
  let P := Yn ⊓ D.comap f
  let : P.Normal := inferInstance
  have hPm : P.map f = D := by
    apply le_antisymm
    · rintro x ⟨y,hy,rfl⟩
      exact hy.2
    · intro x hx
      obtain ⟨y,hy,he⟩ := mem_map.mp (hDP hx)
      exact mem_map.mpr ⟨y,⟨hy,(show f y ∈ D from he.symm ▸ hx)⟩,he⟩
  let E := (pResidual 2 P).map P.subtype
  let : E.Normal := inferInstance
  have hEp : IsPPerfect 2 E := isPPerfect_embedded_pResidual 2 P
  have hEm : E.map f = D := by
    change ((pResidual 2 P).map P.subtype).map f = D
    rw [map_embedded_pResidual, hPm,
      (pResidual_eq_top_iff 2 D).mpr (odd_perfect (IsPGroup.of_card (n := 1) (by simpa using hD3))),
      ← MonoidHom.range_eq_map, range_subtype]
  have hEY : E ≤ Yn := (map_subtype_le _).trans inf_le_left
  have hE3 : 3 ^ (Nat.card E).factorization 3 = 3 := by
    rw [← threePart_map_of_twoGroup_kernel f hk E, hEm, hD3]
    norm_num
  have hgen : Yn = An ⊔ E := by
    apply le_antisymm
    · apply le_normal_of_isPPerfect_of_le_sup_pGroup Yn (An ⊔ E) f.ker hYp hk
      apply (le_comap_map f Yn).trans
      have hm : Yn.map f = (An ⊔ E).map f := by
        rw [Subgroup.map_sup, hEm, hAD]
        exact hYm
      rw [hm, comap_map_eq]
    · exact sup_le (fun _ hx => hAY hx) hEY
  let B := E.map H.subtype
  have hBY : B ≤ Y := by
    rintro x ⟨e,he,rfl⟩
    exact hEY he
  have hHB : H ≤ normalizer (B : Set G) := by
    apply le_normalizer_iff.mpr
    intro g hg b hb
    obtain ⟨e,he,rfl⟩ := mem_map.mp hb
    exact mem_map.mpr ⟨(⟨g,hg⟩ : H) * e * (⟨g,hg⟩ : H)⁻¹,
      (inferInstance : E.Normal).conj_mem e he ⟨g,hg⟩, rfl⟩
  refine ⟨B, hBY, normal_subgroupOf_of_le_normalizer (hYH.trans hHB),
    le_sup_right.trans hHB, hEp.of_surjective (H.subtype.subgroupMap E)
      (H.subtype.subgroupMap_surjective E), ?_, ?_⟩
  · rw [Nat.card_congr (E.equivMapOfInjective H.subtype H.subtype_injective).toEquiv.symm]
    exact hE3
  · have hm := congrArg (Subgroup.map H.subtype) hgen
    simpa only [Yn, An, Subgroup.map_sup, map_subgroupOf_eq_of_le hYH,
      map_subgroupOf_eq_of_le hAH] using hm


end CFSG.Quasithin.Chapter15.Section03.RankTwo
