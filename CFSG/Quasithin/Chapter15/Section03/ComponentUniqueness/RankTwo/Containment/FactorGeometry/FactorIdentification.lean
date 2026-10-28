module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.FactorIdentification.Kernel
public import Theory.GroupTheory.PResidual.NormalSubgroup.TwoGroupKernel
public import Theory.SpecificGroups.SymmetricThreeProduct.NormalThreeSubgroups

/-!
# Identifying the component factors with the plane actors

In the single-component branch of 15.3.40, both component residuals and both
plane actors are normal in Y₊ and invariant under S. Their images in the
actual quotient by O₂,Φ(Y₊S) are normal two-perfect subgroups of S₃ × S₃,
each with three-part three, so each image is one of its two order-three axes.
The kernel is a two-group by the order calculation in `Kernel`; normal
two-perfect subgroups with equal images therefore coincide. Generation of Y₊,
whose three-part is nine, forces the two factors to occupy different axes.

The exported pair is exactly the premise of `orient_component_plane`.
`PlaneActorPair` is an explicit input from the independent natural-action
construction. The Sylow wrapper derives relative normality of L in I from
the actual orbit equality and normalizer-index bound. Only the three-parts
of the two factors are used, as required by the source proof; the printed
stronger full-order assertion about the centralizing factor is unnecessary.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the first
paragraph of 15.3.40 on printed p.1138, using 15.3.36--39 on pp.1135--1138.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo
variable {G : Type*} [Group G] [Finite G]

/-- The two residual factors coincide, in one of the two orientations, with
the supplied plane actors. All four quotient directions and the lifting of
equality are proved from the source invariance, order, and quotient inputs. -/
theorem identify_component_factors_of_relative_normality
    {M Y Yplus L I S V V₁ V₂ : Subgroup G}
    (a : PlaneActorPair M Y Yplus S V V₁ V₂)
    (hLI : L ≤ I) [(L.subgroupOf I).Normal] (hYI : Yplus ≤ I)
    (hS : IsPGroup 2 S) (horbit : L = componentOrbit L S)
    (hSY : S ≤ normalizer (Yplus : Set G))
    (hSV₂ : S ≤ normalizer (V₂ : Set G))
    (hYV₂ : Yplus ≤ normalizer (V₂ : Set G))
    (hsplit : Yplus = componentFactor Yplus L ⊔ centralizingFactor Yplus L)
    (hthreeX : 3 ^ (Nat.card (componentFactor Yplus L)).factorization 3 = 3)
    (hthreeC : 3 ^ (Nat.card (centralizingFactor Yplus L)).factorization 3 = 3)
    (hquot : Nat.card (Yplus ⧸ pCore 2 Yplus) = 9)
    (hshadow : RankTwoShadow Yplus S) :
    (componentFactor Yplus L = a.right ∧
      centralizingFactor Yplus L = centralizingFactor Yplus V₂) ∨
    (componentFactor Yplus L = centralizingFactor Yplus V₂ ∧
      centralizingFactor Yplus L = a.right) := by
  classical
  let H := Yplus ⊔ S
  obtain ⟨e⟩ := hshadow
  let f : H →* SymmetricThreeProduct.G :=
    e.toMonoidHom.comp (QuotientGroup.mk' (twoFrattiniCore H))
  have hf : Function.Surjective f :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = twoFrattiniCore H := by
    ext x
    simp only [MonoidHom.mem_ker, f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      EmbeddingLike.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hk : IsPGroup 2 f.ker := hker ▸ rankTwoShadow_kernel_isTwoGroup hquot hS hSY e
  let im (N : Subgroup G) := (N.subgroupOf H).map f
  let Good (N : Subgroup G) : Prop := N ≤ Yplus ∧ (N.subgroupOf Yplus).Normal ∧
    S ≤ normalizer (N : Set G) ∧ IsPPerfect 2 N ∧
    3 ^ (Nat.card N).factorization 3 = 3
  have good_normal (N : Subgroup G) (hN : Good N) : (N.subgroupOf H).Normal :=
    normal_subgroupOf_of_le_normalizer
      (sup_le ((normal_subgroupOf_iff_le_normalizer hN.1).mp hN.2.1) hN.2.2.1)
  have good_perfect (N : Subgroup G) (hN : Good N) : IsPPerfect 2 (N.subgroupOf H) :=
    hN.2.2.2.1.of_surjective (subgroupOfEquivOfLe (show N ≤ H from hN.1.trans le_sup_left)).symm.toMonoidHom
      (subgroupOfEquivOfLe (show N ≤ H from hN.1.trans le_sup_left)).symm.surjective
  have direction (N : Subgroup G) (hN : Good N) :
      im N = SymmetricThreeProduct.leftThree ∨ im N = SymmetricThreeProduct.rightThree := by
    let : (im N).Normal := (good_normal N hN).map f hf
    apply SymmetricThreeProduct.normal_twoPerfect_threePart _
      ((good_perfect N hN).of_surjective (f.subgroupMap _) (f.subgroupMap_surjective _))
    rw [threePart_map_of_twoGroup_kernel f hk,
      Nat.card_congr (subgroupOfEquivOfLe (show N ≤ H from hN.1.trans le_sup_left)).toEquiv]
    exact hN.2.2.2.2
  have lift (N K : Subgroup G) (hN : Good N) (hK : Good K) (he : im N = im K) : N = K := by
    let : (N.subgroupOf H).Normal := good_normal N hN
    let : (K.subgroupOf H).Normal := good_normal K hK
    have heq := eq_of_normal_twoPerfect_of_map_eq f hk _ _
      (good_perfect N hN) (good_perfect K hK) he
    have hm := congrArg (Subgroup.map H.subtype) heq
    simpa only [map_subgroupOf_eq_of_le (show N ≤ H from hN.1.trans le_sup_left),
      map_subgroupOf_eq_of_le (show K ≤ H from hK.1.trans le_sup_left)] using hm
  obtain ⟨hXn, hCn, hXs, hCs⟩ :=
    component_factors_normal_invariant hLI hYI hSY horbit
  obtain ⟨hAn, hAs⟩ := plane_left_actor_normal_invariant hYV₂ hSY hSV₂
  have hX : Good (componentFactor Yplus L) :=
    ⟨componentFactor_le_left _ _, hXn, hXs, componentFactor_isPPerfect _ _, hthreeX⟩
  have hC : Good (centralizingFactor Yplus L) :=
    ⟨centralizingFactor_le_left _ _, hCn, hCs, centralizingFactor_isPPerfect _ _, hthreeC⟩
  have hA : Good (centralizingFactor Yplus V₂) :=
    ⟨centralizingFactor_le_left _ _, hAn, hAs, centralizingFactor_isPPerfect _ _, a.left_three_part⟩
  have hB : Good a.right :=
    ⟨a.right_le.trans inf_le_left, a.right_normal, a.right_invariant,
      a.right_perfect, a.right_three_part⟩
  have unequal (N K : Subgroup G) (hN : Good N) (hgen : Yplus = N ⊔ K) : N ≠ K := by
    intro he
    have hy : Yplus = N := by simpa only [← he, sup_idem] using hgen
    have h9 := threePart_of_twoCore_quotient_nine hquot
    rw [hy, hN.2.2.2.2] at h9
    norm_num at h9
  have hAB := unequal _ _ hA a.generate
  have hXC := unequal _ _ hX hsplit
  have dichotomy (N : Subgroup G) (hN : Good N) :
      N = centralizingFactor Yplus V₂ ∨ N = a.right := by
    rcases direction N hN with hn | hn <;>
      rcases direction _ hA with ha | ha <;>
      rcases direction _ hB with hb | hb <;>
      first
      | exact Or.inl (lift _ _ hN hA (hn.trans ha.symm))
      | exact Or.inr (lift _ _ hN hB (hn.trans hb.symm))
      | exact (hAB (lift _ _ hA hB (ha.trans hb.symm))).elim
  rcases dichotomy _ hX with hx | hx <;> rcases dichotomy _ hC with hc | hc
  · exact (hXC (hx.trans hc.symm)).elim
  · exact Or.inr ⟨hx, hc⟩
  · exact Or.inl ⟨hx, hc⟩
  · exact (hXC (hx.trans hc.symm)).elim

/-- The factor-pair identification with relative normality discharged from
orbit equality, the source normalizer-index bound, and the actual Sylow
subgroup of I. The actor pair is the independently constructed action output. -/
theorem identify_component_factors_of_planeActors
    {M Y Yplus L I S V V₁ V₂ : Subgroup G}
    (a : PlaneActorPair M Y Yplus S V V₁ V₂)
    (hLI : L ≤ I) (hYI : Yplus ≤ I)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hindex : (normalizer (L.subgroupOf I : Set I)).index ≤ 2)
    (horbit : L = componentOrbit L S)
    (hSY : S ≤ normalizer (Yplus : Set G))
    (hSV₂ : S ≤ normalizer (V₂ : Set G))
    (hYV₂ : Yplus ≤ normalizer (V₂ : Set G))
    (hsplit : Yplus = componentFactor Yplus L ⊔ centralizingFactor Yplus L)
    (hthreeX : 3 ^ (Nat.card (componentFactor Yplus L)).factorization 3 = 3)
    (hthreeC : 3 ^ (Nat.card (centralizingFactor Yplus L)).factorization 3 = 3)
    (hquot : Nat.card (Yplus ⧸ pCore 2 Yplus) = 9)
    (hshadow : RankTwoShadow Yplus S) :
    (componentFactor Yplus L = a.right ∧
      centralizingFactor Yplus L = centralizingFactor Yplus V₂) ∨
    (componentFactor Yplus L = centralizingFactor Yplus V₂ ∧
      centralizingFactor Yplus L = a.right) := by
  let : (L.subgroupOf I).Normal := relative_normal_of_componentOrbit_eq hLI P hP hindex horbit
  have hS : IsPGroup 2 S := hP ▸ P.isPGroup'.map I.subtype
  exact identify_component_factors_of_relative_normality a hLI hYI hS horbit hSY hSV₂ hYV₂
    hsplit hthreeX hthreeC hquot hshadow

end CFSG.Quasithin.Chapter15.Section03.RankTwo
