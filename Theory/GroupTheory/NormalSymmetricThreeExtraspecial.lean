module

public import Theory.GroupTheory.NormalSymmetricThreeMarked
public import Theory.GroupTheory.NormalSymmetricThreePairRank.Inner
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms
public import Theory.ThreeSubgroups
public import Theory.SpecificGroups.SymmetricThreeProduct.NormalThreeSubgroups
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Normal symmetric-three subgroups in a group with a normal three-group

A normal S3 cannot coexist with an extraspecial normal three-group N and a
2-group quotient by N. Its cubic residual lies in N, is centralized by N,
and is forced into the center of S3 by the Three Subgroups Lemma.

For S3 × S3 it suffices that N has center of order three. Conjugation by a
three-group fixes the two normal cubic axes, because their orbits have size
at most two. Both axes would then lie in the order-three center of N.

Source application: Aschbacher–Smith, final proof of15.3.1, p.1155, comparing
the extraspecial F.6.18 row with B.5.6. These are intrinsic normal-subgroup
lemmas; the actual offender-action application is kept in Chapter15.
-/

public section
open Subgroup

namespace Theory.GroupTheory.NormalSymmetricThreeExtraspecial

variable {G : Type*} [Group G] [Finite G]

/-- A three-subgroup centralizes every normal subgroup of order three. -/
private theorem three_subgroup_centralizes_normal_three
    (N R : Subgroup G) [R.Normal] (hN : IsPGroup 3 N)
    (hR : Nat.card R = 3) : N ≤ centralizer (R : Set G) := by
  let : IsCyclic R := isCyclic_of_prime_card hR
  let f : G →* MulAut R := MulAut.conjNormal
  have htwo : IsPGroup 2 (MulAut R) := IsPGroup.of_card (n := 1) (by
    rw [IsCyclic.card_mulAut, hR]
    decide)
  have hthree : IsPGroup 3 (N.map f) := hN.map f
  have hbot : N.map f = ⊥ := by
    have hdis := IsPGroup.disjoint_of_coprime hthree
      (htwo.to_subgroup (N.map f)) (by decide : Nat.Coprime 3 2)
    exact disjoint_self.mp hdis
  intro n hn r hr
  have hfn : f n = 1 := by
    have hm := mem_map_of_mem f hn
    rw [hbot, mem_bot] at hm
    exact hm
  have hc := congrArg (fun a : MulAut R => ((a ⟨r, hr⟩ : R) : G)) hfn
  change n * r * n⁻¹ = r at hc
  exact (mul_inv_eq_iff_eq_mul.mp hc).symm

/-- A normal S3 cannot coexist with a normal extraspecial 3-group whose
quotient is a 2-group. No order-27 or exponent-three restriction is needed. -/
theorem no_normal_symmetricThree
    (N I : Subgroup G) [N.Normal] [I.Normal] [IsExtraspecial 3 N]
    (hquot : IsPGroup 2 (G ⧸ N)) (e : I ≃* Equiv.Perm (Fin 3)) : False := by
  let R := Theory.GroupTheory.NormalSymmetricThreeMarked.residual I
  have hR : Nat.card R = 3 :=
    Theory.GroupTheory.NormalSymmetricThreeMarked.residual_card I e
  have hRN : R ≤ N :=
    (map_pResidual_le 2 I.subtype).trans (sInf_le ⟨inferInstance, hquot⟩)
  have hRI : R ≤ I := map_subtype_le _
  have hNR : N ≤ centralizer (R : Set G) :=
    three_subgroup_centralizes_normal_three N R (IsExtraspecial.isPGroup 3 N) hR
  have hcomm : ⁅N, I⁆ ≤ R := by
    apply (le_inf (commutator_le_right N I) ?_).trans
      (Theory.GroupTheory.NormalSymmetricThreeMarked.inf_centralizer_residual_le I e)
    exact (commutator_mono hNR le_rfl).trans (commutator_le_left _ I)
  have htriple : ⁅⁅N, I⁆, N⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact hcomm.trans (le_centralizer_iff.mp hNR)
  have hderived : ⁅⁅N, N⁆, I⁆ = ⊥ :=
    commutator_commutator_eq_bot_of_rotate htriple
      (by simpa only [commutator_comm I N] using htriple)
  let Z := (center N).map N.subtype
  have hRZ : R ≤ Z := by
    intro r hr
    refine ⟨⟨r, hRN hr⟩, mem_center_iff.mpr ?_, rfl⟩
    intro n
    exact Subtype.ext ((hNR n.property r hr).symm)
  have hZe : Z = R := eq_of_le_of_card_ge hRZ (by
    rw [card_map_of_injective N.subtype_injective, IsExtraspecial.center_order_p 3 N, hR]) |>.symm
  have hZI : Z ≤ centralizer (I : Set G) := by
    change (center N).map N.subtype ≤ centralizer (I : Set G)
    rw [← IsExtraspecial.commutator_eq_center (p := 3), map_subtype_commutator]
    exact commutator_eq_bot_iff_le_centralizer.mp hderived
  have hRbot : R = ⊥ := by
    apply le_bot_iff.mp
    intro r hr
    change r = 1
    let rI : I := ⟨r, hRI hr⟩
    have hz : e rI = 1 :=
      Theory.GroupTheory.NormalSymmetricThreePairRank.symmetricThree_center_trivial _ (by
        intro y
        have he := (hZI (hZe.symm ▸ hr)) (e.symm y) (e.symm y).property
        have hi : e.symm y * rI = rI * e.symm y := Subtype.ext he
        simpa only [map_mul, e.apply_symm_apply] using congrArg e hi)
    exact congrArg Subtype.val (e.map_eq_one_iff.mp hz)
  rw [hRbot, card_bot] at hR
  omega


private theorem threeGroup_isTwoPerfect {A : Type*} [Group A]
    (h : IsPGroup 3 A) : IsPPerfect 2 A := by
  intro K hK hk
  let := hK
  have hd := IsPGroup.disjoint_of_coprime
    ((h.to_quotient K).to_subgroup ⊤) (hk.to_subgroup ⊤)
    (by decide : Nat.Coprime 3 2)
  apply top_unique
  intro a _
  apply (QuotientGroup.eq_one_iff a).mp
  exact Subgroup.disjoint_def.mp hd (mem_top _) (mem_top _)

private theorem normal_card_three_axis (A : Subgroup SymmetricThreeProduct.G)
    [A.Normal] (h : Nat.card A = 3) :
    A = SymmetricThreeProduct.leftThree ∨ A = SymmetricThreeProduct.rightThree := by
  apply SymmetricThreeProduct.normal_twoPerfect_threePart A
    (threeGroup_isTwoPerfect (IsPGroup.of_card (n := 1) (by simpa using h)))
  rw [h]
  norm_num [Nat.Prime.factorization_self Nat.prime_three]

open scoped Pointwise

private theorem three_action_preserves_cubic_axis {A : Type*} [Group A] [Finite A]
    (hA : IsPGroup 3 A) (f : A →* MulAut SymmetricThreeProduct.G)
    (R : Subgroup SymmetricThreeProduct.G) [R.Normal] (hR : Nat.card R = 3)
    (a : A) : R.map (f a).toMonoidHom = R := by
  classical
  let : MulAction A (Subgroup SymmetricThreeProduct.G) :=
    MulAction.compHom (Subgroup SymmetricThreeProduct.G) f
  have horbit : MulAction.orbit A R ⊆
      ({SymmetricThreeProduct.leftThree, SymmetricThreeProduct.rightThree} :
        Set (Subgroup SymmetricThreeProduct.G)) := by
    intro T hT
    obtain ⟨a, rfl⟩ := MulAction.mem_orbit_iff.mp hT
    change R.map (f a).toMonoidHom ∈ _
    let : (R.map (f a).toMonoidHom).Normal := Subgroup.Normal.map inferInstance _ (f a).surjective
    have hc : Nat.card (R.map (f a).toMonoidHom) = 3 := by
      rw [card_map_of_injective (f a).injective, hR]
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      normal_card_three_axis _ hc
  have hsmall : Nat.card (MulAction.orbit A R) ≤ 2 := by
    apply (Set.ncard_le_ncard horbit (Set.toFinite _)).trans
    simpa using Set.ncard_insert_le SymmetricThreeProduct.leftThree
      ({SymmetricThreeProduct.rightThree} : Set (Subgroup SymmetricThreeProduct.G))
  obtain ⟨k, hk⟩ := hA.card_orbit R
  have hk0 : k = 0 := by
    by_contra hn
    have hp : 3 ^ 1 ≤ 3 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
    rw [hk] at hsmall
    norm_num at hp
    omega
  have hc : Nat.card (MulAction.orbit A R) = 1 := by simpa [hk0] using hk
  let : Fintype (MulAction.orbit A R) := Fintype.ofFinite _
  have hf : R ∈ MulAction.fixedPoints A (Subgroup SymmetricThreeProduct.G) :=
    MulAction.mem_fixedPoints_iff_card_orbit_eq_one.mpr (by
      simpa only [Nat.card_eq_fintype_card] using hc)
  exact MulAction.mem_fixedPoints.mp hf a


private theorem three_subgroup_centralizes_normalized_three
    (N R : Subgroup G) (hN : IsPGroup 3 N) (hR : Nat.card R = 3)
    (hn : N ≤ normalizer (R : Set G)) : N ≤ centralizer (R : Set G) := by
  let : IsCyclic R := isCyclic_of_prime_card hR
  let f : N →* MulAut R := R.normalizerMonoidHom.comp (inclusion hn)
  have htwo : IsPGroup 2 (MulAut R) := IsPGroup.of_card (n := 1) (by
    rw [IsCyclic.card_mulAut, hR]
    decide)
  have hthree : IsPGroup 3 f.range := hN.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hbot : f.range = ⊥ := disjoint_self.mp
    (IsPGroup.disjoint_of_coprime hthree (htwo.to_subgroup f.range)
      (by decide : Nat.Coprime 3 2))
  intro n hn r hr
  have hf : f ⟨n, hn⟩ = 1 := by
    have hm : f ⟨n, hn⟩ ∈ f.range := ⟨⟨n, hn⟩, rfl⟩
    rwa [hbot, mem_bot] at hm
  have hc := congrArg (fun a : MulAut R => ((a ⟨r, hr⟩ : R) : G)) hf
  change n * r * n⁻¹ = r at hc
  exact (mul_inv_eq_iff_eq_mul.mp hc).symm

private theorem pair_cubic_axis_le_center
    (N I : Subgroup G) [N.Normal] [I.Normal] (hN : IsPGroup 3 N)
    (hquot : IsPGroup 2 (G ⧸ N)) (e : I ≃* SymmetricThreeProduct.G)
    (R : Subgroup SymmetricThreeProduct.G) [R.Normal] (hR : Nat.card R = 3) :
    R.map (I.subtype.comp e.symm.toMonoidHom) ≤ (center N).map N.subtype := by
  let F : SymmetricThreeProduct.G →* G := I.subtype.comp e.symm.toMonoidHom
  let C := R.map F
  have hF : Function.Injective F := I.subtype_injective.comp e.symm.injective
  have hC : Nat.card C = 3 := by
    change Nat.card (R.map F) = 3
    rw [card_map_of_injective hF, hR]
  have hp : IsPGroup 3 C := IsPGroup.of_card (n := 1) (by simpa using hC)
  have hCN : C ≤ N :=
    (le_pResidual_of_isPPerfect C (threeGroup_isTwoPerfect hp)).trans
      (sInf_le ⟨inferInstance, hquot⟩)
  let f : N →* MulAut SymmetricThreeProduct.G :=
    (MulAut.congr e).toMonoidHom.comp
      ((MulAut.conjNormal : G →* MulAut I).comp N.subtype)
  have hn : N ≤ normalizer (C : Set G) := by
    apply le_normalizer_iff.mpr
    intro n hn x hx
    obtain ⟨r, hr, rfl⟩ := hx
    have hm : f ⟨n, hn⟩ r ∈ R := by
      rw [← three_action_preserves_cubic_axis hN f R hR ⟨n, hn⟩]
      exact mem_map_of_mem _ hr
    refine ⟨f ⟨n, hn⟩ r, hm, ?_⟩
    simp [F, f, MulAut.congr_apply]
  have hc := three_subgroup_centralizes_normalized_three N C hN hC hn
  intro r hr
  refine ⟨⟨r, hCN hr⟩, mem_center_iff.mpr ?_, rfl⟩
  intro n
  exact Subtype.ext ((hc n.property r hr).symm)

/-- The pair case needs only that the normal three-group has center of
order three. Its two normal cubic directions cannot both fit there. -/
theorem no_normal_symmetricThreePair
    (N I : Subgroup G) [N.Normal] [I.Normal] (hN : IsPGroup 3 N)
    (hcenter : Nat.card (center N) = 3) (hquot : IsPGroup 2 (G ⧸ N))
    (e : I ≃* SymmetricThreeProduct.G) : False := by
  let F : SymmetricThreeProduct.G →* G := I.subtype.comp e.symm.toMonoidHom
  have hF : Function.Injective F := I.subtype_injective.comp e.symm.injective
  let : SymmetricThreeProduct.leftThree.Normal := by
    unfold SymmetricThreeProduct.leftThree
    infer_instance
  let : SymmetricThreeProduct.rightThree.Normal := by
    unfold SymmetricThreeProduct.rightThree
    infer_instance
  have hl := pair_cubic_axis_le_center N I hN hquot e
    SymmetricThreeProduct.leftThree SymmetricThreeProduct.card_leftThree
  have hr := pair_cubic_axis_le_center N I hN hquot e
    SymmetricThreeProduct.rightThree SymmetricThreeProduct.card_rightThree
  have hle : SymmetricThreeProduct.leftThree.map F = (center N).map N.subtype :=
    eq_of_le_of_card_ge hl (by
      rw [card_map_of_injective hF, SymmetricThreeProduct.card_leftThree,
        card_map_of_injective N.subtype_injective, hcenter])
  have hre : SymmetricThreeProduct.rightThree.map F = (center N).map N.subtype :=
    eq_of_le_of_card_ge hr (by
      rw [card_map_of_injective hF, SymmetricThreeProduct.card_rightThree,
        card_map_of_injective N.subtype_injective, hcenter])
  have he : SymmetricThreeProduct.leftThree = SymmetricThreeProduct.rightThree :=
    map_injective hF (hle.trans hre.symm)
  let x : SymmetricThreeProduct.G :=
    (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2, 1)
  have hx : x ∈ SymmetricThreeProduct.leftThree := by decide
  have hn : x ∉ SymmetricThreeProduct.rightThree := by decide
  exact hn (he ▸ hx)


end Theory.GroupTheory.NormalSymmetricThreeExtraspecial
