module
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import Theory.GroupTheory.OrderNineAutomorphisms
public import Theory.GroupTheory.NormalSymmetricThreePairRank.Inner
public import Mathlib.GroupTheory.Nilpotent

/-!
# Normal actors above a nonquasisimple C-component

A nontrivial image of a finite C-component remains a C-component: its proper
internal kernel is solvable. If the quotient over that image is a two-group,
every ordinary component lies in it. Minimality then excludes all ordinary
components when the image is nonquasisimple.

A perfect subgroup centralizes every normal actor with a characteristic
self-centralizing subgroup of order three or nine. Its action on that small
subgroup is solvable, and the three-subgroup lemma propagates centralization.
For a centerless normal actor, this embeds it in the quotient over the perfect
subgroup; a two-group quotient and trivial two-core force the actor to vanish.

In S₃ and S₃×S₃, the cube-one elements form the required characteristic
subgroup. Six-element permutation calculations prove the one-factor facts;
the product argument allows automorphisms interchanging its factors.

Source: Aschbacher–Smith, A.3.3, printed pp.42–43, and the solvable cases
of B.5.6, printed p.105. The actual offender-action application belongs to
Chapter 13's NonquasisimpleFactorization module.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory.NonquasisimpleAction
variable {G D : Type*} [Group G] [Group D]

private theorem perfect_hom_eq_one {E F : Type*} [Group E] [Group F]
    [Group.IsPerfect E] [Group.IsSolvable F] (f : E →* F) : f = 1 := by
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hb : f.range = ⊥ := by
    by_contra hb
    let : Nontrivial f.range := (nontrivial_iff_ne_bot _).mpr hb
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  exact MonoidHom.range_eq_bot_iff.mp hb

/-- A nontrivial homomorphic image of a finite C-component is a C-component.
Only the kernel inside the component is required to be solvable. -/
theorem ccomponent_image_or_bot [Finite G] {K : Subgroup G} (hK : K.IsCComponent)
    (f : G →* D) (hf : Function.Surjective f) :
    K.map f = ⊥ ∨ (K.map f).IsCComponent := by
  by_cases hb : K.map f = ⊥
  · exact Or.inl hb
  right
  let g := f.subgroupMap K
  have hproper : g.ker ≠ ⊤ := by
    intro ht
    apply hb
    apply (Subgroup.eq_bot_iff_forall _).mpr
    rintro _ ⟨x, hx, rfl⟩
    have hm : (⟨x, hx⟩ : K) ∈ g.ker := ht ▸ mem_top _
    exact congrArg Subtype.val hm
  let : Group.IsSolvable g.ker :=
    hK.isSolvable_of_subnormal_lt_top (inferInstance : g.ker.Normal).isSubnormal hproper
  have htop : (⊤ : Subgroup K).IsCComponent := by
    simpa using hK.subgroupOf (le_refl K)
  have hm := cComponent_map_of_solvable_ker htop g (f.subgroupMap_surjective K)
  rw [map_top_of_surjective _ (f.subgroupMap_surjective K)] at hm
  simpa only [← MonoidHom.range_eq_map, range_subtype] using
    hm.map_subtype (hK.subnormal.map hf)

/-- A nonquasisimple C-component with a two-group supplement leaves no
ordinary component anywhere in the group. -/
theorem no_ordinary_components [Finite D] (K : Subgroup D) [K.Normal]
    (hK : K = ⊥ ∨ K.IsCComponent) (hq : IsPGroup 2 (D ⧸ K))
    (hnq : ¬ IsQuasisimple K) : ∀ L : Subgroup D, ¬ IsComponent D L := by
  let : Group.IsNilpotent (D ⧸ K) := hq.isNilpotent
  intro L hL
  let := hL.2
  have hLK : L ≤ K := le_of_isPerfect_of_solvable_quotient L K
  rcases hK with hb | hK
  · exact hL.isCComponent.ne_bot (eq_bot_iff.mpr (hb ▸ hLK))
  · exact hnq ((hL.isCComponent.eq_of_le hK hLK) ▸ hL.2)

/-- Centralization of a normal subgroup by the component forces that
subgroup into the two-core when its intrinsic center is trivial. -/
theorem normal_eq_bot_of_centerless [Finite D] (K N : Subgroup D)
    [K.Normal] [N.Normal] (hq : IsPGroup 2 (D ⧸ K))
    (hcore : pCore 2 D = ⊥) (hZ : center N = ⊥)
    (hc : K ≤ centralizer (N : Set D)) : N = ⊥ := by
  let f := (QuotientGroup.mk' K).comp N.subtype
  have hi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro n hn
    have hnK : (n : D) ∈ K := (QuotientGroup.eq_one_iff _).mp hn
    have hnZ : n ∈ center N := by
      apply mem_center_iff.mpr
      intro x
      exact Subtype.ext (hc hnK x x.property)
    simpa only [hZ, mem_bot] using hnZ
  have hp : IsPGroup 2 N := hq.of_injective f hi
  exact eq_bot_iff.mpr (hcore ▸ (show N ≤ pCore 2 D from le_sSup ⟨inferInstance, hp⟩))

private theorem automorphisms_solvable {E : Type*} [Group E] [Finite E]
    (hc : Nat.card E = 3 ∨ Nat.card E = 9) : Group.IsSolvable (MulAut E) := by
  rcases hc with hc | hc
  · let : IsCyclic E := isCyclic_of_prime_card hc
    exact Group.isSolvable_of_isSolvable_injective
      (f := (IsCyclic.mulAutMulEquiv E).toMonoidHom) (IsCyclic.mulAutMulEquiv E).injective
  · exact MulAut.isSolvable_of_card_nine hc

/-- A small characteristic self-centralizing subgroup forces every perfect
ambient subgroup to centralize the normal actor. -/
theorem perfect_centralizes_small_actor [Finite D] (N : Subgroup D) [N.Normal]
    (R : Subgroup N) [R.Characteristic]
    (hR : Nat.card R = 3 ∨ Nat.card R = 9)
    (hC : centralizer (R : Set N) ≤ R)
    (K : Subgroup D) [Group.IsPerfect K] : K ≤ centralizer (N : Set D) := by
  let U := R.map N.subtype
  let : U.Normal := ConjAct.normal_of_characteristic_of_normal
  have hcard : Nat.card U = 3 ∨ Nat.card U = 9 := by
    simpa only [U, card_map_of_injective N.subtype_injective] using hR
  let : Group.IsSolvable (MulAut U) := automorphisms_solvable hcard
  let f : K →* MulAut U := (MulAut.conjNormal : D →* MulAut U).comp K.subtype
  have hf := perfect_hom_eq_one f
  have hKU : K ≤ centralizer (U : Set D) := by
    intro k hk u hu
    have he := congrArg (fun g : K →* MulAut U => ((g ⟨k, hk⟩ ⟨u, hu⟩ : U) : D)) hf
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hNC : N ⊓ centralizer (U : Set D) ≤ U := by
    rintro n ⟨hn, hc⟩
    refine ⟨⟨n, hn⟩, hC ?_, rfl⟩
    intro r hr
    exact Subtype.ext (hc r (mem_map_of_mem _ hr))
  have hcomm : ⁅N, K⁆ ≤ U :=
    (le_inf (commutator_le_left N K)
      ((commutator_mono le_rfl hKU).trans (commutator_le_right N _))).trans hNC
  apply le_centralizer_iff.mpr
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply commutator_eq_bot_of_iterated_eq_bot N K
  exact le_bot_iff.mp ((commutator_mono hcomm le_rfl).trans
    (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hKU)).le)

end Theory.GroupTheory.NonquasisimpleAction

open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory.NonquasisimpleAction

private structure CubicFacts (D : Type*) [Group D] : Prop where
  closed : ∀ x y : D, x ^ 3 = 1 → y ^ 3 = 1 → (x * y) ^ 3 = 1
  card : Nat.card {x : D // x ^ 3 = 1} = 3 ∨ Nat.card {x : D // x ^ 3 = 1} = 9
  centralizer : ∀ x : D, (∀ y : D, y ^ 3 = 1 → y * x = x * y) → x ^ 3 = 1
  center : ∀ x : D, (∀ y : D, y * x = x * y) → x = 1

private def cubicSubgroup {D : Type*} [Group D] (h : CubicFacts D) : Subgroup D where
  carrier := {x | x ^ 3 = 1}
  one_mem' := one_pow 3
  mul_mem' := h.closed _ _
  inv_mem' := by
    intro x hx
    change x⁻¹ ^ 3 = 1
    rw [inv_pow, hx, inv_one]

private theorem cubic_characteristic {D : Type*} [Group D] (h : CubicFacts D) :
    (cubicSubgroup h).Characteristic := by
  apply characteristic_iff_map_eq.mpr
  intro e
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change e y ^ 3 = 1
    change y ^ 3 = 1 at hy
    rw [← map_pow, hy, map_one]
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    change e.symm x ^ 3 = 1
    change x ^ 3 = 1 at hx
    rw [← map_pow, hx, map_one]

private theorem CubicFacts.of_equiv {D E : Type*} [Group D] [Group E]
    (e : D ≃* E) (h : CubicFacts E) : CubicFacts D := by
  let c : {x : D // x ^ 3 = 1} ≃ {x : E // x ^ 3 = 1} :=
    { toFun := fun x => ⟨e x, by rw [← map_pow, x.property, map_one]⟩
      invFun := fun x => ⟨e.symm x, by rw [← map_pow, x.property, map_one]⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x)
      right_inv := fun x => Subtype.ext (e.apply_symm_apply x) }
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hx hy
    apply e.injective
    rw [map_pow, map_mul, map_one]
    exact h.closed _ _ (by rw [← map_pow, hx, map_one]) (by rw [← map_pow, hy, map_one])
  · simpa only [Nat.card_congr c] using h.card
  · intro x hx
    apply e.injective
    rw [map_pow, map_one]
    apply h.centralizer
    intro y hy
    have hp : e.symm y ^ 3 = 1 := by rw [← map_pow, hy, map_one]
    simpa only [map_mul, e.apply_symm_apply] using congrArg e (hx (e.symm y) hp)
  · intro x hx
    apply e.injective
    rw [map_one]
    apply h.center
    intro y
    simpa only [map_mul, e.apply_symm_apply] using congrArg e (hx (e.symm y))

private theorem symmetricThree_cubicFacts : CubicFacts (Equiv.Perm (Fin 3)) where
  closed := by decide +kernel
  card := Or.inl (by rw [Nat.card_eq_fintype_card]; decide)
  centralizer := by decide +kernel
  center := Theory.GroupTheory.NormalSymmetricThreePairRank.symmetricThree_center_trivial

private theorem pair_cubicFacts : CubicFacts (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) where
  closed := by
    intro x y hx hy
    exact Prod.ext
      (symmetricThree_cubicFacts.closed _ _ (congrArg Prod.fst hx) (congrArg Prod.fst hy))
      (symmetricThree_cubicFacts.closed _ _ (congrArg Prod.snd hx) (congrArg Prod.snd hy))
  card := Or.inr (by rw [Nat.card_eq_fintype_card]; decide)
  centralizer := by
    intro x hx
    apply Prod.ext
    · apply symmetricThree_cubicFacts.centralizer
      intro y hy
      exact congrArg Prod.fst (hx (y, 1) (Prod.ext hy (one_pow 3)))
    · apply symmetricThree_cubicFacts.centralizer
      intro y hy
      exact congrArg Prod.snd (hx (1, y) (Prod.ext (one_pow 3) hy))
  center := by
    intro x hx
    exact Prod.ext
      (symmetricThree_cubicFacts.center _ (fun y => congrArg Prod.fst (hx (y, 1))))
      (symmetricThree_cubicFacts.center _ (fun y => congrArg Prod.snd (hx (1, y))))

private theorem small_actor_eq_bot {D : Type*} [Group D] [Finite D]
    (K N : Subgroup D) [K.Normal] [N.Normal] [Group.IsPerfect K]
    (hq : IsPGroup 2 (D ⧸ K)) (hcore : pCore 2 D = ⊥) (h : CubicFacts N) : N = ⊥ := by
  let R := cubicSubgroup h
  let : R.Characteristic := cubic_characteristic h
  apply normal_eq_bot_of_centerless K N hq hcore
  · apply (Subgroup.eq_bot_iff_forall _).mpr
    intro n hn
    exact h.center n (mem_center_iff.mp hn)
  · apply perfect_centralizes_small_actor N R h.card _ K
    intro n hn
    exact h.centralizer n hn

/-- The normal S₃ branch is impossible in a two-reduced group that has a
perfect normal subgroup with two-group quotient. -/
theorem normal_symmetricThree_eq_bot {D : Type*} [Group D] [Finite D]
    (K N : Subgroup D) [K.Normal] [N.Normal] [Group.IsPerfect K]
    (hq : IsPGroup 2 (D ⧸ K)) (hcore : pCore 2 D = ⊥)
    (e : N ≃* Equiv.Perm (Fin 3)) : N = ⊥ :=
  small_actor_eq_bot K N hq hcore (symmetricThree_cubicFacts.of_equiv e)

/-- The normal S₃×S₃ branch uses its intrinsic characteristic cubic subgroup
of order nine. No preservation of the two coordinate factors is assumed. -/
theorem normal_symmetricThreePair_eq_bot {D : Type*} [Group D] [Finite D]
    (K N : Subgroup D) [K.Normal] [N.Normal] [Group.IsPerfect K]
    (hq : IsPGroup 2 (D ⧸ K)) (hcore : pCore 2 D = ⊥)
    (e : N ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) : N = ⊥ :=
  small_actor_eq_bot K N hq hcore (pair_cubicFacts.of_equiv e)

end Theory.GroupTheory.NonquasisimpleAction
