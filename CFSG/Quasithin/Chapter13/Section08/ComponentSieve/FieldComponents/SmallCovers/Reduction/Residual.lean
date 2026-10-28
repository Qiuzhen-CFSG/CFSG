module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Basic
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Theory.GroupTheory.CentralPChiefCore
public import Theory.GroupTheory.PrimeOrderLift

/-!
# The literal central-cover residual

For a finite group K whose two-core quotient has center of order three,
Y = O²(O₂,Z(K)) is nontrivial and solvable. It is two-perfect, and each
of its odd-order elements has order one or three: the map to the center
has a two-group kernel. Consequently the order-three elements generate Y.
The universal solvable-overgroup conclusion of 13.8.13 places Y in M,
and the actual theta identity of 13.7.3(9) then places it in L₁.

The last deduction uses the earlier local catalogue of proper nontrivial
T-invariant two-perfect subgroups. It excludes L₀ using the proved
normalizer argument from Basic. Excluding Y = L₁ is deliberately still a
premise here; it needs the actual K₁ and the Dynkin-action alternative.
Neither this module nor its last theorem asserts that exclusion.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
13.7.5 proof, printed p.938, and 13.8.21(2), printed p.956 (PDF p.973).
Center order three is the consequence needed from the genuine cover
models. No split product is used as a cover.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The residual is taken inside the literal central preimage. -/
theorem coverResidual_le_centralPreimage :
    coverResidual G ≤ centralPreimage (pCore 2 G) := map_subtype_le _

theorem coverResidual_isPPerfect : IsPPerfect 2 (coverResidual G) :=
  isPPerfect_embedded_pResidual 2 (centralPreimage (pCore 2 G))

theorem coverResidualIn_isPPerfect (K : Subgroup G) :
    IsPPerfect 2 (coverResidualIn K) := by
  exact (coverResidual_isPPerfect (G := K)).of_surjective
    (K.subtype.subgroupMap (coverResidual K)) (K.subtype.subgroupMap_surjective _)

/-- The residual maps onto the entire cubic center, not merely into it. -/
theorem coverResidual_map_center
    (hcenter : Nat.card (center (G ⧸ pCore 2 G)) = 3) :
    (coverResidual G).map (QuotientGroup.mk' (pCore 2 G)) = center (G ⧸ pCore 2 G) := by
  have hr : pResidual 2 (center (G ⧸ pCore 2 G)) = ⊤ := by
    apply top_unique
    intro x _
    apply mem_pResidual_of_orderOf_coprime
    exact (by decide : Nat.Coprime 2 3).of_dvd_right
      (hcenter ▸ orderOf_dvd_natCard x)
  rw [coverResidual, map_embedded_pResidual, map_centralPreimage, hr,
    ← MonoidHom.range_eq_map, range_subtype]

theorem coverResidual_ne_bot (hcenter : Nat.card (center (G ⧸ pCore 2 G)) = 3) :
    coverResidual G ≠ ⊥ := by
  intro hz
  have hr : pResidual 2 (centralPreimage (pCore 2 G)) = ⊥ :=
    (map_eq_bot_iff_of_injective _ (centralPreimage (pCore 2 G)).subtype_injective).mp hz
  have hp : IsPGroup 2 (centralPreimage (pCore 2 G)) := by
    have h := isPGroup_quotient_pResidual (G := centralPreimage (pCore 2 G)) 2
    exact h.of_equiv ((QuotientGroup.quotientMulEquivOfEq hr).trans
      QuotientGroup.quotientBot)
  have hpc : IsPGroup 2 (center (G ⧸ pCore 2 G)) := by
    rw [← map_centralPreimage (pCore 2 G)]
    exact hp.map _
  obtain ⟨n, hn⟩ := hpc.exists_card_dvd_pow
  rw [hcenter] at hn
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hn)

theorem coverResidualIn_ne_bot (K : Subgroup G)
    (hcenter : Nat.card (center (K ⧸ pCore 2 K)) = 3) : coverResidualIn K ≠ ⊥ := by
  intro hz
  exact coverResidual_ne_bot hcenter
    ((map_eq_bot_iff_of_injective _ K.subtype_injective).mp hz)

theorem coverResidual_solvable : Group.IsSolvable (coverResidual G) := by
  let q := QuotientGroup.mk' (pCore 2 G)
  have hk : Group.IsSolvable q.ker := by
    dsimp [q]
    rw [QuotientGroup.ker_mk']
    let : Group.IsNilpotent (pCore 2 G) := pCore_isNilpotent
    infer_instance
  let := hk
  let : Group.IsSolvable (centralPreimage (pCore 2 G)) :=
    isSolvable_comap_of_solvable_ker q (center (G ⧸ pCore 2 G))
  exact Group.isSolvable_of_isSolvable_injective
    (f := inclusion coverResidual_le_centralPreimage)
    (inclusion_injective coverResidual_le_centralPreimage)

theorem coverResidualIn_solvable (K : Subgroup G) :
    Group.IsSolvable (coverResidualIn K) := by
  let := coverResidual_solvable (G := K)
  exact Group.isSolvable_of_surjective (K.subtype.subgroupMap_surjective (coverResidual K))

omit [Finite G] in
private theorem solvable_join_of_normalizes (A B : Subgroup G)
    [Group.IsSolvable A] [Group.IsSolvable B]
    (hn : B ≤ normalizer (A : Set G)) : Group.IsSolvable (A ⊔ B : Subgroup G) := by
  let A' := A.subgroupOf (A ⊔ B)
  let B' := B.subgroupOf (A ⊔ B)
  let : A'.Normal := normal_subgroupOf_of_le_normalizer (sup_le A.le_normalizer hn)
  let : Group.IsSolvable A' := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show A ≤ A ⊔ B from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show A ≤ A ⊔ B from le_sup_left)).injective
  let : Group.IsSolvable B' := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show B ≤ A ⊔ B from le_sup_right)).toMonoidHom)
    (subgroupOfEquivOfLe (show B ≤ A ⊔ B from le_sup_right)).injective
  exact Group.isSolvable_of_normal_sup_eq_top A' B' (codisjoint_subgroupOf_sup A B).eq_top

/-- Apply the universal earlier 13.8.13 conclusion to Y L₁ T. Its
solvability follows from the two solvable factors and relative normality. -/
theorem coverResidualIn_le_M (H K L₁ T G₁ M : Subgroup G)
    (hKH : K ≤ H) [(K.subgroupOf H).Normal]
    (hbase : L₁ ⊔ T ≤ H) (hHG : H ≤ G₁)
    [Group.IsSolvable (L₁ ⊔ T : Subgroup G)]
    (h13 : ∀ J : Subgroup G, L₁ ⊔ T ≤ J → J ≤ G₁ →
      Group.IsSolvable J → J ≤ M) : coverResidualIn K ≤ M := by
  let := coverResidualIn_solvable K
  have hs := solvable_join_of_normalizes (coverResidualIn K) (L₁ ⊔ T)
    (hbase.trans (normalizes_coverResidualIn H K hKH))
  exact le_sup_left.trans (h13 _ le_sup_right
    ((sup_le ((coverResidualIn_le K).trans hKH) hbase).trans hHG) hs)

omit [Finite G] in
theorem odd_order_coverResidual_dvd_three
    (hcenter : Nat.card (center (G ⧸ pCore 2 G)) = 3)
    (x : coverResidual G) (hx : Nat.Coprime 2 (orderOf x)) : orderOf x ∣ 3 := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let f : coverResidual G →* center (G ⧸ pCore 2 G) :=
    (q.comp (coverResidual G).subtype).codRestrict _
      (fun x => coverResidual_le_centralPreimage x.property)
  let i : f.ker →* pCore 2 G :=
    ((coverResidual G).subtype.comp f.ker.subtype).codRestrict _ (by
      intro y
      apply (QuotientGroup.eq_one_iff _).mp
      exact congrArg Subtype.val (show f y.val = 1 from y.property))
  have hi : Function.Injective i := by
    intro a b he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : pCore 2 G => (z : G)) he
  have hk : IsPGroup 2 f.ker := pCore_isPGroup.of_injective i hi
  rw [← f.orderOf_map_eq_of_coprime_of_isPGroup_ker hk x hx]
  exact hcenter ▸ orderOf_dvd_natCard (f x)

/-- Order-three generation gives containment in the literal theta subgroup. -/
theorem coverResidualIn_le_theta (H K M L₁ : Subgroup G)
    (hKH : K ≤ H) (hYM : coverResidualIn K ≤ M)
    (hcenter : Nat.card (center (K ⧸ pCore 2 K)) = 3)
    (htheta : L₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3}) :
    coverResidualIn K ≤ L₁ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hgen := closure_coprime_order_eq_top_of_pResidual_eq_top 2
    ((pResidual_eq_top_iff 2 (coverResidual K)).mpr coverResidual_isPPerfect)
  let f : coverResidual K →* G := K.subtype.comp (coverResidual K).subtype
  have hle : closure {x : coverResidual K | Nat.Coprime 2 (orderOf x)} ≤ L₁.comap f := by
    apply (closure_le _).mpr
    intro x hx
    rcases (Nat.dvd_prime Nat.prime_three).mp
      (odd_order_coverResidual_dvd_three hcenter x hx) with ho | ho
    · have he : x = 1 := orderOf_eq_one_iff.mp ho
      simp [he]
    · rw [htheta]
      apply Subgroup.subset_closure
      have hy : f x ∈ coverResidualIn K := ⟨x.val, x.property, rfl⟩
      refine ⟨⟨hKH ((coverResidualIn_le K) hy), hYM hy⟩, ?_⟩
      exact (orderOf_injective f (K.subtype_injective.comp
        (coverResidual K).subtype_injective) x).trans ho
  rw [hgen] at hle
  rintro z ⟨x, hx, rfl⟩
  exact hle (show (⟨x, hx⟩ : coverResidual K) ∈ ⊤ from trivial)

/-- Nontrivial placement in L₁, without assuming placement of Y in M. -/
theorem coverResidualIn_located (H K L₁ T G₁ M : Subgroup G)
    (hKH : K ≤ H) [(K.subgroupOf H).Normal]
    (hbase : L₁ ⊔ T ≤ H) (hHG : H ≤ G₁)
    [Group.IsSolvable (L₁ ⊔ T : Subgroup G)]
    (hcenter : Nat.card (center (K ⧸ pCore 2 K)) = 3)
    (htheta : L₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3})
    (h13 : ∀ J : Subgroup G, L₁ ⊔ T ≤ J → J ≤ G₁ →
      Group.IsSolvable J → J ≤ M) :
    coverResidualIn K ≠ ⊥ ∧ coverResidualIn K ≤ L₁ := by
  exact ⟨coverResidualIn_ne_bot K hcenter,
    coverResidualIn_le_theta H K M L₁ hKH
      (coverResidualIn_le_M H K L₁ T G₁ M hKH hbase hHG h13) hcenter htheta⟩

/-- Once the K₁ argument has excluded Y = L₁, the earlier local catalogue
and N_G(L₀) = M identify Y with L₁,+. The catalogue quantifies over all
proper nontrivial T-invariant two-perfect subgroups, as in the proof of
13.7.5(7); it does not assume an identification of this residual. -/
theorem coverResidualIn_eq_L1plus (H K L₁ L₀ L₁plus T M : Subgroup G)
    (hKH : K ≤ H) [(K.subgroupOf H).Normal] (hTH : T ≤ H)
    (hHM : ¬ H ≤ M) (hnorm : normalizer (L₀ : Set G) = M)
    (hcenter : Nat.card (center (K ⧸ pCore 2 K)) = 3)
    (hYL : coverResidualIn K ≤ L₁) (hne : coverResidualIn K ≠ L₁)
    (hsmall : ∀ X : Subgroup G, X < L₁ → X ≠ ⊥ → IsPPerfect 2 X →
      T ≤ normalizer (X : Set G) → X = L₀ ∨ X = L₁plus) :
    coverResidualIn K = L₁plus := by
  rcases hsmall (coverResidualIn K) (lt_iff_le_and_ne.mpr ⟨hYL, hne⟩)
    (coverResidualIn_ne_bot K hcenter) (coverResidualIn_isPPerfect K)
    (hTH.trans (normalizes_coverResidualIn H K hKH)) with h | h
  · exact (coverResidualIn_ne_L0 H K L₀ M hKH hHM hnorm h).elim
  · exact h

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction
