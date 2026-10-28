module
public import Theory.SpecificGroups.Alternating.FourTransitiveCubic
public import Theory.GroupAction.RegularNonidentityOrbit
public import Theory.GroupAction.CoprimeHall
public import Theory.GroupTheory.SubgroupConjugation
public import Theory.GroupTheory.PResidualCommutator
public import Theory.GroupTheory.Commutator.NormalizesSupplement
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.SpecificGroups.SymmetricTwoResidual

/-!
# The actual A₄ residual of a cubic extension

A cubic group fully moving an abelian four-group is transitive on its three
nonidentity elements, hence their join is A₄. In a two-group-by-cubic group,
coprime commutator idempotence identifies the four-element moving subgroup,
and its join with the cubic complement is normal and two-perfect. It is
therefore the actual two-residual, independent of the chosen complement.

Source application: Y=O²(Y₀) in Aschbacher–Smith C.1.29, printed p.134.
-/
public section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup
/-- A normalized intermediate subgroup containing the coprime moving
subgroup has the same ambient commutator. -/
theorem commutator_eq_of_coprime_containment
    {G : Type*} [Group G] (R U X : Subgroup G)
    (hn : X ≤ normalizer (R : Set G))
    (hc : Nat.Coprime (Nat.card X) (Nat.card R))
    (hUR : U ≤ R) (hm : ⁅R, X⁆ ≤ U) : ⁅R, X⁆ = ⁅U, X⁆ := by
  have hfull : ⁅⁅R, X⁆, X⁆ = ⁅R, X⁆ := by
    have he := commutator_closure_coprime_idempotent R (X : Set G)
      (by simpa only [Subgroup.closure_eq] using hn)
      (fun x hx => hc.of_dvd_left (by
        simpa only [Subgroup.orderOf_mk] using _root_.orderOf_dvd_natCard (⟨x, hx⟩ : X)))
    simpa only [Subgroup.closure_eq] using he
  exact le_antisymm (hfull.symm.le.trans (commutator_mono hm le_rfl))
    (commutator_mono hUR le_rfl)
end Subgroup

namespace AlternatingFourTransitiveCubic
variable {G : Type*} [Group G] [Finite G]

/-- A cubic complement fully moving an abelian four-group gives an actual A₄. -/
theorem nonempty_equiv_of_full_movement (U X : Subgroup G)
    [IsMulCommutative U] (hU : Nat.card U = 4) (hX : Nat.card X = 3)
    (hn : X ≤ normalizer (U : Set G)) (hm : ⁅U, X⁆ = U) :
    Nonempty ((U ⊔ X : Subgroup G) ≃* alternatingGroup (Fin 4)) := by
  let : Normalizes X U := ⟨hn⟩
  let : MulDistribMulAction X U := conjMulDistribMulActionOfLeNormalizer X U hn
  have hfull : commutatorAction X U = ⊤ := by
    apply map_injective U.subtype_injective
    rw [commutatorAction_subgroup_conj_map_eq_commutator U X hn, hm,
      ← MonoidHom.range_eq_map, range_subtype]
  have hcop : Nat.Coprime (Nat.card X) (Nat.card U) := by rw [hX, hU]; decide
  have hfix : FixedPoints.subgroup X U = ⊥ := by
    have hh := (isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := U) (A := X) (Group.isSolvable_of_comm fun x y => mul_comm x y)
      hcop inferInstance).disjoint
    change Disjoint (FixedPoints.subgroup X U) (commutatorAction X U) at hh
    rwa [hfull, disjoint_top] at hh
  have hfree : ∀ x : X, x ≠ 1 → ∀ u : U, x • u = u → u = 1 := by
    intro x hx u hu
    have hgen : zpowers x = ⊤ := zpowers_eq_top_of_prime_card hX hx
    apply hfix.le
    intro y
    exact smul_eq_self_of_mem_zpowers (hgen.symm ▸ mem_top y) hu
  apply nonempty_equiv U X hU hX hn
  intro u hu hun v hv hvn
  obtain ⟨x, hx⟩ := Theory.GroupAction.exists_smul_eq_of_free_of_card
    (by rw [hU, hX]) hfree
    (show (⟨u, hu⟩ : U) ≠ 1 from fun hh => hun (congrArg Subtype.val hh))
    (show (⟨v, hv⟩ : U) ≠ 1 from fun hh => hvn (congrArg Subtype.val hh))
  exact ⟨x, congrArg Subtype.val hx⟩

/-- In a two-group-by-cubic group, a four-element moving subgroup makes
the actual two-residual A₄. The residual, rather than a chosen complement,
is therefore normalized by every automorphism of the original group. -/
theorem residual_equiv_of_commutator_four (R X : Subgroup G) [R.Normal]
    (hR : IsPGroup 2 R) (hX : Nat.card X = 3) (hgen : R ⊔ X = ⊤)
    [IsMulCommutative (⁅R, X⁆ : Subgroup G)]
    (hm : Nat.card (⁅R, X⁆ : Subgroup G) = 4) :
    Nonempty (pResidual 2 G ≃* alternatingGroup (Fin 4)) := by
  let U := ⁅R, X⁆
  have hcop : Nat.Coprime (Nat.card X) (Nat.card R) := by
    obtain ⟨n, hn⟩ := hR.exists_card_eq
    rw [hX, hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hfull : ⁅U, X⁆ = U := by
    have he := commutator_closure_coprime_idempotent R (X : Set G)
      (by simpa only [Subgroup.closure_eq] using
        (show X ≤ normalizer (R : Set G) from le_normalizer_of_normal))
      (fun x hx => hcop.of_dvd_left (by
        simpa only [Subgroup.orderOf_mk] using _root_.orderOf_dvd_natCard (⟨x, hx⟩ : X)))
    simpa only [Subgroup.closure_eq] using he
  obtain ⟨eY⟩ := nonempty_equiv_of_full_movement U X hm hX
    (normalizer_commutator_ge_right R X) hfull
  let Y := U ⊔ X
  let : U.Normal := normalizer_eq_top_iff.mp (top_unique (by
    rw [← hgen]
    exact sup_le (normalizer_commutator_ge_left R X) (normalizer_commutator_ge_right R X)))
  have hRY : R ≤ normalizer (Y : Set G) := by
    have hh := le_normalizer_sup_of_commutator_le X R X U le_rfl
      (by rw [commutator_comm])
    change R ≤ normalizer ((U ⊔ X : Subgroup G) : Set G)
    rw [sup_comm]
    exact hh
  let : Y.Normal := normalizer_eq_top_iff.mp (top_unique (by
    rw [← hgen]
    exact sup_le hRY ((show X ≤ Y from le_sup_right).trans Y.le_normalizer)))
  let e4 : pResidual 2 (Equiv.Perm (Fin 4)) ≃* alternatingGroup (Fin 4) :=
    MulEquiv.subgroupCongr (Equiv.Perm.twoResidual_eq_alternating (Fin 4))
  have hp4 : IsPPerfect 2 (alternatingGroup (Fin 4)) :=
    (isPPerfect_pResidual 2).of_surjective e4.toMonoidHom e4.surjective
  have hpY : IsPPerfect 2 Y := hp4.of_surjective eY.symm.toMonoidHom eY.symm.surjective
  have hYR : Y ⊔ R = ⊤ := top_unique (by
    rw [← hgen]
    exact sup_le le_sup_right ((show X ≤ Y from le_sup_right).trans le_sup_left))
  have he : pResidual 2 G = Y := pResidual_eq_of_isPPerfect_sup Y R hpY hR hYR
  exact ⟨(MulEquiv.subgroupCongr he).trans eY⟩
end AlternatingFourTransitiveCubic

namespace AlternatingFourTransitiveCubic
variable {G : Type*} [Group G] [Finite G]
theorem residual_join_equiv_of_commutator_four (R X : Subgroup G) [R.Normal]
    (hR : IsPGroup 2 R) (hX : Nat.card X = 3)
    (hm : Nat.card (⁅R, X⁆ : Subgroup G) = 4) :
    Nonempty (pResidual 2 (R ⊔ X : Subgroup G) ≃* alternatingGroup (Fin 4)) := by
  let H := R ⊔ X
  let R0 := R.subgroupOf H
  let X0 := X.subgroupOf H
  have hR0 : IsPGroup 2 R0 := hR.comap_subtype
  have hX0 : Nat.card X0 = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show X ≤ H from le_sup_right)).toEquiv).trans hX
  have hgen : R0 ⊔ X0 = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left, map_subgroupOf_eq_of_le le_sup_right,
      ← MonoidHom.range_eq_map, range_subtype]
  have hmmap : (⁅R0, X0⁆ : Subgroup H).map H.subtype = ⁅R, X⁆ := by
    rw [map_commutator, map_subgroupOf_eq_of_le le_sup_left, map_subgroupOf_eq_of_le le_sup_right]
  have hmcard : Nat.card (⁅R0, X0⁆ : Subgroup H) = 4 := by
    rw [← card_map_of_injective (K := (⁅R0, X0⁆ : Subgroup H)) (f := H.subtype) H.subtype_injective,
      hmmap, hm]
  let : IsMulCommutative (⁅R0, X0⁆ : Subgroup H) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hmcard
  exact residual_equiv_of_commutator_four R0 X0 hR0 hX0 hgen hmcard
end AlternatingFourTransitiveCubic
