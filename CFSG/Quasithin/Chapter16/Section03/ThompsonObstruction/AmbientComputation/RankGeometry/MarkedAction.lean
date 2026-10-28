module

public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.AmbientComputation.Contracts
public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.AmbientComputation.RankGeometry.ComponentGeometry
public import Theory.SpecificGroups.SymmetricEight.ComponentMarking.PermutationFacts

/-!
# The marked A₆ action and its natural S₆ preimage

The supplied S₈ identification sends L to the even permutations fixing the
first pair. Extending permutations of the remaining six letters gives an
explicit equivalence with A₆. Compatibility with conjugation identifies the
action of the marked u = (01)(23) with the transposition (01) on six letters.

The actual image of T_L is a faithful inner D₈. The image of T₀ contains this
order-eight subgroup and the odd transposition, so its order is at least
sixteen. The natural part of the T-action is a two-subgroup of S₆, hence has
order at most sixteen. Their images are equal; the kernel T_C lies in T₀,
which gives the required preimage equality. No rank-five or Thompson
subgroup conclusion is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the setup and
first paragraph of the proof of Lemma 16.3.12, printed pp.1181–1182 /
PDF pp.1198–1199.
-/

@[expose] public section
open Subgroup Equiv Equiv.Perm
namespace CFSG.Quasithin.Chapter16.ThompsonObstruction.AmbientComputation.MarkedAction

/-- Label the last six letters by 0 through 5, preserving their order. -/
def remaining : Fin 6 ≃ {i : Fin 8 // 2 ≤ i.val} where
  toFun i := ⟨⟨i.val + 2, by omega⟩, by dsimp; omega⟩
  invFun i := ⟨i.val.val - 2, by have := i.val.isLt; have := i.property; omega⟩
  left_inv i := by apply Fin.ext; simp
  right_inv i := by apply Subtype.ext; apply Fin.ext; have := i.property; simp; omega

/-- Extend a six-letter permutation by fixing the first pair. -/
def extend : Perm (Fin 6) →* Perm (Fin 8) := extendDomainHom remaining

theorem extend_injective : Function.Injective extend := extendDomainHom_injective remaining

theorem extend_zero (g : Perm (Fin 6)) : extend g 0 = 0 :=
  extendDomain_apply_not_subtype g remaining (by decide)

theorem extend_one (g : Perm (Fin 6)) : extend g 1 = 1 :=
  extendDomain_apply_not_subtype g remaining (by decide)

theorem extend_sign (g : Perm (Fin 6)) : sign (extend g) = sign g :=
  sign_extendDomain g remaining

def evenEmbedding : AlternatingSix.ShadowLocal.A6 →* Perm (Fin 8) :=
  extend.comp (alternatingGroup (Fin 6)).subtype

theorem evenEmbedding_injective : Function.Injective evenEmbedding :=
  extend_injective.comp Subtype.val_injective

theorem evenEmbedding_range : evenEmbedding.range = markedA6 := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨g, rfl⟩
    exact ⟨mem_alternatingGroup.mpr ((extend_sign g).trans
      (mem_alternatingGroup.mp g.property)), extend_zero g, extend_one g⟩
  · rw [← Nat.card_congr (MonoidHom.ofInjective evenEmbedding_injective).toEquiv,
      AlternatingSix.ShadowLocal.card_A6]
    exact le_of_eq Theory.SpecificGroups.SymmetricEight.ComponentMarking.card_evenPairFixer

/-- Extension identifies A₆ with the marked even pointwise pair stabilizer. -/
noncomputable def evenEquiv : AlternatingSix.ShadowLocal.A6 ≃* markedA6 :=
  (MonoidHom.ofInjective evenEmbedding_injective).trans
    (MulEquiv.subgroupCongr evenEmbedding_range)

theorem evenEquiv_coe (g : AlternatingSix.ShadowLocal.A6) :
    (evenEquiv g : Perm (Fin 8)) = extend g := rfl

theorem extend_swap : extend (swap (0 : Fin 6) 1) = swap (2 : Fin 8) 3 := by
  decide +kernel

theorem pair_commutes (g : Perm (Fin 6)) : Commute (swap (0 : Fin 8) 1) (extend g) := by
  change _ = _
  rw [mul_swap_eq_swap_mul, extend_zero, extend_one]

theorem marked_conjugation (g : Perm (Fin 6)) :
    (swap (0 : Fin 8) 1 * swap 2 3) * extend g *
      (swap 0 1 * swap 2 3)⁻¹ =
        extend (swap (0 : Fin 6) 1 * g * (swap 0 1)⁻¹) := by
  rw [← extend_swap, mul_inv_rev]
  calc
    _ = swap (0 : Fin 8) 1 * (extend (swap (0 : Fin 6) 1) * extend g *
        (extend (swap (0 : Fin 6) 1))⁻¹) * (swap 0 1)⁻¹ := by group
    _ = swap (0 : Fin 8) 1 * extend (swap (0 : Fin 6) 1 * g * (swap 0 1)⁻¹) *
        (swap 0 1)⁻¹ := by rw [map_mul, map_mul, map_inv]
    _ = _ := by rw [(pair_commutes _).eq, mul_inv_cancel_right]

open AlternatingSix.ShadowLocal

/-- A two-subgroup of the natural symmetric group has order at most sixteen. -/
theorem natural_two_subgroup_card_le (Q : Subgroup AutA6) (hQ : IsPGroup 2 Q)
    (hn : Q ≤ natural) : Nat.card Q ≤ 16 := by
  let R := Q.subgroupOf natural
  let e : R ≃* Q := subgroupOfEquivOfLe hn
  have hR : IsPGroup 2 R := hQ.of_injective e.toMonoidHom e.injective
  obtain ⟨S, hRS⟩ := hR.exists_le_sylow
  have hcardS : Nat.card S = 16 := by
    rw [S.card_eq_multiplicity, card_natural]
    rw [show 720 = 2 ^ 4 * 45 by decide,
      Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
      Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 45)]
    rfl
  rw [← Nat.card_congr e.toEquiv, ← hcardS]
  exact Nat.card_le_card_of_injective (inclusion hRS) (inclusion_injective hRS)

/-- Odd permutation conjugations do not become inner automorphisms of A₆. -/
theorem transposition_not_inner :
    permutationAction (swap (0 : Fin 6) 1) ∉ AlternatingSix.ShadowLocal.inner := by
  rintro ⟨g, hg⟩
  have he : (g : Perm (Fin 6)) = swap 0 1 :=
    permutationAction_injective ((permutationAction_coe g).trans hg)
  have h := g.property
  rw [he, mem_alternatingGroup] at h
  exact (by decide : sign (swap (0 : Fin 6) 1) ≠ 1) h

end CFSG.Quasithin.Chapter16.ThompsonObstruction.AmbientComputation.MarkedAction

namespace CFSG.Quasithin.Chapter16.ThompsonObstruction.AmbientComputation
open AlternatingSix.ShadowLocal
variable {G : Type*} [Group G] {T : Sylow 2 G} {z t : G} {L : Subgroup G}

/-- The component lies in the domain of the supplied S₈ marking. -/
theorem component_le_markedOvergroup : L ≤ enlargement t L ⊔ zpowers z :=
  (ComponentTransfer.le_layerClosure (involutionCentralizer t) L).trans le_sup_left

/-- Restrict the supplied S₈ equivalence to the actual component L. -/
noncomputable def markedComponentEquiv (d : Prepared T z t L) : L ≃* markedA6 :=
  (subgroupOfEquivOfLe component_le_markedOvergroup).symm.trans
    ((d.marked.equiv.subgroupMap _).trans (MulEquiv.subgroupCongr d.marked.component_image))

/-- The identification with A₆ obtained by restricting to the last six letters. -/
noncomputable def markedSixEquiv (d : Prepared T z t L) : L ≃* A6 :=
  (markedComponentEquiv d).trans MarkedAction.evenEquiv.symm

theorem markedSixEquiv_compatible (d : Prepared T z t L) (l : L) :
    MarkedAction.evenEmbedding (markedSixEquiv d l) =
      d.marked.equiv ⟨l, component_le_markedOvergroup l.property⟩ := by
  have h := congrArg (fun a : markedA6 => (a : Perm (Fin 8)))
    (MarkedAction.evenEquiv.apply_symm_apply (markedComponentEquiv d l))
  exact h

/-- Transport the genuine T-action through this same marked identification. -/
noncomputable def markedAction (d : Prepared T z t L) : ↥T →* AutA6 :=
  (MulAut.congr (markedSixEquiv d)).toMonoidHom.comp (componentAction d)

theorem markedAction_apply (d : Prepared T z t L) (x : T) (l : L) :
    markedAction d x (markedSixEquiv d l) = markedSixEquiv d (componentAction d x l) := by
  simp [markedAction, MulAut.congr]

theorem markedSixEquiv_conjugation (d : Prepared T z t L) (x : T)
    (hx : (x : G) ∈ enlargement t L ⊔ zpowers z) (l : L) :
    MarkedAction.evenEmbedding (markedAction d x (markedSixEquiv d l)) =
      d.marked.equiv ⟨x, hx⟩ * MarkedAction.evenEmbedding (markedSixEquiv d l) *
        (d.marked.equiv ⟨x, hx⟩)⁻¹ := by
  rw [markedAction_apply, markedSixEquiv_compatible, markedSixEquiv_compatible]
  change d.marked.equiv (⟨x, hx⟩ * ⟨l, component_le_markedOvergroup l.property⟩ *
    (⟨x, hx⟩ : ↥(enlargement t L ⊔ zpowers z))⁻¹) = _
  rw [map_mul, map_mul, map_inv]

/-- The source double transposition acts as the first transposition on six letters. -/
theorem markedAction_u (d : Prepared T z t L) :
    markedAction d ⟨d.marked.u, d.u_mem⟩ = permutationAction (swap (0 : Fin 6) 1) := by
  apply MulEquiv.ext
  intro a
  obtain ⟨l, rfl⟩ := (markedSixEquiv d).surjective a
  apply MarkedAction.evenEmbedding_injective
  have huJ : d.marked.u ∈ enlargement t L ⊔ zpowers z :=
    (le_sup_left : enlargement t L ≤ enlargement t L ⊔ zpowers z)
      d.marked.u_mem_enlargement
  rw [markedSixEquiv_conjugation d _ huJ]
  have hu : d.marked.equiv ⟨d.marked.u, huJ⟩ =
      swap (0 : Fin 8) 1 * swap 2 3 := d.marked.equiv.apply_symm_apply _
  rw [hu]
  exact MarkedAction.marked_conjugation _

/-- Elements of T_L act by their corresponding inner automorphisms. -/
theorem markedAction_component (d : Prepared T z t L) (l : componentSylow T L) :
    markedAction d ⟨l, l.property.1⟩ =
      MulAut.conj (markedSixEquiv d ⟨l, l.property.2⟩) := by
  apply MulEquiv.ext
  intro a
  obtain ⟨k, rfl⟩ := (markedSixEquiv d).surjective a
  rw [markedAction_apply]
  change markedSixEquiv d (⟨l, l.property.2⟩ * k * (⟨l, l.property.2⟩ : L)⁻¹) = _
  simp only [map_mul, map_inv, MulAut.conj_apply]

theorem markedAction_ker (d : Prepared T z t L) :
    (markedAction d).ker = (commutingSylow T L).subgroupOf (T : Subgroup G) := by
  rw [markedAction, MonoidHom.ker_comp_of_injective _ _ (MulAut.congr _).injective,
    componentAction_ker]

noncomputable def markedComponentAction (d : Prepared T z t L) :
    componentSylow T L →* AutA6 :=
  (markedAction d).comp (inclusion (show componentSylow T L ≤ (T : Subgroup G) from inf_le_left))

/-- The T_L action is faithful because the conjugation action of A₆ is faithful. -/
theorem markedComponentAction_injective (d : Prepared T z t L) :
    Function.Injective (markedComponentAction d) := by
  intro a b h
  have h' : MulAut.conj (markedSixEquiv d ⟨a, a.property.2⟩) =
      MulAut.conj (markedSixEquiv d ⟨b, b.property.2⟩) := by
    change markedAction d ⟨a, a.property.1⟩ = markedAction d ⟨b, b.property.1⟩ at h
    simpa only [markedAction_component] using h
  have hab := (markedSixEquiv d).injective (inner_injective h')
  exact Subtype.ext (congrArg (fun l : L => (l : G)) hab)

theorem markedComponentAction_le_inner (d : Prepared T z t L) :
    (markedComponentAction d).range ≤ AlternatingSix.ShadowLocal.inner := by
  rintro _ ⟨a, rfl⟩
  exact ⟨markedSixEquiv d ⟨a, a.property.2⟩, (markedAction_component d a).symm⟩

theorem markedComponentAction_card [Finite G] (d : Prepared T z t L) :
    Nat.card (markedComponentAction d).range = 8 := by
  obtain ⟨e⟩ := component_dihedral_of_equiv d (markedSixEquiv d)
  rw [← Nat.card_congr (MonoidHom.ofInjective (markedComponentAction_injective d)).toEquiv,
    Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

theorem smallGroup_le_natural_preimage (d : Prepared T z t L) :
    (smallGroup d).subgroupOf (T : Subgroup G) ≤ natural.comap (markedAction d) := by
  change ((commutingSylow T L ⊔ componentSylow T L) ⊔ zpowers d.marked.u).subgroupOf
    (T : Subgroup G) ≤ _
  have hC : commutingSylow T L ≤ (T : Subgroup G) := inf_le_left
  have hD : componentSylow T L ≤ (T : Subgroup G) := inf_le_left
  rw [subgroupOf_sup (sup_le hC hD) (zpowers_le.mpr d.u_mem), subgroupOf_sup hC hD]
  refine sup_le (sup_le ?_ ?_) ?_
  · rw [← markedAction_ker d]
    exact ker_le_comap _ _
  · intro x hx
    exact inner_le_natural (markedComponentAction_le_inner d
      ⟨⟨x, hx⟩, rfl⟩)
  · intro x hx
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hx
    have he : x = (⟨d.marked.u, d.u_mem⟩ : T) ^ n := Subtype.ext hn.symm
    change markedAction d x ∈ natural
    rw [he, map_zpow]
    exact natural.zpow_mem ⟨swap (0 : Fin 6) 1, (markedAction_u d).symm⟩ n

theorem markedComponentAction_le_small_image (d : Prepared T z t L) :
    (markedComponentAction d).range ≤
      ((smallGroup d).subgroupOf (T : Subgroup G)).map (markedAction d) := by
  rintro _ ⟨l, rfl⟩
  exact ⟨⟨l, l.property.1⟩, mem_sup_left (mem_sup_right l.property), rfl⟩

variable [Finite G]

/-- The inner order-eight image and the odd marked involution force order at least sixteen. -/
theorem marked_small_image_card_ge (d : Prepared T z t L) :
    16 ≤ Nat.card (((smallGroup d).subgroupOf (T : Subgroup G)).map (markedAction d)) := by
  let D := (markedComponentAction d).range
  let B := ((smallGroup d).subgroupOf (T : Subgroup G)).map (markedAction d)
  have hD : Nat.card D = 8 := markedComponentAction_card d
  have hDB : D ≤ B := markedComponentAction_le_small_image d
  have hne : D ≠ B := by
    intro he
    have huB : markedAction d ⟨d.marked.u, d.u_mem⟩ ∈ B :=
      ⟨⟨d.marked.u, d.u_mem⟩, mem_sup_right (mem_zpowers _), rfl⟩
    rw [← he] at huB
    have huI := markedComponentAction_le_inner d huB
    rw [markedAction_u] at huI
    exact MarkedAction.transposition_not_inner huI
  have hlt : 8 < Nat.card B := by
    by_contra h
    apply hne
    exact eq_of_le_of_card_ge hDB (by omega)
  have hdiv := card_dvd_of_le hDB
  rw [hD] at hdiv
  obtain ⟨k, hk⟩ := hdiv
  change 16 ≤ Nat.card B
  omega

/-- The natural part of T has the same image as T₀; both contain the action kernel. -/
theorem marked_natural_preimage (d : Prepared T z t L) :
    natural.comap (markedAction d) = (smallGroup d).subgroupOf (T : Subgroup G) := by
  let X := natural.comap (markedAction d)
  let B := (smallGroup d).subgroupOf (T : Subgroup G)
  have hBX : B ≤ X := smallGroup_le_natural_preimage d
  have hX2 : IsPGroup 2 (X.map (markedAction d)) :=
    (T.isPGroup'.of_injective X.subtype X.subtype_injective).map (markedAction d)
  have hXn : X.map (markedAction d) ≤ natural := map_comap_le _ _
  have hcardX := MarkedAction.natural_two_subgroup_card_le _ hX2 hXn
  have hcardB := marked_small_image_card_ge d
  have hmap : B.map (markedAction d) = X.map (markedAction d) :=
    eq_of_le_of_card_ge (map_mono hBX) (le_trans hcardX hcardB)
  have hkerB : (markedAction d).ker ≤ B := by
    rw [markedAction_ker]
    intro x hx
    exact mem_sup_left (mem_sup_left hx)
  exact (map_injective_of_ker_le (markedAction d) hkerB (hkerB.trans hBX) hmap).symm

/-- The source marking identifies the genuine action and its natural symmetric preimage. -/
theorem exists_marked_natural_preimage (d : Prepared T z t L) :
    ∃ e : L ≃* A6,
      natural.comap ((MulAut.congr e).toMonoidHom.comp (componentAction d)) =
        (smallGroup d).subgroupOf (T : Subgroup G) :=
  ⟨markedSixEquiv d, marked_natural_preimage d⟩

end CFSG.Quasithin.Chapter16.ThompsonObstruction.AmbientComputation
