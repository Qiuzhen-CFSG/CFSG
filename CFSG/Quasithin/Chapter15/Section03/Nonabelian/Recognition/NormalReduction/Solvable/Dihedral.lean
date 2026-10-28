module

public import Theory.Comparator.Defs
public import Theory.GroupTheory.PGroup.ExtraspecialInvolution
public import Theory.GroupTheory.CyclicNormalCentralizer
public import Theory.GroupTheory.Commutator.CoprimeQuadratic

/-!
# The marked dihedral obstruction in 15.3.58

An elementary subgroup larger than the center of an extraspecial binary
group supplies a noncentral involution, and hence an actual dihedral factor.
The specified center identifies its central involution with the source v.
This group normalizes [K, v] whenever K is normal. Its central involution is
a commutator, so its action on a cyclic [K, v] is trivial. Coprime quadratic
action would then make [K, v] trivial.

The extraspecial product, its center, and its elementary subgroup come from
the correctly marked clauses (4) and (6) of 15.3.56. An abstract order-eight
nonabelian factor without a center marking would not suffice.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), pp.1147–1149.
-/

public section
open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction
open scoped commutatorElement
variable {G : Type*} [Group G] [Finite G]

/-- An elementary subgroup larger than the center constructs a dihedral embedding carrying its central involution to the prescribed actor. -/
theorem exists_marked_dihedral_of_extraspecial
    (P : Subgroup G) [IsExtraspecial 2 P] (X : Subgroup P)
    [IsElementaryAbelian 2 X] (hX : 2 < Nat.card X)
    (v : G) (hv : v ≠ 1)
    (hZ : (Subgroup.center P).map P.subtype = Subgroup.zpowers v) :
    ∃ f : DihedralGroup 4 →* G, Function.Injective f ∧ f (DihedralGroup.r 2) = v := by
  have hXZ : ¬ X ≤ Subgroup.center P := by
    intro h
    have hh := Subgroup.card_le_of_le h
    rw [IsExtraspecial.center_order_p 2 P] at hh
    omega
  obtain ⟨x, hx, hxZ⟩ := SetLike.not_le_iff_exists.mp hXZ
  have hx2 : x ^ 2 = 1 := congrArg Subtype.val
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 X) (⟨x, hx⟩ : X))
  obtain ⟨D, ⟨e⟩, hZD, -⟩ :=
    IsExtraspecial.exists_dihedral_factor_of_noncentral_involution x hx2 hxZ
  have hvZ : v ∈ (Subgroup.center P).map P.subtype := hZ ▸ Subgroup.mem_zpowers v
  obtain ⟨z, hz, hzv⟩ := hvZ
  let zD : D := ⟨z, hZD hz⟩
  have heZ : e zD ∈ Subgroup.center (DihedralGroup 4) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨y, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_center_iff.mp hz y)
  have hene : e zD ≠ 1 := by
    intro h
    have hh : zD = 1 := e.injective (h.trans e.map_one.symm)
    exact hv (hzv.symm.trans (congrArg (fun d : D => ((d : P) : G)) hh))
  have hemark : e zD = DihedralGroup.r 2 :=
    (show ∀ a : DihedralGroup 4, a ∈ Subgroup.center _ → a ≠ 1 → a = DihedralGroup.r 2 by
      decide +kernel) _ heZ hene
  let f := P.subtype.comp (D.subtype.comp e.symm.toMonoidHom)
  refine ⟨f, P.subtype_injective.comp (D.subtype_injective.comp e.symm.injective), ?_⟩
  rw [← hemark]
  change ((e.symm (e zD) : D) : G) = v
  rw [e.symm_apply_apply]
  change (z : G) = v
  exact hzv

omit [Finite G] in
/-- The marked dihedral subgroup normalizes the actual commutator of a normal subgroup with its center. -/
theorem marked_dihedral_normalizes_commutator
    (K : Subgroup G) [K.Normal] (v : G)
    (f : DihedralGroup 4 →* G) (hmark : f (DihedralGroup.r 2) = v) :
    f.range ≤ Subgroup.normalizer ((⁅K, Subgroup.zpowers v⁆ : Subgroup G) : Set G) := by
  rintro _ ⟨d, rfl⟩
  have hc : Commute (f d) v := by
    rw [← hmark]
    exact (show Commute d (DihedralGroup.r 2) from
      (show ∀ d : DihedralGroup 4, Commute d (DihedralGroup.r 2) by
        change ∀ d : DihedralGroup 4, d * DihedralGroup.r 2 = DihedralGroup.r 2 * d
        decide +kernel) d).map f
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.Normal.map_conj_eq, MonoidHom.map_zpowers]
  change ⁅K, Subgroup.zpowers (f d * v * (f d)⁻¹)⁆ = _
  rw [hc.eq, mul_inv_cancel_right]

omit [Finite G] in
/-- Conjugation on a cyclic group kills the central involution of a normalizing dihedral group of order eight. -/
theorem marked_dihedral_center_centralizes_cyclic
    (R : Subgroup G) [IsCyclic R] (v : G)
    (f : DihedralGroup 4 →* G) (hmark : f (DihedralGroup.r 2) = v)
    (hnorm : f.range ≤ Subgroup.normalizer (R : Set G)) :
    v ∈ Subgroup.centralizer (R : Set G) := by
  let g : DihedralGroup 4 →* Subgroup.normalizer (R : Set G) :=
    f.codRestrict _ (fun d => hnorm ⟨d, rfl⟩)
  let a := R.normalizerMonoidHom.comp g
  let _ := (IsCyclic.mulAutMulEquiv R).toMonoidHom.commGroupOfInjective
    (IsCyclic.mulAutMulEquiv R).injective
  have ha : a (DihedralGroup.r 2) = 1 := by
    have hz : ⁅(DihedralGroup.r 1 : DihedralGroup 4),
        (DihedralGroup.sr 0 : DihedralGroup 4)⁆ = DihedralGroup.r 2 := by decide +kernel
    rw [← hz, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have he := congrArg (fun b : MulAut R => (b ⟨r, hr⟩ : G)) ha
  change f (DihedralGroup.r 2) * r * (f (DihedralGroup.r 2))⁻¹ = r at he
  rw [hmark] at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction
variable {G : Type*} [Group G] [Finite G]

/-- A nontrivial odd solvable commutator cannot be cyclic when the involution is the center of a dihedral subgroup. -/
theorem odd_normal_commutator_not_cyclic_of_marked_dihedral
    (K : Subgroup G) [K.Normal] [Group.IsSolvable K]
    (hodd : Odd (Nat.card K)) (v : G) (hv : IsInvolution v)
    (f : DihedralGroup 4 →* G) (hmark : f (DihedralGroup.r 2) = v)
    (hne : ⁅K, Subgroup.zpowers v⁆ ≠ ⊥) :
    ¬ IsCyclic (⁅K, Subgroup.zpowers v⁆ : Subgroup G) := by
  intro hc
  let := hc
  have hcent := marked_dihedral_center_centralizes_cyclic
    ⁅K, Subgroup.zpowers v⁆ v f hmark (marked_dihedral_normalizes_commutator K v f hmark)
  apply hne
  apply Subgroup.commutator_eq_bot_of_coprime_quadratic K (Subgroup.zpowers v)
    Subgroup.le_normalizer_of_normal inferInstance
  · rw [Nat.card_zpowers, orderOf_eq_prime hv.2 hv.1]
    exact hodd.coprime_two_left
  · rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact Subgroup.zpowers_le.mpr hcent
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction

