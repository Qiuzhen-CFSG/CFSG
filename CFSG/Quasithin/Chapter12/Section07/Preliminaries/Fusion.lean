module

public import Theory.GroupTheory.ElementSubgroupIncidence
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.ElementaryAbelian.Basic
public import CFSG.Quasithin.Chapter12.Section07

/-!
# Fusion on V and the t-centralizer core

The two L-orbits in V# remain distinct because z centralizes an ambient Sylow
subgroup while the centralizer of t has even relative index in M. Explicit
fusion transport gives centralizer transitivity and the unique conjugate
through t. Only M_t is required to normalize V: the source does not in general
assert M = N_G(V). The final theorem supplies the literal t-core hypothesis
to Section07.conjugate_join_isTwoGroup_of_two_orbits.

The fusion export concerns elements of V. The broader wording about all
involutions of M in printed 12.7.9(1) is not asserted by this module.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Notation
12.2.5(3e), Lemmas 12.7.9(2,3) and 12.7.22(5), printed pp.796, 842, 848.
-/

public section

open Subgroup
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07.Preliminaries
variable {G : Type*} [Group G]

/-- The two module orbits cannot fuse when the centralizer of one has even
index in M and the other centralizes an ambient Sylow two-subgroup. -/
theorem not_isConj_of_even_centralizer_index [Finite G]
    (T : Sylow 2 G) (M : Subgroup G) (z t : G)
    (hz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (ht : centralizer ({t} : Set G) ≤ M)
    (hi : 2 ∣ (centralizer ({t} : Set G)).relIndex M) : ¬ IsConj z t := by
  intro hconj
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  have hCt : (g • T : Sylow 2 G) ≤ centralizer ({t} : Set G) := by
    rintro a ⟨b, hb, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change (g * b * g⁻¹) * t = t * (g * b * g⁻¹)
    have h := congrArg (MulAut.conj g) (mem_centralizer_singleton_iff.mp (hz hb))
    simpa only [map_mul, MulAut.conj_apply, hg] using h
  exact (g • T : Sylow 2 G).not_dvd_index
    ((hi.trans (relIndex_dvd_index_of_le ht)).trans (index_dvd_of_le hCt))

/-- Fusion inside V from the two distinct ambient classes. This states the
precise scope supplied by the two-orbit argument of 12.7.9(1). -/
theorem fusion_on_V_of_two_orbits (V M : Subgroup G) (z t : G)
    (horbits : ∀ v ∈ V, v ≠ 1 → ∃ m ∈ M,
      MulAut.conj m v = z ∨ MulAut.conj m v = t)
    (hzt : ¬ IsConj z t) {x y : G} (hx : x ∈ V) (hy : y ∈ V)
    (hxy : IsConj x y) : ∃ m ∈ M, MulAut.conj m x = y := by
  by_cases hx1 : x = 1
  · subst x
    have hy1 : y = 1 := by simpa using hxy.symm
    exact ⟨1, M.one_mem, by simp [hy1]⟩
  have hy1 : y ≠ 1 := by
    intro hy1
    subst y
    exact hx1 (by simpa using hxy)
  obtain ⟨a, ha, hax⟩ := horbits x hx hx1
  obtain ⟨b, hb, hby⟩ := horbits y hy hy1
  have he : MulAut.conj a x = MulAut.conj b y := by
    have hconj : IsConj (MulAut.conj a x) (MulAut.conj b y) :=
      (isConj_iff.mpr ⟨a, rfl⟩).symm.trans (hxy.trans (isConj_iff.mpr ⟨b, rfl⟩))
    rcases hax with hax | hax <;> rcases hby with hby | hby
    · exact hax.trans hby.symm
    · exact (hzt (hax ▸ hby ▸ hconj)).elim
    · exact (hzt (hby ▸ hax ▸ hconj.symm)).elim
    · exact hax.trans hby.symm
  refine ⟨b⁻¹ * a, M.mul_mem (M.inv_mem hb) ha, ?_⟩
  calc
    _ = MulAut.conj b⁻¹ (MulAut.conj a x) := by simp [MulAut.conj_apply, mul_assoc]
    _ = y := by rw [he]; simp [MulAut.conj_apply, mul_assoc]

/-- Source 12.7.9(2), with an actual centralizer conjugator. -/
theorem centralizer_transitive_on_conjugates (V M : Subgroup G) (z t : G)
    (hMN : M ≤ normalizer (V : Set G))
    (horbits : ∀ v ∈ V, v ≠ 1 → ∃ m ∈ M,
      MulAut.conj m v = z ∨ MulAut.conj m v = t)
    (hzt : ¬ IsConj z t) {v : G} (hv : v ∈ V) (g : G) (hg : v ∈ V.conjBy g) :
    ∃ c ∈ centralizer ({v} : Set G), V.conjBy c = V.conjBy g := by
  apply (element_fusion_iff_centralizer_incidence V v).mp ?_ g hg
  intro y hy hvy
  obtain ⟨m, hm, he⟩ := fusion_on_V_of_two_orbits V M z t horbits hzt hv hy hvy
  exact ⟨m, hMN hm, he⟩

/-- Source 12.7.9(3): the branch centralizer bound makes its orbit on
conjugates trivial. -/
theorem unique_conjugate_through_t (V A M : Subgroup G) (z t : G)
    (hAN : A ≤ normalizer (V : Set G)) (htV : t ∈ V)
    (horbits : ∀ v ∈ V, v ≠ 1 → ∃ m ∈ A,
      MulAut.conj m v = z ∨ MulAut.conj m v = t)
    (hzt : ¬ IsConj z t) (ht : centralizer ({t} : Set G) ≤ M)
    (hMt : M ⊓ centralizer ({t} : Set G) ≤ normalizer (V : Set G))
    (g : G) (hg : t ∈ V.conjBy g) : V.conjBy g = V := by
  obtain ⟨c, hc, he⟩ := centralizer_transitive_on_conjugates V A z t hAN horbits hzt htV g hg
  rw [← he]
  exact mem_normalizer_iff_map_conj_eq.mp (hMt ⟨ht hc, hc⟩)

/-- The literal two-core containment supplied by the branch 12.7.8. -/
theorem le_t_centralizer_core (V M : Subgroup G) [IsElementaryAbelian 2 V]
    (t : G) (htV : t ∈ V)
    (hMt : M ⊓ centralizer ({t} : Set G) ≤ normalizer (V : Set G))
    (ht : centralizer ({t} : Set G) ≤ M) :
    V ≤ (centralizer ({t} : Set G)).pCoreIn 2 := by
  apply le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V) ?_ ((le_inf ht le_rfl).trans hMt)
  intro v hv
  apply mem_centralizer_singleton_iff.mpr
  exact congrArg Subtype.val (mul_comm (⟨v, hv⟩ : V) ⟨t, htV⟩)

/-- Application to the exact two-orbit consumer in Section07. Only the
independent centralizer core at z remains to be supplied. -/
theorem conjugate_join_isTwoGroup_of_t_branch (V A M : Subgroup G)
    [IsElementaryAbelian 2 V] (z t : G) (htV : t ∈ V)
    (hAN : A ≤ normalizer (V : Set G))
    (horbits : ∀ v ∈ V, v ≠ 1 → ∃ m ∈ A,
      MulAut.conj m v = z ∨ MulAut.conj m v = t)
    (ht : centralizer ({t} : Set G) ≤ M)
    (hMt : M ⊓ centralizer ({t} : Set G) ≤ normalizer (V : Set G))
    (hz : V ≤ (centralizer ({z} : Set G)).pCoreIn 2)
    (g : G) (hfix : V ⊓ centralizer (V.conjBy g : Set G) ≠ ⊥) :
    IsPGroup 2 (V ⊔ V.conjBy g : Subgroup G) := by
  apply Section07.conjugate_join_isTwoGroup_of_two_orbits V
    (IsElementaryAbelian.isPGroup 2 V) z t ?_ hz
    (le_t_centralizer_core V M t htV hMt ht) g hfix
  intro v hv hv1
  obtain ⟨m, hm, he⟩ := horbits v hv hv1
  exact ⟨m, hAN hm, he⟩

section LocalOrbit
variable [Finite G]

private theorem local_index_sup_of_normal (N C : Subgroup G) [N.Normal] :
    C.relIndex (N ⊔ C) = C.relIndex N := by
  have hmul : N.relIndex C * C.relIndex (N ⊔ C) = N.relIndex C * C.relIndex N := by
    calc
      N.relIndex C * C.relIndex (N ⊔ C) = (C ⊓ N).relIndex (N ⊔ C) := by
        rw [← inf_relIndex_left (H := C) (K := N)]
        exact relIndex_mul_relIndex _ _ _ inf_le_left le_sup_right
      _ = (C ⊓ N).relIndex N * N.relIndex (N ⊔ C) :=
        (relIndex_mul_relIndex _ _ _ inf_le_right le_sup_left).symm
      _ = N.relIndex C * C.relIndex N := by
        simp [inf_relIndex_right, Nat.mul_comm]
  exact Nat.eq_of_mul_eq_mul_left
    (Nat.pos_of_ne_zero (index_ne_zero_of_finite : N.relIndex C ≠ 0)) hmul

/-- The intrinsic even L-orbit of t suffices: normality of L in its
normalizer transfers that even index to M before applying the Sylow argument. -/
theorem not_isConj_of_even_local_orbit (T : Sylow 2 G) (L : Subgroup G) (z t : G)
    (hz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (ht : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hi : 2 ∣ (centralizer ({t} : Set G)).relIndex L) : ¬ IsConj z t := by
  let M := normalizer (L : Set G)
  let N := L.subgroupOf M
  let C := (centralizer ({t} : Set G)).subgroupOf M
  let : N.Normal := normal_subgroupOf_of_le_normalizer (show M ≤ normalizer (L : Set G) from le_rfl)
  have hrel : C.relIndex N = (centralizer ({t} : Set G)).relIndex L :=
    relIndex_subgroupOf L.le_normalizer
  have hdiv : C.relIndex N ∣ C.index := by
    rw [← local_index_sup_of_normal N C]
    exact relIndex_dvd_index_of_le le_sup_right
  exact not_isConj_of_even_centralizer_index T M z t hz ht ((hrel.symm ▸ hi).trans hdiv)
end LocalOrbit

end CFSG.Quasithin.Chapter12.Section07.Preliminaries
