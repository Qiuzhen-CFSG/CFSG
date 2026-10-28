module
public import Theory.GroupTheory.CentralizerSmallKernelTransport
public import Theory.ElementaryAbelian.Injective
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The characteristic span of involutions with small conjugacy classes

The involutions with centralizer index at most two generate a characteristic
subgroup. If an elementary subgroup V centralizes an index-two subgroup Q,
then V lies in this span. When [Q,R] lies in V and R together with a Sylow
generates the ambient group, the absence of characteristic normal subgroups
therefore forces one of the generating involutions outside Q.

This is the subgroup K and outside-involution step of Goldschmidt,
*Automorphisms of trivalent graphs* (1980), proof of (2.14), printed p.385.
-/

public section
open Subgroup
namespace Theory.GroupTheory.SmallClassInvolutions
variable {G : Type*} [Group G]

def span (G : Type*) [Group G] : Subgroup G :=
  closure {t : G | t ^ 2 = 1 ∧ (centralizer ({t} : Set G)).index ≤ 2}

instance : (span G).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro e
  apply (closure_le _).2
  intro t ht
  apply Subgroup.subset_closure
  change e t ^ 2 = 1 ∧ (centralizer ({e t} : Set G)).index ≤ 2
  refine ⟨by simpa only [map_pow, map_one] using congrArg e ht.1, ?_⟩
  rw [← CentralizerSmallKernelTransport.map_centralizer e t,
    index_map_of_bijective e.bijective]
  exact ht.2

theorem le_span_of_centralizes_index_two (V Q : Subgroup G)
    [IsElementaryAbelian 2 V] (hVQ : V ≤ centralizer (Q : Set G))
    (hQ : Q.index = 2) : V ≤ span G := by
  intro v hv
  apply Subgroup.subset_closure
  refine ⟨elemPow_eq_one_of_isElementaryAbelian v hv, ?_⟩
  have hc : Q ≤ centralizer ({v} : Set G) := by
    intro q hq
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hVQ hv) q hq)
  exact Nat.le_of_dvd (by omega) (hQ ▸ index_dvd_of_le hc)

theorem exists_outside_of_no_characteristic_normal
    (P : Sylow 2 G) (Q R V : Subgroup G)
    (hQP : Q ≤ (P : Subgroup G)) (hVQ : V ≤ Q)
    [IsElementaryAbelian 2 V] (hV : V ≠ ⊥)
    (hVC : V ≤ centralizer (Q : Set G))
    (hQi : Q.relIndex (P : Subgroup G) = 2)
    (hQR : ⁅Q,R⁆ ≤ V) (hgen : R ⊔ (P : Subgroup G) = ⊤)
    (hP : ∀ K : Subgroup P, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (P : Subgroup G).subtype).Normal) :
    ∃ t : P, (t : G) ∉ Q ∧ t ^ 2 = 1 ∧
      (centralizer ({t} : Set P)).index ≤ 2 := by
  let S := (P : Subgroup G)
  let KP := span P
  let K := KP.map S.subtype
  have hVP : V ≤ S := hVQ.trans hQP
  let VP := V.subgroupOf S
  let QP := Q.subgroupOf S
  let u : VP ≃* V := subgroupOfEquivOfLe hVP
  let : IsElementaryAbelian 2 VP :=
    IsElementaryAbelian.of_injective u.toMonoidHom u.injective
  have hVK : V ≤ K := by
    have hc : VP ≤ centralizer (QP : Set P) := by
      intro v hv
      rw [mem_centralizer_iff]
      intro q hq
      apply Subtype.ext
      exact mem_centralizer_iff.mp (hVC hv) q hq
    have hh := le_span_of_centralizes_index_two VP QP hc hQi
    rw [← map_subgroupOf_eq_of_le hVP]
    exact map_mono hh
  by_contra h
  have hKQ : K ≤ Q := by
    apply map_le_iff_le_comap.mpr
    apply (closure_le _).2
    intro t ht
    by_contra htQ
    exact h ⟨t, htQ, ht.1, ht.2⟩
  have hPK : S ≤ normalizer (K : Set G) := by
    have hh := KP.le_normalizer_map S.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  have hRK : R ≤ normalizer (K : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr
      (((commutator_mono hKQ le_rfl).trans hQR).trans hVK)
  have hKN : K.Normal := normalizer_eq_top_iff.mp
    (top_unique (hgen.symm.le.trans (sup_le hRK hPK)))
  have hKP : KP ≠ ⊥ := by
    intro hk
    apply hV
    apply bot_unique
    simpa only [K, hk, Subgroup.map_bot] using hVK
  exact hP KP inferInstance hKP hKN

end Theory.GroupTheory.SmallClassInvolutions
