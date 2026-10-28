module
public import ABG.ChapterII.Section1.SmallSubgroups
public import Theory.GroupTheory.SubgroupConjugacy
public import ABG.ChapterII.Section1.MaximalModels
public import ABG.ChapterII.Section1.DerivedFrattini
public import ABG.ChapterII.Section1.WreathedDefs
public import ABG.ChapterII.Section1.CanonicalFrattiniJoins

/-!
# Joins with the derived and Frattini subgroup

In a quasi-dihedral group, adjoining any Klein four subgroup to the derived
subgroup gives a dihedral subgroup of index two. Adjoining any quaternion
subgroup of order eight gives a generalized quaternion subgroup of index two.
Together the two joins generate the whole group, while the derived subgroup
itself is cyclic of index four. The derived subgroup equals the Frattini
subgroup by the already proved structure lemma.

For the presentation generators, the canonical small subgroups give the
joins `⟨a²,b⟩` and `⟨a²,ab⟩`. Their explicit dihedral and quaternion
models and index two are known from Lemma 1. Both maximal subgroups are
normal, as is the derived subgroup, so conjugating a small representative
leaves its join unchanged. The single subgroup classes transfer these exact
join equalities to arbitrary representatives. The two canonical joins contain
`b` and `ab`, hence generate the whole group. The derived-subgroup cardinality
from Lemma 1 gives its index four.

These are the subgroup-join calculations used in Alperin–Brauer–Gorenstein,
Chapter II, §1, Proposition 1, article pp.10–11, based on Lemma 1(ii)–(iv)
on article p.9 of `refs/latex/alperin-brauer-gorenstein.tex`. They supply
concrete subgroup types for the focal-subgroup cases in the fusion argument.
-/

namespace ABG.QuasiDihedral
variable {G : Type*} [Group G]

private theorem sup_eq_of_conjugate (K D T₀ T : Subgroup G) [K.Normal] [D.Normal]
    (hjoin : K ⊔ T₀ = D) (g : G)
    (hg : T₀.map (MulAut.conj g).toMonoidHom = T) : K ⊔ T = D := by
  have hK : K.map (MulAut.conj g).toMonoidHom = K := by
    simpa only [MulEquiv.toMonoidHom_eq_coe] using Subgroup.Normal.map_conj_eq K g
  have hD : D.map (MulAut.conj g).toMonoidHom = D := by
    simpa only [MulEquiv.toMonoidHom_eq_coe] using Subgroup.Normal.map_conj_eq D g
  calc
    K ⊔ T = K.map (MulAut.conj g).toMonoidHom ⊔ T₀.map (MulAut.conj g).toMonoidHom := by
      rw [hK, hg]
    _ = (K ⊔ T₀).map (MulAut.conj g).toMonoidHom := (Subgroup.map_sup _ _ _).symm
    _ = D := by rw [hjoin, hD]

private theorem derived_index_four {n : ℕ} (hn : 4 ≤ n)
    (hcard : Nat.card G = 2 ^ n)
    (hderived : Nat.card (commutator G) = 2 ^ (n - 2)) :
    (commutator G).index = 4 := by
  have h := (commutator G).card_mul_index
  rw [hderived, hcard] at h
  have he : 2 ^ n = 2 ^ (n - 2) * 4 := by
    calc
      2 ^ n = 2 ^ ((n - 2) + 2) := congrArg (2 ^ ·) (by omega)
      _ = 2 ^ (n - 2) * 4 := by rw [pow_add]; norm_num
  rw [he] at h
  exact Nat.eq_of_mul_eq_mul_left (by positivity) h

/-- The derived subgroup joined with arbitrary four and Q8 representatives gives
  the two noncyclic maximal subgroups and their combined top join. -/
public theorem frattini_joins (hG : Stellmacher.IsSemidihedralGroup G)
    (T Q : Subgroup G) (hT : IsKleinFour T) (hQ : Nonempty (Q ≃* QuaternionGroup 2)) :
    (commutator G ⊔ T).index = 2 ∧
      Stellmacher.IsDihedralGroup ↥(commutator G ⊔ T) ∧
      (commutator G ⊔ Q).index = 2 ∧
      ABG.IsGeneralizedQuaternionGroup ↥(commutator G ⊔ Q) ∧
      commutator G ⊔ T ⊔ Q = ⊤ ∧
      (commutator G).index = 4 ∧ IsCyclic (commutator G) := by
  obtain ⟨R, S, _, _, hfour, hquaternion, _⟩ := four_quaternion_subgroups hG
  obtain ⟨n, hn, hcard, a, b, ha, hb, hab, hgen⟩ := hG
  let T₀ := Subgroup.closure ({a ^ (2 ^ (n - 2)), b} : Set G)
  let Q₀ := Subgroup.closure ({a ^ (2 ^ (n - 3)), a * b} : Set G)
  let D₀ := Subgroup.closure ({a ^ 2, b} : Set G)
  let Y₀ := Subgroup.closure ({a ^ 2, a * b} : Set G)
  have hT₀ : IsKleinFour T₀ := four_representative_isKleinFour hn a b ha hb hab hgen
  have hQ₀ : Nonempty (Q₀ ≃* QuaternionGroup 2) :=
    (quaternion_representative_local hn a b hcard ha hb hab hgen).1
  obtain ⟨gT, hgT⟩ := Subgroup.conjugate_of_same_class R T T₀ (hfour T hT) (hfour T₀ hT₀)
  obtain ⟨gQ, hgQ⟩ := Subgroup.conjugate_of_same_class S Q Q₀
    (hquaternion Q hQ) (hquaternion Q₀ hQ₀)
  obtain ⟨hKF, hFA, hcyclic, hKcard⟩ := derived_eq_frattini hn hcard a b ha hb hab hgen
  have hKA : commutator G = Subgroup.zpowers (a ^ 2) := hKF.trans hFA
  obtain ⟨_, hDi, hYi, _, hDiso, hYiso⟩ := explicit_subgroup_models hn a b hcard ha hb hab hgen
  let : D₀.Normal := Subgroup.normal_of_index_eq_two hDi
  let : Y₀.Normal := Subgroup.normal_of_index_eq_two hYi
  obtain ⟨hKT, hKQ, hDY⟩ := canonical_frattini_joins hn a b hgen
  have hDT : commutator G ⊔ T = D₀ :=
    sup_eq_of_conjugate (commutator G) D₀ T₀ T (by rw [hKA]; exact hKT) gT hgT
  have hYQ : commutator G ⊔ Q = Y₀ :=
    sup_eq_of_conjugate (commutator G) Y₀ Q₀ Q (by rw [hKA]; exact hKQ) gQ hgQ
  refine ⟨?_, ?_, ?_, ?_, ?_, derived_index_four hn hcard hKcard, hcyclic⟩
  · rw [hDT]
    exact hDi
  · rw [hDT]
    exact ⟨2 ^ (n - 2), hDiso⟩
  · rw [hYQ]
    exact hYi
  · rw [hYQ]
    exact ⟨n - 3, by omega, hYiso⟩
  · calc
      commutator G ⊔ T ⊔ Q = (commutator G ⊔ T) ⊔ (commutator G ⊔ Q) := by
        simp [sup_left_comm, sup_comm]
      _ = D₀ ⊔ Y₀ := by rw [hDT, hYQ]
      _ = ⊤ := hDY
end ABG.QuasiDihedral
