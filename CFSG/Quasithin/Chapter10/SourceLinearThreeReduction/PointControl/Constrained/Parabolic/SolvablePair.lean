module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Parabolic.NodeExchange
public import Theory.GroupTheory.TwoThreeSolvable
public import Theory.GroupTheory.NormalizedSupConsequences
public import Theory.GroupTheory.SolvableMutualCommutator
/-!
# Solvability of the two exchanged component point nodes

The natural-three marking gives C_L(u) order 24 times the two-core order,
so it is solvable. Its conjugate is solvable as well. The source component
commutation theorem puts their mutual commutator inside the two-core of
L T, making their join solvable. The common point Sylow normalizes both
centralizers. Adjoining it proves that the literal Pc and Pc^t have
solvable join, as required by the rank-ten exchange contradiction.

Source: Aschbacher--Smith, 10.2.9, printed p.753.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

theorem LinearFiveData.componentPointCentralizer_solvable {c : Context D t v I}
    (m : LinearFiveData c) : Group.IsSolvable (componentPointCentralizer L t v) := by
  apply isSolvable_of_prime_dvd_card_eq_two_or_three
  intro p hp hd
  rw [m.componentPointCentralizer_card] at hd
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := L)).exists_card_eq
  rw [hn] at hd
  rcases hp.dvd_mul.mp hd with h24 | h2
  · have h : p ∣ 2^3*3 := h24
    rcases hp.dvd_mul.mp h with h2 | h3
    · exact Or.inl (((Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow h2)).resolve_left hp.ne_one)
    · exact Or.inr (((Nat.dvd_prime Nat.prime_three).mp h3).resolve_left hp.ne_one)
  · exact Or.inl (((Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow h2)).resolve_left hp.ne_one)

/-- The two original component centralizers have solvable join: their
mutual commutator lies in the actual local two-core. -/
theorem LinearFiveData.componentPointCentralizer_pair_solvable {c : Context D t v I}
    (m : LinearFiveData c) : Group.IsSolvable
      (componentPointCentralizer L t v ⊔
        (componentPointCentralizer L t v).map (MulAut.conj t).toMonoidHom : Subgroup G) := by
  let A := componentPointCentralizer L t v
  let B := A.map (MulAut.conj t).toMonoidHom
  let : Group.IsSolvable A := m.componentPointCentralizer_solvable
  let : Group.IsSolvable B := Group.isSolvable_of_surjective
    ((MulAut.conj t).toMonoidHom.subgroupMap_surjective A)
  have hc : ⁅A,B⁆ ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    (commutator_mono inf_le_left (map_mono inf_le_left)).trans
      (source_conjugate_commutator_le_core D.simpleQTKE D.maximal.1
        c.escaping.t_mem c.escaping.t_not_normalizes)
  let : Group.IsNilpotent (⁅A,B⁆ : Subgroup G) :=
    ((isPGroup_pCoreIn 2 (L ⊔ (T : Subgroup G))).to_le hc).isNilpotent
  exact Group.isSolvable_sup_of_solvable_commutator A B

/-- The literal Pc and its t-conjugate generate a solvable subgroup. -/
theorem LinearFiveData.componentPointNode_pair_solvable {c : Context D t v I}
    (m : LinearFiveData c) : Group.IsSolvable
      (componentPointNode T L t v ⊔
        (componentPointNode T L t v).map (MulAut.conj t).toMonoidHom : Subgroup G) := by
  let A := componentPointCentralizer L t v
  let B := A.map (MulAut.conj t).toMonoidHom
  let S := pointSylow T v
  let f := (MulAut.conj t).toMonoidHom
  have hS : S.map f = S := mem_normalizer_iff_map_conj_eq.mp
    (m.pointSylow_normalized c.escaping.t_mem)
  have hSA : S ≤ normalizer (A : Set G) := m.pointSylow_normalizes_componentPointCentralizer
  have hSB : S ≤ normalizer (B : Set G) := by
    rw [←hS]
    exact (map_mono hSA).trans (A.le_normalizer_map f)
  have hSAB : S ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) :=
    (le_inf hSA hSB).trans (normalizer_inf_normalizer_le_normalizer_sup A B)
  let : Group.IsSolvable (A ⊔ B : Subgroup G) := m.componentPointCentralizer_pair_solvable
  let : Group.IsNilpotent S := ((Chapter1.isSylowIn_iff.mp c.join_sylow).1).isNilpotent
  have hs := Group.isSolvable_sup_of_normalizes (A ⊔ B) S hSAB
  have he : componentPointNode T L t v ⊔
      (componentPointNode T L t v).map f = (A ⊔ B) ⊔ S := by
    change (A ⊔ S) ⊔ (A ⊔ S).map f = _
    rw [Subgroup.map_sup,hS]
    exact sup_sup_sup_comm A S B S |>.trans (by rw [sup_idem])
  rw [he]
  exact hs
end CFSG.Quasithin.Chapter10.PointControl.Constrained
