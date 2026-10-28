module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Section
public import Theory.GroupTheory.SolvableResidual
public import Theory.SpecificGroups.DihedralSolvable
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

/-!
# The canonical ambient A₆ supplied by Held's section

A normal A₆ with dihedral quotient is exactly the solvable residual of its
overgroup: A₆ is perfect and the quotient is solvable. Thus every perfect
subgroup of that overgroup lies in this A₆. We transport the supplied section
to the ambient group, preserving its actual equivalence and proving this
universal containment property.

In particular, an ambient conjugation carrying this A₆ into the original
centralizer already normalizes it. This is the normalization step in Held
5.2, without assuming that the larger centralizer is normalized.

Source: D. Held, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, Lemmas 4.2 and 5.2.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis
namespace AlternatingSixSection

variable {C : Type*} [Group C] (s : AlternatingSixSection C)

public theorem subgroup_isPerfect : Group.IsPerfect s.subgroup := by
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  exact Group.IsPerfect.ofSurjective (f := s.alternatingEquiv.symm.toMonoidHom)
    s.alternatingEquiv.symm.surjective

public theorem subgroup_eq_solvableResidual : s.subgroup = solvableResidual C := by
  let := s.normal
  let := s.subgroup_isPerfect
  let := GLS3.Chapter5.dihedralGroup_isSolvable 4
  let : Group.IsSolvable (C ⧸ s.subgroup) :=
    Group.isSolvable_of_isSolvable_injective
      (f := s.quotientEquiv.toMonoidHom) s.quotientEquiv.injective
  exact le_antisymm (le_solvableResidual_of_isPerfect _)
    (solvableResidual_le_of_solvable_quotient _)

/-- The quotient has order eight, so every element with cube one lies in A₆. -/
public theorem mem_subgroup_of_cube_eq_one (x : C) (hx : x ^ 3 = 1) :
    x ∈ s.subgroup := by
  let := s.normal
  let q := QuotientGroup.mk' s.subgroup
  have hq3 : (q x) ^ 3 = 1 := by rw [← map_pow, hx, map_one]
  have hcard : Nat.card (C ⧸ s.subgroup) = 8 := by
    rw [Nat.card_congr s.quotientEquiv.toEquiv, DihedralGroup.nat_card]
  have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hq3) (orderOf_dvd_natCard (q x))
  rw [hcard] at hd
  norm_num at hd
  exact (QuotientGroup.eq_one_iff x).mp hd

variable {G : Type*} [Group G] {H : Subgroup G} (s : AlternatingSixSection H)

/-- The actual subgroup of the ambient group, not the quotient section. -/
@[expose] public def ambientSubgroup : Subgroup G := s.subgroup.map H.subtype

public noncomputable def ambientAlternatingEquiv :
    s.ambientSubgroup ≃* alternatingGroup (Fin 6) :=
  (s.subgroup.equivMapOfInjective H.subtype H.subtype_injective).symm.trans
    s.alternatingEquiv

public theorem ambientSubgroup_isPerfect : Group.IsPerfect s.ambientSubgroup := by
  let := s.subgroup_isPerfect
  exact Group.IsPerfect.map H.subtype

public theorem ambientSubgroup_le : s.ambientSubgroup ≤ H := by
  rintro _ ⟨a, _, rfl⟩
  exact a.property

public theorem mem_ambientSubgroup_of_cube_eq_one (x : G) (hx : x ∈ H)
    (hcube : x ^ 3 = 1) : x ∈ s.ambientSubgroup :=
  ⟨⟨x, hx⟩, s.mem_subgroup_of_cube_eq_one ⟨x, hx⟩ (Subtype.ext hcube), rfl⟩

public theorem ambientSubgroup_center_eq_bot : center s.ambientSubgroup = ⊥ := by
  apply eq_bot_iff.mpr
  intro a ha
  apply s.ambientAlternatingEquiv.injective
  rw [map_one]
  have hm : s.ambientAlternatingEquiv a ∈ center (alternatingGroup (Fin 6)) := by
    rw [mem_center_iff]
    intro b
    obtain ⟨b, rfl⟩ := s.ambientAlternatingEquiv.surjective b
    simpa only [map_mul] using congrArg s.ambientAlternatingEquiv (mem_center_iff.mp ha b)
  rwa [alternatingGroup.center_eq_bot (by simp), mem_bot] at hm

public theorem le_normalizer_ambientSubgroup : H ≤ normalizer (s.ambientSubgroup : Set G) := by
  let := s.normal
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨g, hg⟩ * a * ⟨g, hg⟩⁻¹, s.normal.conj_mem a ha ⟨g, hg⟩, rfl⟩
  · rintro ⟨a, ha, he⟩
    refine ⟨(⟨g, hg⟩ : H)⁻¹ * a * ⟨g, hg⟩, ?_, ?_⟩
    · exact s.normal.conj_mem' a ha ⟨g, hg⟩
    · change g⁻¹ * (a : G) * g = x
      change (a : G) = g * x * g⁻¹ at he
      rw [he]
      group

/-- The A₆ is intrinsic to the centralizer; the chosen section equivalence
does not affect its underlying subgroup. -/
public theorem ambientSubgroup_eq_map_solvableResidual :
    s.ambientSubgroup = (solvableResidual H).map H.subtype := by
  rw [ambientSubgroup, s.subgroup_eq_solvableResidual]

public theorem perfect_le_ambientSubgroup (P : Subgroup G) [Group.IsPerfect P]
    (hP : P ≤ H) : P ≤ s.ambientSubgroup := by
  rw [s.ambientSubgroup_eq_map_solvableResidual]
  exact le_map_solvableResidual_of_isPerfect P H hP

/-- It suffices that the conjugate A₆ stays inside the original centralizer.
The conclusion is normalization of A₆, not of that centralizer. -/
public theorem normalizes_ambientSubgroup_of_conj_le (g : G)
    (hg : s.ambientSubgroup.map (MulAut.conj g).toMonoidHom ≤ H) :
    g ∈ normalizer (s.ambientSubgroup : Set G) := by
  let := s.ambientSubgroup_isPerfect
  let : Group.IsPerfect (s.ambientSubgroup.map (MulAut.conj g).toMonoidHom) :=
    Group.IsPerfect.map _
  let : Finite s.ambientSubgroup :=
    Finite.of_equiv (alternatingGroup (Fin 6)) s.ambientAlternatingEquiv.symm.toEquiv
  rw [mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge (s.perfect_le_ambientSubgroup _ hg)
  rw [card_map_of_injective (MulAut.conj g).injective]

end AlternatingSixSection
end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis
