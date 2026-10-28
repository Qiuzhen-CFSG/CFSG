module
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.Normalizer
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.ComponentEscape
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# The component-normality reductions in C.4.8

An original C.2.8 component which is also an ambient C-component is already
normalized by the proper local subgroup. Otherwise its two ambient conjugates
would both occur in the local span, making that span normal in H, contrary to
the genuine C.2.12 normalizer identity. Independently, a quasisimple two-core
quotient of the local span makes the span a C-component, so minimality identifies
it with the original component.

These are the terminal normality steps of C.2.13 and C.3.1/C.4.1 used in
C.4.8. Promotion to an ambient component in the contained-Fitting branch,
and the one-component quotient calculation in the escaping branches, remain
separate source obligations. Neither is assumed as part of C.2.8.

Source: Aschbacher--Smith, C.2.13 and C.4.8, printed pp.148,153; used by
the original nonnormal covering argument of 4.2.12--13, printed pp.610--611.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G]
variable {H M L R V : Subgroup G}

omit [Finite G] in
private theorem normalizes_of_two_orbits {A N : Subgroup G}
    (horbit : A.Normal ∨ (normalizer (A : Set G)).index = 2)
    (hnot : ¬ (conjugateSpanBy A N).Normal) : N ≤ normalizer (A : Set G) := by
  rcases horbit with hn | hi
  · let := hn
    rw [normalizer_eq_top]
    exact le_top
  · by_contra hN
    let B := normalizer (A : Set G)
    let : B.Normal := normal_of_index_eq_two hi
    have hlt : B < B ⊔ N := lt_of_le_of_ne le_sup_left (by
      intro he
      exact hN ((show N ≤ B ⊔ N from le_sup_right).trans he.symm.le))
    have hm := relIndex_mul_index hlt.le
    rw [hi] at hm
    have hp : (B.relIndex (B ⊔ N) * (B ⊔ N).index).Prime :=
      hm ▸ Nat.prime_two
    have htop : B ⊔ N = ⊤ := by
      rcases Nat.prime_mul_iff.mp hp with ⟨_,hindex⟩ | ⟨_,hrel⟩
      · exact index_eq_one.mp hindex
      · exact (hlt.not_ge (relIndex_eq_one.mp hrel)).elim
    exact hnot (conjugateSpanBy_normal_of_normalizer_normal A N htop)

/-- The ambient-component part of C.2.13 implies the needed local normality. -/
theorem normalizes_of_ambient_component
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V) (hstrict : M < H)
    (hL : (L.subgroupOf H).IsCComponent) : M ≤ normalizer (L : Set G) := by
  have hLH : L ≤ H := h.component_le.trans h.local_le
  let A := L.subgroupOf H
  let N := M.subgroupOf H
  let C := conjugateSpanBy A N
  have hmap : C.map H.subtype = conjugateSpanBy L M := by
    rw [map_conjugateSpanBy,map_subgroupOf_eq_of_le hLH,
      map_subgroupOf_eq_of_le h.local_le]
  have hnot : ¬ C.Normal := by
    intro hn
    let := hn
    have hHC : H ≤ normalizer (conjugateSpanBy L M : Set G) := by
      rw [←hmap]
      have hh := C.le_normalizer_map H.subtype
      simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
    have hHM : H ≤ M := by
      rw [←h.normalizer_span_eq]
      exact le_inf le_rfl hHC
    exact hstrict.not_ge hHM
  have hQ : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) := by
    refine ⟨?_,h.sqtk.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (h.sqtk.stronglyQuasithin p hp ho)
  have hn : N ≤ normalizer (A : Set H) := normalizes_of_two_orbits
    (Chapter1.Section02.proposition_1_2_1_three_orbit_source hQ hL) hnot
  have hh := (map_mono (f := H.subtype) hn).trans (A.le_normalizer_map H.subtype)
  rwa [map_subgroupOf_eq_of_le hLH,map_subgroupOf_eq_of_le h.local_le] at hh

/-- The C.2.13 span equality follows from ambient component placement. -/
theorem span_eq_of_ambient_component
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V) (hstrict : M < H)
    (hL : (L.subgroupOf H).IsCComponent) : conjugateSpanBy L M = L :=
  le_antisymm (conjugateSpanBy_le le_rfl (h.normalizes_of_ambient_component hstrict hL))
    (le_conjugateSpanBy L M)

/-- Only the quasisimple quotient of the span, rather than the full C.3/C.4
classification row or its module marking, is needed to identify the component. -/
theorem span_eq_of_quasisimple_quotient
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    [IsQuasisimple ((conjugateSpanBy L M) ⧸ pCore 2 (conjugateSpanBy L M))] :
    conjugateSpanBy L M = L := by
  let X := conjugateSpanBy L M
  let : Group.IsPerfect X := h.span_perfect
  have hp : IsPPerfect 2 X := by
    intro N hN hq
    let := hN
    by_contra hne
    let : Nontrivial (X ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsNilpotent (X ⧸ N) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable (X ⧸ N) inferInstance
  have hX := isCComponent_top_of_isPPerfect_of_quasisimple_quotient
    (pCore 2 X) pCore_isPGroup hp
  have hLX := h.component.subgroupOf_of_le (le_conjugateSpanBy L M)
    (conjugateSpanBy_le_self h.component_le)
  exact le_antisymm (subgroupOf_eq_top.mp (hLX.eq_of_le hX le_top))
    (le_conjugateSpanBy L M)

/-- The actual contrary configuration in 4.2.12 has neither of the two
placement properties sufficient for C.4.8 normality. -/
theorem nonnormal_obstructions
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V) (hstrict : M < H)
    (hn : ¬ M ≤ normalizer (L : Set G)) :
    ¬ (L.subgroupOf H).IsCComponent ∧
      ¬ IsQuasisimple ((conjugateSpanBy L M) ⧸ pCore 2 (conjugateSpanBy L M)) := by
  refine ⟨fun hL => hn (h.normalizes_of_ambient_component hstrict hL),?_⟩
  intro hq
  let := hq
  have hs := h.span_eq_of_quasisimple_quotient
  exact hn (hs ▸ le_normalizer_conjugateSpanBy L M)

end CFSG.Quasithin.ChapterC.HypothesisC28
