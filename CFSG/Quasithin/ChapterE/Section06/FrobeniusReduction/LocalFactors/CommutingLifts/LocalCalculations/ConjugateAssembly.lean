module

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts.LocalCalculations.Basic
public import Theory.GroupTheory.PCoreImage

/-!
# Transporting a local calculation to every cyclic candidate

Choose the genuine cyclic conjugates supplied by the transitive factor
permutation. For a pair of conjugates, conjugate the first back by the
second's chosen conjugator. Its action commutes with the original torus,
so the local normalization and commutator calculation applies. Transport
that calculation back, retaining the actual conjugate local subgroup and
its intrinsic two-core.

The replacement theorem allows a new regular cyclic subgroup with exactly
the original action image. It retains the given decomposition's factors
and summands; only the distinguished torus witness changes. This permits
the symplectic calculation to select a torus central modulo the radical.

The universal local calculation is an explicit premise here. `BlockCore`
discharges it in the L₂-block branch. The remaining model calculations
must discharge it before the complete E.6.25 conclusion can be asserted.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
E.6.25, printed p.255 (PDF p.266).
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts
variable {G : Type*} [Group G]

private theorem map_conj_back (B : Subgroup G) (n : G) :
    (B.map (MulAut.conj n⁻¹).toMonoidHom).map (MulAut.conj n).toMonoidHom = B := by
  rw [map_map]
  have he : (MulAut.conj n).toMonoidHom.comp (MulAut.conj n⁻¹).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp [mul_assoc]
  rw [he, map_id]

variable [Finite G] {M V U X : Subgroup G} [IsElementaryAbelian 2 V]

/-- A single local calculation in N_G(V) supplies all conjugate envelopes. -/
theorem exists_calculations_of_normalizer_control
    (hX : RegularCyclicSection M V U X)
    (D : Representation.RegularCyclicNormalClosure.Decomposition
      (automizerRepresentation V) (inducedAutomizer V X))
    (ho : Odd (Nat.card X))
    (B : Subgroup (normalizer (V : Set G)))
    (hlocal : ∀ A : Subgroup (normalizer (V : Set G)), Odd (Nat.card A) →
      (∀ a ∈ A.map V.normalizerMonoidHom.rangeRestrict,
        ∀ x ∈ inducedAutomizer V X, Commute a x) →
      A ≤ normalizer (B : Set (normalizer (V : Set G))) ∧
        ⁅A, X.subgroupOf (normalizer (V : Set G))⁆ ≤ B.pCoreIn 2) :
    ∃ (F : Candidates U X D) (B' : Fin D.size → Subgroup (normalizer (V : Set G))),
      (∀ i j, F.subgroup i ≤ normalizer (B' j : Set (normalizer (V : Set G)))) ∧
      Pairwise fun i j => ⁅F.subgroup i, F.subgroup j⁆ ≤ (B' i).pCoreIn 2 := by
  classical
  choose n hn hcyc hcard hfaith him using exists_conjugate_cyclic_lift hX D
  let C := X.subgroupOf (normalizer (V : Set G))
  let F : Candidates U X D :=
    ⟨fun i => C.map (MulAut.conj (n i)).toMonoidHom, hn, hcyc, hcard, hfaith, him⟩
  let f := V.normalizerMonoidHom.rangeRestrict
  have hcomm (i j) (a : F.subgroup i) (b : F.subgroup j) : Commute (f a) (f b) := by
    by_cases hij : i = j
    · subst j
      let _ := F.cyclic i
      exact (Commute.all a b).map (f.comp (F.subgroup i).subtype)
    · exact F.image_commuting hij a b
  have hback (i j) :
      (F.subgroup i).map (MulAut.conj (n j)⁻¹).toMonoidHom ≤
        normalizer (B : Set (normalizer (V : Set G))) ∧
      ⁅(F.subgroup i).map (MulAut.conj (n j)⁻¹).toMonoidHom, C⁆ ≤ B.pCoreIn 2 := by
    apply hlocal
    · rw [card_map_of_injective (MulAut.conj (n j)⁻¹).injective, F.card_eq]
      exact ho
    · rintro a ⟨r, ⟨s, hs, rfl⟩, rfl⟩ x ⟨t, ht, rfl⟩
      have ht' : (MulAut.conj (n j)) t ∈ F.subgroup j :=
        mem_map_of_mem _ ht
      have hh := (hcomm i j ⟨s, hs⟩ ⟨(MulAut.conj (n j)) t, ht'⟩).conj (f (n j)⁻¹)
      simpa [f, MulAut.conj_apply, map_mul, map_inv, mul_assoc] using hh
  refine ⟨F, fun j => B.map (MulAut.conj (n j)).toMonoidHom, ?_, ?_⟩
  · intro i j
    have hn := map_mono (f := (MulAut.conj (n j)).toMonoidHom) (hback i j).1
    rw [map_conj_back, map_equiv_normalizer_eq] at hn
    exact hn
  · intro i j _
    have hc := map_mono (f := (MulAut.conj (n i)).toMonoidHom) (hback j i).2
    rw [map_commutator, map_conj_back,
      map_pCoreIn_of_ker_isPGroup _
        (IsPGroup.ker_isPGroup_of_injective (MulAut.conj (n i)).injective)] at hc
    change ⁅F.subgroup j, F.subgroup i⁆ ≤ _ at hc
    rwa [commutator_comm] at hc

/-- Restrict an ambient local calculation and transport it to every factor.
The constructed envelopes are conjugates of B inside N_G(V). -/
theorem exists_calculations_of_ambient_control
    (hX : RegularCyclicSection M V U X)
    (D : Representation.RegularCyclicNormalClosure.Decomposition
      (automizerRepresentation V) (inducedAutomizer V X))
    (ho : Odd (Nat.card X))
    (B : Subgroup G) (hBN : B ≤ normalizer (V : Set G))
    (hlocal : ∀ A : Subgroup G, A ≤ normalizer (V : Set G) → Odd (Nat.card A) →
      (∀ a ∈ inducedAutomizer V A, ∀ x ∈ inducedAutomizer V X, Commute a x) →
      A ≤ normalizer (B : Set G) ∧ ⁅A, X⁆ ≤ B.pCoreIn 2) :
    ∃ (F : Candidates U X D) (B' : Fin D.size → Subgroup (normalizer (V : Set G))),
      (∀ i j, F.subgroup i ≤ normalizer (B' j : Set (normalizer (V : Set G)))) ∧
      Pairwise fun i j => ⁅F.subgroup i, F.subgroup j⁆ ≤ (B' i).pCoreIn 2 := by
  let N := normalizer (V : Set G)
  apply exists_calculations_of_normalizer_control hX D ho (B.subgroupOf N)
  intro A hodd hcomm
  have hc : ∀ a ∈ inducedAutomizer V (A.map N.subtype),
      ∀ x ∈ inducedAutomizer V X, Commute a x := by
    change ∀ a ∈ ((A.map N.subtype).comap N.subtype).map
      V.normalizerMonoidHom.rangeRestrict, ∀ x ∈ inducedAutomizer V X, Commute a x
    rwa [comap_map_eq_self_of_injective N.subtype_injective]
  obtain ⟨hn, hk⟩ := hlocal (A.map N.subtype) (map_subtype_le A)
    (by simpa only [card_map_of_injective N.subtype_injective] using hodd) hc
  constructor
  · have hh := map_le_iff_le_comap.mp hn
    change A ≤ (normalizer (B : Set G)).subgroupOf N at hh
    rwa [subgroupOf_normalizer_eq hBN] at hh
  · apply (map_le_map_iff_of_injective N.subtype_injective).mp
    rw [map_commutator, map_subgroupOf_eq_of_le
      (hX.contained.trans (inf_le_left.trans inf_le_right)),
      map_pCoreIn_of_ker_isPGroup _ (IsPGroup.ker_isPGroup_of_injective N.subtype_injective),
      map_subgroupOf_eq_of_le hBN]
    exact hk

/-- A torus with the same action image can replace the original cyclic
choice, without changing the prescribed factor images or cardinalities. -/
theorem exists_calculations_of_replacement {Y : Subgroup G}
    (hX : RegularCyclicSection M V U X) (hY : RegularCyclicSection M V U Y)
    (himage : inducedAutomizer V Y = inducedAutomizer V X)
    (D : Representation.RegularCyclicNormalClosure.Decomposition
      (automizerRepresentation V) (inducedAutomizer V X))
    (ho : Odd (Nat.card X))
    (B : Subgroup G) (hBN : B ≤ normalizer (V : Set G))
    (hlocal : ∀ A : Subgroup G, A ≤ normalizer (V : Set G) → Odd (Nat.card A) →
      (∀ a ∈ inducedAutomizer V A, ∀ y ∈ inducedAutomizer V Y, Commute a y) →
      A ≤ normalizer (B : Set G) ∧ ⁅A, Y⁆ ≤ B.pCoreIn 2) :
    ∃ (F : Candidates U X D) (B' : Fin D.size → Subgroup (normalizer (V : Set G))),
      (∀ i j, F.subgroup i ≤ normalizer (B' j : Set (normalizer (V : Set G)))) ∧
      Pairwise fun i j => ⁅F.subgroup i, F.subgroup j⁆ ≤ (B' i).pCoreIn 2 := by
  have hcard : Nat.card Y = Nat.card X := hY.card_eq.trans hX.card_eq.symm
  let D' : Representation.RegularCyclicNormalClosure.Decomposition
      (automizerRepresentation V) (inducedAutomizer V Y) :=
    { size := D.size
      positive := D.positive
      factor := D.factor
      summand := D.summand
      distinguished := D.distinguished
      contained := by simpa only [himage] using D.contained
      group_eq := by simpa only [himage] using D.group_eq
      group_independent := D.group_independent
      commuting := D.commuting
      split := by simpa only [himage] using D.split
      moved_eq := by simpa only [himage] using D.moved_eq
      summands_independent := D.summands_independent
      self_moved := D.self_moved
      cross_fixed := D.cross_fixed
      permuted := D.permuted
      transitive := D.transitive
      alternatives := by simpa only [himage] using D.alternatives }
  obtain ⟨F, B', hn, hc⟩ := exists_calculations_of_ambient_control hY D'
    (hcard.symm ▸ ho) B hBN hlocal
  let F' : Candidates U X D := ⟨F.subgroup, F.local_containment, F.cyclic,
    fun i => (F.card_eq i).trans hcard, F.faithful, F.image_le⟩
  exact ⟨F', B', hn, hc⟩

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts
