module

public import Theory.GroupTheory.NoncentralChiefRefinement.BinaryFlagSections

/-!
# Chief refinement of repeated two-factor binary flags

An equivariant section with m copies of a binary representation is filtered by
coordinate support. Each successive copy pulls back its invariant two-factor
flag to two actual ambient-normal chief intervals. Concatenation gives length
and noncentral two-chief count 2m. Zero copies give a singleton series.
The relative coordinates of every step come from `SectionCoordinates.stepCoordinates`
and `BinaryFlag.Map` and retain the original conjugation action.

Source application: Aschbacher--Smith, 13.5.22(2), printed p.924/PDF p.941.
-/

@[expose] public section
open Subgroup
namespace NoncentralChiefRefinement.SectionCoordinates
variable {K V : Type*} [Group K] [AddCommGroup V] [Module (ZMod 2) V]
  {A B : NormalNode K} {ρ : Representation (ZMod 2) K V}

private theorem exists_flag_pair (c : SectionCoordinates A B ρ 1) (hAB : A ≤ B)
    (P : Subrepresentation ρ)
    [Representation.IsIrreducible P.toRepresentation]
    [Representation.IsIrreducible P.quotientRepresentation]
    (hP : ∃ k v, P.toRepresentation k v ≠ v)
    (hQ : ∃ k v, P.quotientRepresentation k v ≠ v) :
    ∃ t : ChiefSeries K, t.head = A ∧ t.last = B ∧
      t.length = 2 ∧ t.noncentralTwoCount = 2 := by
  let e : Section A B ≃* Multiplicative V :=
    c.equiv.trans BinaryFlag.Map.oneCopy.symm
  have he (k : K) (x : Section A B) :
      (e (sectionAction A B k x)).toAdd = ρ k (e x).toAdd :=
    c.equivariant k x 0
  let q := BinaryFlag.ofSection e.toMonoidHom he
  have hq : Function.Surjective q.hom :=
    BinaryFlag.ofSection_surjective _ he e.surjective
  have hA : q.preimage ⊥ = A := by
    apply le_antisymm
    · intro x hx
      have hz : e (QuotientGroup.mk' (A.val.subgroupOf B.val) ⟨x, hx.1⟩) = 1 :=
        Multiplicative.toAdd.injective hx.2
      exact (QuotientGroup.eq_one_iff (N := A.val.subgroupOf B.val) ⟨x, hx.1⟩).mp (e.injective (hz.trans e.map_one.symm))
    · exact BinaryFlag.le_ofSection_kernel hAB _ he
  obtain ⟨t, ht0, ht1, htl, htc⟩ := q.exists_chief_pair P hq hP hQ
  exact ⟨t, ht0.trans hA, ht1, htl, htc⟩

theorem exists_repeatedFlag_refinement {m : ℕ} (c : SectionCoordinates A B ρ m)
    (hAB : A ≤ B) (P : Subrepresentation ρ)
    [Representation.IsIrreducible P.toRepresentation]
    [Representation.IsIrreducible P.quotientRepresentation]
    (hP : ∃ k v, P.toRepresentation k v ≠ v)
    (hQ : ∃ k v, P.quotientRepresentation k v ≠ v) :
    ∃ t : ChiefSeries K, t.head = A ∧ t.last = B ∧
      t.length = 2 * m ∧ t.noncentralTwoCount = 2 * m := by
  have aux (n : ℕ) (hn : n ≤ m) :
      ∃ t : ChiefSeries K, t.head = c.supportNode 0 ∧ t.last = c.supportNode n ∧
        t.length = 2 * n ∧ t.noncentralTwoCount = 2 * n := by
    induction n with
    | zero =>
      refine ⟨RelSeries.singleton _ (c.supportNode 0), rfl, rfl, rfl, ?_⟩
      exact Nat.card_eq_zero.mpr (Or.inl ⟨fun i => Fin.elim0 i.val⟩)
    | succ n ih =>
      obtain ⟨t, ht0, htn, htl, htc⟩ := ih (by omega)
      let i : Fin m := ⟨n, by omega⟩
      obtain ⟨u, hu0, hu1, hul, huc⟩ := exists_flag_pair (c.stepCoordinates i)
        (c.supportNode_mono (Nat.le_succ n)) P hP hQ
      have htu : t.last = u.head := htn.trans hu0.symm
      refine ⟨t.smash u htu, (RelSeries.head_smash htu).trans ht0,
        (RelSeries.last_smash htu).trans hu1, ?_, ?_⟩
      · change t.length + u.length = _
        rw [htl, hul]
        omega
      · rw [ChiefSeries.noncentralTwoCount_smash, htc, huc]
        omega
  obtain ⟨t, ht0, ht1, htl, htc⟩ := aux m le_rfl
  exact ⟨t, ht0.trans (c.supportNode_zero hAB), ht1.trans c.supportNode_last, htl, htc⟩
end NoncentralChiefRefinement.SectionCoordinates
