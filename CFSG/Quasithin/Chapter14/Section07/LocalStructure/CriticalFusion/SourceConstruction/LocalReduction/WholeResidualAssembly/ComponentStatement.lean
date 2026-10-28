module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceSetup
public import Theory.SpecificGroups.BinaryComponentResidual
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterOrder
public import Theory.Alternating.Aut

/-!
# The component input of source 14.7.47

The input asserts only containment of the original L₁ in each actual
C-component and an isomorphism for its intrinsic quotient by O₂. The
binary linear degrees are 3, 4, 5 and the alternating degrees are 5, 6, 7,
as in F.9.18(4) and Theorem C; A₈ is represented by SL₄(2). No uniqueness,
Sylow supplement, residual identity or conclusion of 14.7.52 is assumed.

Every permitted carrier has trivial center and a two-group outer group.
We prove those facts using the actual automorphism coverage for the binary
linear groups, the alternating groups (including the exceptional A₆ outer
group), and the octonion-derived G₂(2)′ carrier.

Source: Aschbacher–Smith, 14.7.47–48, printed pp.1063–1064,
refs/quasithin.pdf. The component input is retained for
qt-d-14752-local-reduction to discharge on this same G, T and flag.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly
open Chapter12.Section08 CriticalFusion.Source
universe u

/-- The source component carriers, with the admissible binary degrees. -/
@[expose] def ComponentRows (X : Type*) [Group X] : Prop :=
  (∃ n : ℕ, 3 ≤ n ∧ n ≤ 5 ∧ Nonempty (X ≃* SL(n, ZMod 2))) ∨
  (∃ n : ℕ, 5 ≤ n ∧ n ≤ 7 ∧ Nonempty (X ≃* alternatingGroup (Fin n))) ∨
  Nonempty (X ≃* commutator (Atlas.G2.Model (ZMod 2)))

private theorem center_bot_of_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hz : center B = ⊥) : center A = ⊥ := by
  apply eq_bot_iff.mpr
  intro a ha
  have hh := (centerCongr e ⟨a,ha⟩).property
  change e a ∈ center B at hh
  rw [hz,mem_bot] at hh
  exact e.map_eq_one_iff.mp hh

private theorem alternating_outer_two {n : ℕ} (hn : 5 ≤ n) :
    IsPGroup 2 (MulAut.Outer (alternatingGroup (Fin n))) := by
  by_cases hsix : n = 6
  · subst n
    exact IsPGroup.of_card (n := 2) AlternatingSix.ShadowLocal.outer_card
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  let A := alternatingGroup (Fin n)
  have hcard : Nat.card (Equiv.Perm (Fin n) ⧸ A) = 2 ^ 1 := by
    rw [← A.index_eq_card]
    exact alternatingGroup.index_eq_two
  apply (IsPGroup.of_card hcard).of_surjective (MulAut.outerAction A)
  intro x
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup A) x
  obtain ⟨σ,rfl⟩ :=
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hsix).surjective a
  exact ⟨QuotientGroup.mk' A σ,rfl⟩

/-- The actual center and outer-action facts for every permitted row. -/
theorem ComponentRows.center_and_outer {X : Type*} [Group X]
    (hm : ComponentRows X) : center X = ⊥ ∧ IsPGroup 2 (MulAut.Outer X) := by
  rcases hm with ⟨n,hn,hn',⟨e⟩⟩ | ⟨n,hn,_,⟨e⟩⟩ | he
  · refine ⟨center_bot_of_equiv e
      (BinaryLinear.OuterCyclic.binary_center_eq_bot (by omega)),?_⟩
    by_cases h3 : n = 3
    · subst n
      exact Matrix.PSL3Two.Automorphisms.outer_sl_isTwoGroup.of_equiv (MulAut.outerCongr e).symm
    · exact (Theory.SpecificGroups.BinaryComponentResidual.linear_outer_two
        (by omega : n = 4 ∨ n = 5)).of_equiv (MulAut.outerCongr e).symm
  · exact ⟨center_bot_of_equiv e (alternatingGroup.center_eq_bot (by simpa using (show 4 ≤ n by omega))),
      (alternating_outer_two hn).of_equiv (MulAut.outerCongr e).symm⟩
  · obtain ⟨e⟩ := he
    exact ⟨center_bot_of_equiv e Theory.SpecificGroups.g2_derived_two_center_eq_bot,
      Theory.SpecificGroups.BinaryComponentResidual.g2_outer_two.of_equiv
        (MulAut.outerCongr e).symm⟩

/-- Transport the source row through an actual group isomorphism. -/
theorem ComponentRows.of_equiv {X Y : Type*} [Group X] [Group Y]
    (hm : ComponentRows X) (e : X ≃* Y) : ComponentRows Y := by
  rcases hm with ⟨n,hn,hn',⟨a⟩⟩ | ⟨n,hn,hn',⟨a⟩⟩ | ha
  · exact Or.inl ⟨n,hn,hn',⟨e.symm.trans a⟩⟩
  · exact Or.inr (Or.inl ⟨n,hn,hn',⟨e.symm.trans a⟩⟩)
  · obtain ⟨a⟩ := ha
    exact Or.inr (Or.inr ⟨e.symm.trans a⟩)

variable {G : Type u} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The literal earlier component assertion, specialized to the original flag. -/
@[expose] def Earlier14747 (F : InvariantFlag T V 3) (L : Subgroup G) : Prop :=
  ∀ (I : Subgroup G), I ∈ F.Hz L (normalizer (L : Set G)) →
    ∀ (C : Subgroup I), C.IsCComponent →
      F.Li L 1 ≤ C.map I.subtype ∧ ComponentRows (C ⧸ pCore 2 C)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly
