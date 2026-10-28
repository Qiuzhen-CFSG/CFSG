module

public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.LinearPrimeFamily
public import Theory.SpecificGroups.AlternatingSix.OuterSolvable
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Dihedral
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterOrder
public import Theory.SpecificGroups.PSL3Four.CentralCover.FixedResiduals.Kernels.SylowModels
public import Theory.SpecificGroups.PSL3Three.OuterTwo
public import Theory.SpecificGroups.PSL3Three.EvenLocals
public import Theory.Mathieu.M11.Properties.OuterRestriction
public import Theory.Mathieu.M11.Properties.SylowTwo
public import Theory.SpecificGroups.PSL2.OuterSolvable.SmallDegreeTwoGroup
public import Theory.SpecificGroups.PSL2.AdjacentPowerSylow
public import Theory.GroupTheory.SemidihedralStandardModel

/-!
# The surviving small component models in source 2.5.8

After the eliminations in 2.5.7, the non-Bender list in 2.5.2 consists of
A₆, PSL₃(2), PSL₃(3), M₁₁ and PSL₂(p), with p > 7 Fermat or Mersenne.
The predicate below retains that exact prime domain. Actual automorphism
quotients are two-groups, and each actual Sylow subgroup is dihedral of
order at least eight or isomorphic to the standard semidihedral sixteen.
The source dispatcher is separate: it supplies this model witness from
the original ambient hypotheses, rather than assuming these conclusions.

Source: Aschbacher--Smith 2.5.2, printed pp.551--552, and 2.5.8(1),(3), p.556.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup
open scoped MatrixGroups

/-- The exact non-Bender component catalogue surviving source 2.5.7. -/
def IsSmallRemainingComponent (K : Type*) [Group K] : Prop :=
  Nonempty (K ≃* alternatingGroup (Fin 6)) ∨
  Nonempty (K ≃* Matrix.PSL3Two.PSL) ∨
  Nonempty (K ≃* Matrix.PSL3Three.PSL) ∨
  Nonempty (K ≃* Sporadic.Mathieu.M11) ∨ IsLargePrimeLinear K

/-- The two concrete possibilities in source 2.5.8(3). -/
def SourceSylowTwoShape (P : Type*) [Group P] : Prop :=
  (∃ m : ℕ, 2 ≤ m ∧ Nonempty (P ≃* DihedralGroup (2 ^ m))) ∨
    Nonempty (P ≃* Semidihedral.StandardModel 4 (by omega))

theorem SourceSylowTwoShape.of_mulEquiv {P Q : Type*} [Group P] [Group Q]
    (h : SourceSylowTwoShape Q) (e : P ≃* Q) : SourceSylowTwoShape P := by
  unfold SourceSylowTwoShape at h
  rcases h with h | h
  · obtain ⟨m, hm, ⟨f⟩⟩ := h
    exact Or.inl ⟨m, hm, ⟨e.trans f⟩⟩
  · obtain ⟨f⟩ := h
    exact Or.inr ⟨e.trans f⟩

/-- Source 2.5.8(1), using the actual outer quotient of the selected component. -/
theorem IsSmallRemainingComponent.outer_isTwoGroup {K : Type*} [Group K]
    (h : IsSmallRemainingComponent K) : IsPGroup 2 (MulAut.Outer K) := by
  unfold IsSmallRemainingComponent at h
  rcases h with h | h | h | h | h
  · obtain ⟨e⟩ := h
    exact (IsPGroup.of_card (n := 2) AlternatingSix.ShadowLocal.outer_card).of_equiv
      (MulAut.outerCongr e).symm
  · obtain ⟨e⟩ := h
    exact Matrix.PSL3Two.Automorphisms.outer_sl_isTwoGroup.of_equiv
      (MulAut.outerCongr (e.trans Matrix.PSL3Two.equiv.symm)).symm
  · obtain ⟨e⟩ := h
    exact Matrix.PSL3Three.outer_isTwoGroup.of_equiv (MulAut.outerCongr e).symm
  · obtain ⟨e⟩ := h
    exact Sporadic.Mathieu.m11_outer_isPGroup_two.of_equiv (MulAut.outerCongr e).symm
  · obtain ⟨p, hp, hb, ⟨e⟩⟩ := h
    let : Fact p.Prime := ⟨hp.1⟩
    exact (Theory.PSL2.OuterSolvable.SmallDegreeSquares.outer_isPGroup_two
      (F := ZMod p) (n := 1) hp.1 (hp.1.odd_of_ne_two (by omega)) (by omega)
      (by simp)).of_equiv (MulAut.outerCongr e).symm

private theorem semidihedral_shape {P : Type*} [Group P] (hc : Nat.card P = 16)
    (hg : ∃ a b : P, orderOf a = 8 ∧ orderOf b = 2 ∧
      b * a * b⁻¹ = a ^ 3 ∧ closure ({a, b} : Set P) = ⊤) :
    SourceSylowTwoShape P := by
  obtain ⟨a, b, ha, hb, hab, hgen⟩ := hg
  exact Or.inr (Semidihedral.standardModel_equiv_of_presentation
    (by omega : 4 ≤ 4) a b ha hb hab hgen hc)

private theorem model_sylow_transport {K L : Type*} [Group K] [Finite K]
    [Group L] [Finite L] (e : K ≃* L)
    (h : ∀ Q : Sylow 2 L, SourceSylowTwoShape Q) (P : Sylow 2 K) :
    SourceSylowTwoShape P := by
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  exact (h Q).of_mulEquiv ((P : Subgroup K).equivMapOfInjective e.toMonoidHom e.injective)

/-- Source 2.5.8(3), on every specified Sylow subtype of the selected component. -/
theorem IsSmallRemainingComponent.sylowTwoShape {K : Type*} [Group K] [Finite K]
    (h : IsSmallRemainingComponent K) (P : Sylow 2 K) : SourceSylowTwoShape P := by
  unfold IsSmallRemainingComponent at h
  rcases h with h | h | h | h | h
  · obtain ⟨e⟩ := h
    apply model_sylow_transport e _ P
    intro Q
    exact Or.inl ⟨2, le_rfl, AlternatingSix.ShadowLocal.alternatingSylow_dihedral Q⟩
  · obtain ⟨e⟩ := h
    apply model_sylow_transport e _ P
    intro Q
    exact Or.inl ⟨2, le_rfl,
      Matrix.PSL3Four.FixedResidualKernels.psl3Two_sylow_dihedral Q⟩
  · obtain ⟨e⟩ := h
    apply model_sylow_transport (e.trans Matrix.PSL3Three.equiv.symm) _ P
    intro Q
    apply semidihedral_shape _ (Matrix.PSL3Three.sylowTwo_generators_SL Q)
    change Nat.card (Q : Subgroup Matrix.PSL3Three.SL) = 16
    rw [Q.card_eq_multiplicity, Matrix.PSL3Three.card_SL]
    decide +kernel
  · obtain ⟨e⟩ := h
    apply model_sylow_transport e _ P
    intro Q
    obtain ⟨T, a, b, ha, hb, hab, hgen⟩ := Sporadic.Mathieu.m11_exists_semidihedral_sylow
    apply SourceSylowTwoShape.of_mulEquiv (P := Q) (Q := T) _ (Q.equiv T)
    apply semidihedral_shape _ ⟨a, b, ha, hb, hab, hgen⟩
    change Nat.card (T : Subgroup Sporadic.Mathieu.M11) = 16
    rw [T.card_eq_multiplicity, Sporadic.Mathieu.m11_order]
    decide +kernel
  · obtain ⟨p, hp, hb, ⟨e⟩⟩ := h
    let : Fact p.Prime := ⟨hp.1⟩
    apply model_sylow_transport e _ P
    intro Q
    apply Or.inl
    obtain ⟨k, hk⟩ : ∃ k, p - 1 = 2 ^ k ∨ p + 1 = 2 ^ k := by
      rcases hp.2 with ⟨k, hk⟩ | ⟨k, hk⟩
      · exact ⟨2 ^ k, Or.inl (by omega)⟩
      · exact ⟨k, Or.inr hk⟩
    exact Theory.PSL2.sylow_dihedral_of_adjacent_power (by omega) hk Q

/-- Literal joint consumer: the model witness supplies both source assertions. -/
theorem IsSmallRemainingComponent.outer_and_sylow {K : Type*} [Group K] [Finite K]
    (h : IsSmallRemainingComponent K) (P : Sylow 2 K) :
    IsPGroup 2 (MulAut.Outer K) ∧ SourceSylowTwoShape P :=
  ⟨h.outer_isTwoGroup, h.sylowTwoShape P⟩

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
