module

public import Theory.Representation.SL2.FieldTrace
public import Theory.Representation.SchurDisplacement.MarkedAction
public import Theory.SpecificGroups.PSL2.OuterInvolutionFormula
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.Representation.Quotient

/-!
# The Schur period of an actual outer binary SL₂ actor

For a self-centralizing normal marked SL₂ layer, a literal outer involution
induces inner times half-degree Frobenius. Schur linearity gives an actual
linear intertwiner on the marked endomorphism-field module. Its trace period
then forces the original Schur degree to divide the half-field degree.
Normality, outerness and scalar linearity are all transported through the
specified marking; no degree window or tensor estimate is assumed.

Source: Guralnick--Malle, Classification of 2F-modules II, §3.5 and
Proposition 4.1(2), manuscript pp.20,22. The ambient Chapter K consumer is
`RankOne.PSL2Recognition.DegreeSelection.Outer.SchurLinear`.
-/

public section

open scoped MatrixGroups MonoidAlgebra
namespace Representation.SL2
variable {G K V : Type*} [Group G] [Field K] [Finite K] [CharP K 2]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [L.Normal]
  (e : L ≃* SL(2,K)) [IsIrreducible (ρ.comp L.subtype)]

/-- Schur linearity of the literal outer actor forces the original Schur field
to have degree dividing the half-degree of the defining field. -/
theorem schurDegree_dvd_half_of_outer_actor {r : ℕ} (hr : 0 < r)
    (hc : Nat.card K = 2 ^ r) (hCL : Subgroup.centralizer (L : Set G) = ⊥)
    (t : G) (ht : t ^ 2 = 1) (htL : t ∉ L) (hlin : IsSchurLinear ρ L t) :
    schurDegree 2 ((ρ.comp L.subtype).comp e.symm.toMonoidHom) ∣ r / 2 := by
  let σ : Representation (ZMod 2) SL(2,K) V := (ρ.comp L.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective
      (ρ.comp L.subtype)).mpr inferInstance
  let a := MulAut.congr e (MulAut.conjNormal (H := L) t)
  have ha : a ^ 2 = 1 := by
    dsimp [a]
    rw [← map_pow, ← map_pow, ht, map_one, map_one]
  have hout : a ∉ MulAut.innerSubgroup SL(2,K) := by
    intro hh
    change MulAut.congr e (MulAut.conjNormal (H := L) t) ∈ _ at hh
    rw [← MulAut.map_innerSubgroup_congr e, Subgroup.mem_map_equiv] at hh
    have hi : t ∈ (MulAut.innerSubgroup L).comap MulAut.conjNormal := by
      change MulAut.conjNormal (H := L) t ∈ MulAut.innerSubgroup L
      simpa only [MulEquiv.symm_apply_apply] using hh
    rw [MulAut.conjNormal_comap_innerSubgroup, hCL, sup_bot_eq] at hi
    exact htL hi
  obtain ⟨_, c, hform⟩ := Theory.PSL2.sl2_outer_involution_formula hr hc a ha hout
  apply schurDegree_dvd_of_field_intertwiner σ (r / 2) c
    (schurLinearMarkedEquiv ρ L e.symm t hlin)
  intro g v
  have hh := schurLinearMarkedEquiv_intertwines ρ L e.symm t hlin g v
  change schurLinearMarkedEquiv ρ L e.symm t hlin (σ.endFieldRep g v) =
    σ.endFieldRep (a g) (schurLinearMarkedEquiv ρ L e.symm t hlin v) at hh
  rw [hform] at hh
  exact hh
end Representation.SL2
