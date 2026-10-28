module

public import Theory.SpecificGroups.PSp4Three.IrreducibleOvergroups.NontrivialTwoCore.Representation
public import Theory.SpecificGroups.PSp4Three.IrreducibleOvergroups.NontrivialTwoCore.CoreLift
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.GroupTheory.Fitting.Centralizer
public import Theory.SpecificGroups.SL2.BinaryTetrahedral
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# A small linear centralizer forces characteristic two

A subgroup of GL₂(3) is solvable and has order dividing 48. For the
centralizer C of a two-core, its characteristic odd core is therefore a
three-group. If the ambient three-core is trivial, this odd core vanishes.
The Fitting subgroup of C is then its two-core; it is central in C because
its ambient image belongs to the original two-core. Fitting
self-centralization forces C to be a two-group.

Faithful irreducibility in characteristic three supplies the vanishing
three-core for the full symplectic preimage. This reduces the relative
centralizer bound to constructing a genuine embedding of C into GL₂(3).
Source application: Aschbacher–Smith, Theorem 0.1.2(4), condition K,
printed pp.4 and 482 of `refs/quasithin.pdf`.
-/

namespace Matrix.PSp4Three.NontrivialTwoCore.Geometry
open Subgroup
private abbrev GL2 := Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)

private theorem gl2_isSolvable : Group.IsSolvable GL2 := by
  let hQ : IsPGroup 2 (QuaternionGroup 2) :=
    IsPGroup.of_card (n := 3) (by norm_num [QuaternionGroup.card])
  let : Group.IsNilpotent (QuaternionGroup 2) := hQ.isNilpotent
  let : Group.IsSolvable
      (QuaternionGroup 2 ⋊[GLS3.Chapter5.SchurPresentation.q8C3Action]
        Multiplicative (ZMod 3)) :=
    Group.isSolvable_of_ker_le_range SemidirectProduct.inl
      SemidirectProduct.rightHom SemidirectProduct.range_inl_eq_ker_rightHom.ge
  let : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) := by
    apply Group.isSolvable_of_surjective
      (f := GLS3.Chapter5.SchurPresentation.binaryTetrahedralEquivSL.toMonoidHom)
    exact GLS3.Chapter5.SchurPresentation.binaryTetrahedralEquivSL.surjective
  let det := Matrix.GeneralLinearGroup.det (n := Fin 2) (R := ZMod 3)
  apply Group.isSolvable_of_ker_le_range (SpecialLinearGroup.toGL (R := ZMod 3)) det
  intro g hg
  let y : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) := ⟨(g : Matrix (Fin 2) (Fin 2) (ZMod 3)), by
    have h := congr_arg Units.val hg
    change Matrix.det (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) = 1 at h
    exact h⟩
  refine ⟨y, ?_⟩
  apply Units.ext
  rfl

/-- A centralizer of the two-core that embeds in GL₂(3) is a two-group,
provided the ambient three-core is trivial. -/
public theorem centralizer_le_twoCore_of_gl2_embedding
    {G : Type*} [Group G] [Finite G] (h3 : pCore 3 G = ⊥)
    (f : centralizer (pCore 2 G : Set G) →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (hf : Function.Injective f) : centralizer (pCore 2 G : Set G) ≤ pCore 2 G := by
  let C := centralizer (pCore 2 G : Set G)
  let : Group.IsSolvable GL2 := gl2_isSolvable
  have hsolv : Group.IsSolvable C :=
    Group.isSolvable_of_isSolvable_injective (f := f) hf
  have hCcard : Nat.card C ∣ 48 := by
    have hcard : Nat.card GL2 = 48 := by rw [Matrix.card_GL_field]; decide
    rw [← hcard]
    exact card_dvd_of_injective f hf
  have hodd : pPrimeCore 2 C = ⊥ := by
    let R := pPrimeCore 2 C
    have hRcard : Nat.card R ∣ 3 := by
      have hc : Nat.Coprime (Nat.card R) (2 ^ 4) :=
        (pPrimeCore_coprime_card (p := 2) (G := C)).symm.pow_right 4
      exact hc.dvd_of_dvd_mul_left ((R.card_subgroup_dvd_card.trans hCcard) :
        Nat.card R ∣ 2 ^ 4 * 3)
    have hRthree : IsPGroup 3 R := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hRcard with h | h
      · exact IsPGroup.of_card (n := 0) h
      · exact IsPGroup.of_card (n := 1) h
    have hRle : R.map C.subtype ≤ pCore 3 G :=
      le_sSup ⟨inferInstance, hRthree.map C.subtype⟩
    rw [h3] at hRle
    apply bot_unique
    intro x hx
    apply Subtype.ext
    exact hRle ⟨x, hx, rfl⟩
  have hmap : (pCore 2 C).map C.subtype ≤ pCore 2 G :=
    le_sSup ⟨inferInstance, pCore_isPGroup.map C.subtype⟩
  have hcentral : pCore 2 C ≤ center C := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact (mem_centralizer_iff.mp y.prop x.val (hmap ⟨x, hx, rfl⟩)).symm
  have hfit := centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv
  rw [Fitting_eq_pcore C 2 hodd] at hfit
  intro g hg
  have hgc : (⟨g, hg⟩ : C) ∈ pCore 2 C := by
    apply hfit
    apply mem_centralizer_iff.mpr
    intro x hx
    exact (mem_center_iff.mp (hcentral hx) ⟨g, hg⟩).symm
  exact hmap ⟨⟨g, hg⟩, hgc, rfl⟩

/-- Faithful irreducibility in characteristic three kills the actual three-core. -/
public theorem fullPreimage_threeCore_eq_bot
    (M : Subgroup (PSp 2 (ZMod 3))) (hred : ¬ HasInvariantSubspace M) :
    pCore 3 (fullPreimage M) = ⊥ := by
  let : Representation.IsIrreducible (fullPreimageRepresentation M) :=
    (fullPreimageRepresentation_irreducible_iff M).mpr hred
  have hker := Representation.normal_p_subgroup_le_ker
    (fullPreimageRepresentation M) (pCore 3 (fullPreimage M)) pCore_isPGroup
  have hk : (fullPreimageRepresentation M).ker = ⊥ :=
    (MonoidHom.ker_eq_bot_iff _).mpr (fullPreimageRepresentation_injective M)
  exact bot_unique (hk ▸ hker)

end Matrix.PSp4Three.NontrivialTwoCore.Geometry
