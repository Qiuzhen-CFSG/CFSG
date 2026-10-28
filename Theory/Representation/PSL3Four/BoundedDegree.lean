module
public import Theory.Representation.PSL3Four.NormalCoreDegree
public import Mathlib.LinearAlgebra.DirectSum.Finite

/-!
# Binary constituent degrees up to twenty-two for PSL₃(4)

The actual SL₃ tensor-word classification and exact Frobenius period give
Schur degree one or two. Enumerating the corresponding words of length one
or two leaves dimensions at most twelve, sixteen or eighteen. The existing
small-degree theorem removes all but one and nine in the first range.

Normal two-cores act trivially on simple binary modules. Clifford's internal
direct sum makes the dimension of an irreducible overgroup module a positive
multiple of its normal constituent dimension. Thus a nontrivial normal
PSL₃(4) core quotient leaves only nine, sixteen or eighteen below twenty-three.
These are necessary alternatives; no extension action or existence of an
eighteen-dimensional simple PSL₃(4) module is asserted.

The actual source consumer bounds its whole secondary radical by 2^22,
including nonabelian numerators, before applying this list to its literal
conjugation sections.
Source: GLS III §§2.8.6, 2.8.8, 2.8.10(c), and Isaacs, Character Theory,
Theorem 6.5; Aschbacher--Smith, conclusion of 4.3.2, pp.618--619.
-/

public section
noncomputable section
open Representation
open scoped MatrixGroups TensorProduct MonoidAlgebra
namespace Representation.PSL3Four
open Representation.SL3.BinaryDefiningFactors
private theorem sl3_degree_le_twenty_two
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) Matrix.PSL3Four.SL V) [ρ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) V ≤ 22) :
    Module.finrank (ZMod 2) V ≤ 12 ∨ Module.finrank (ZMod 2) V = 16 ∨
      Module.finrank (ZMod 2) V = 18 := by
  let E := Module.End (ZMod 2)[Matrix.PSL3Four.SL] ρ.asModule
  let K := AlgebraicClosure E
  let : CharP E 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) E).injective 2
  let : Algebra (ZMod 2) Matrix.PSL3Four.F := ZMod.algebra _ 2
  let : Algebra (ZMod 2) K := ZMod.algebra _ 2
  let : IsAbsolutelyIrreducible ρ.endFieldRep := endFieldRep_isAbsolutelyIrreducible ρ
  let : IsIrreducible (extendScalars K ρ.endFieldRep) :=
    IsAbsolutelyIrreducible.irreducible_of_extension ρ.endFieldRep K
  let ι : Matrix.PSL3Four.F →+* K :=
    (IsAlgClosed.lift (R := ZMod 2) (S := Matrix.PSL3Four.F) (M := K)).toRingHom
  have hF : Nat.card Matrix.PSL3Four.F = 2^2 := Matrix.PSL3Four.card_F
  obtain ⟨w, hw, he⟩ := exists_word_equiv ι 2 hF (extendScalars K ρ.endFieldRep)
  obtain ⟨t,b,ht,hb,hs,_,hdegree⟩ := exists_repeated_block_dimension_of_word_model
    ρ ι w 2 (by decide) hw hF (wordRep_isIrreducible ι 2 hF)
    (fun u v hu hv h => (wordRep_equiv_iff ι 2 hF u v hu hv).mp h) he
  have hspos : 0 < Representation.schurDegree 2 ρ := by nlinarith
  have hsle : Representation.schurDegree 2 ρ ≤ 2 := by nlinarith
  rcases (by omega : Representation.schurDegree 2 ρ = 1 ∨ Representation.schurDegree 2 ρ = 2) with hs' | hs'
  · rw [hs'] at hs hb hdegree
    have ht' : t = 2 := by omega
    rw [ht'] at hdegree
    have hb' : b.length = 1 := hb
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hb'
    cases a <;> simp [naturalCount, adjointCount] at hdegree <;> omega
  · rw [hs'] at hs hb hdegree
    have ht' : t = 1 := by omega
    rw [ht'] at hdegree
    have hb' : b.length = 2 := hb
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hb'
    cases a <;> cases b <;> simp [naturalCount, adjointCount] at hdegree <;> omega

/-- Necessary degrees for a simple binary action within the source radical bound. -/
theorem simple_degree_le_twenty_two
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) Matrix.PSL3Four.PSL V) [ρ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) V ≤ 22) :
    Module.finrank (ZMod 2) V = 1 ∨ Module.finrank (ZMod 2) V = 9 ∨
      Module.finrank (ZMod 2) V = 16 ∨ Module.finrank (ZMod 2) V = 18 := by
  let π := QuotientGroup.mk' (Subgroup.center Matrix.PSL3Four.SL)
  let σ : Representation (ZMod 2) Matrix.PSL3Four.SL V := ρ.comp π
  let : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff π (QuotientGroup.mk'_surjective _) ρ).mpr inferInstance
  rcases sl3_degree_le_twenty_two σ hd with hs | h16 | h18
  · rcases MathieuSmall.M22Recognition.PointRestriction.SimpleDegrees.simple_degree ρ hs with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h16))
  · exact Or.inr (Or.inr (Or.inr h18))

private theorem normal_constituent_dimension
    {F G W : Type*} [Field F] [Group G] [Finite G]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (ρ : Representation F G W) [ρ.IsIrreducible]
    (H : Subgroup G) [H.Normal]
    (J : Subrepresentation (ρ.comp H.subtype)) (hJ : J.toRepresentation.IsIrreducible) :
    ∃ n : ℕ, Module.finrank F W = n * Module.finrank F J.toSubmodule := by
  classical
  obtain ⟨n,g,hi,_,_,_⟩ := isaacs_theorem_6_5.{_,_,_,0} ρ H inferInstance J hJ
  let B := fun i : Fin n => (conjugateSubrepresentation ρ H J (g i)).asSubmodule
  let e := (LinearEquiv.ofBijective (DirectSum.coeLinearMap B) hi).symm |>.trans
    (DirectSum.linearEquivFunOnFintype F[H] (Fin n) _)
  let : ∀ i : Fin n, FiniteDimensional F (B i) := fun i =>
    Module.Finite.of_injective ((B i).subtype.restrictScalars F) (B i).subtype_injective
  have hd := (e.restrictScalars F).finrank_eq
  have hj (i : Fin n) : Module.finrank F (B i) = Module.finrank F J.toSubmodule :=
    (conjugateSubrepresentationEquiv ρ H J (g i)).toLinearEquiv.finrank_eq
  refine ⟨n,?_⟩
  change Module.finrank F W = Module.finrank F ((i : Fin n) → B i) at hd
  simpa only [Module.finrank_pi_fintype,hj,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,smul_eq_mul] using hd


variable {G W : Type*} [Group G] [Finite G]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- The same degree list after killing the original normal two-core. -/
theorem core_simple_degree_le_twenty_two
    (e : (G ⧸ pCore 2 G) ≃* Matrix.PSL3Four.PSL)
    (ρ : Representation (ZMod 2) G W) [ρ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) W ≤ 22) :
    Module.finrank (ZMod 2) W = 1 ∨ Module.finrank (ZMod 2) W = 9 ∨
      Module.finrank (ZMod 2) W = 16 ∨ Module.finrank (ZMod 2) W = 18 := by
  have hk : pCore 2 G ≤ ρ.ker := normal_p_subgroup_le_ker ρ _ pCore_isPGroup
  let τ := quotientOfLEKer ρ (pCore 2 G) hk
  let σ := τ.comp e.symm.toMonoidHom
  let : IsIrreducible τ := (quotientOfLEKer_irreducible_iff ρ _ hk).mpr inferInstance
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective τ).mpr inferInstance
  exact simple_degree_le_twenty_two σ hd

/-- A nontrivial normal component action in degree at most twenty-two has degree nine, sixteen or eighteen. -/
theorem normal_core_simple_degree_le_twenty_two
    (H : Subgroup G) [H.Normal]
    (e : (H ⧸ pCore 2 H) ≃* Matrix.PSL3Four.PSL)
    (ρ : Representation (ZMod 2) G W) [ρ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) W ≤ 22) (hnt : ¬ H ≤ ρ.ker) :
    Module.finrank (ZMod 2) W = 9 ∨ Module.finrank (ZMod 2) W = 16 ∨
      Module.finrank (ZMod 2) W = 18 := by
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial ρ
  have hpos : 0 < Module.finrank (ZMod 2) W := Module.finrank_pos_iff.mpr inferInstance
  obtain ⟨J,hJ⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
    (ρ.comp H.subtype)
  let : J.toRepresentation.IsIrreducible := hJ
  have hj := core_simple_degree_le_twenty_two e J.toRepresentation (J.toSubmodule.finrank_le.trans hd)
  have hjne : Module.finrank (ZMod 2) J.toSubmodule ≠ 1 := by
    intro h1
    apply hnt
    apply le_ker_of_normal_invariants_ne_bot ρ H
    let : Nontrivial J.toSubmodule := Subrepresentation.irreducible_module_nontrivial J.toRepresentation
    obtain ⟨v,hv⟩ := exists_ne (0 : J.toSubmodule)
    have ht (g : H) : J.toRepresentation g v = v := by
      obtain ⟨a,ha⟩ := exists_smul_eq_of_finrank_eq_one h1 hv (J.toRepresentation g v)
      have ha0 : a ≠ 0 := by
        intro he
        have hh : J.toRepresentation g v = 0 := by simpa [he] using ha.symm
        apply hv
        simpa only [J.toRepresentation.inv_self_apply,map_zero] using
          congrArg (J.toRepresentation g⁻¹) hh
      have ha1 : a = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) a ha0
      simpa only [ha1,one_smul] using ha.symm
    intro hb
    have hm : (v : W) ∈ invariants (ρ.comp H.subtype) :=
      fun g => congrArg Subtype.val (ht g)
    rw [hb,Submodule.mem_bot] at hm
    exact hv (Subtype.ext hm)
  obtain ⟨k,hk⟩ := normal_constituent_dimension ρ H J hJ
  rcases hj.resolve_left hjne with h9 | h16 | h18
  · rw [h9] at hk
    omega
  · rw [h16] at hk
    omega
  · rw [h18] at hk
    omega
end Representation.PSL3Four
