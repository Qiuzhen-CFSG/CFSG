module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.AmbientExtensions.DegreeThreeModels.BinaryExtension
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.GoldschmidtAlternatives.Models
public import Theory.SpecificGroups.SU3.BinaryG2Comparison
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTransfer

/-!
# The two surviving unitary ambient models

Over a field of order nine the special-to-projective scalar kernel is
trivial: its scalar has both cube one and eighth power one. The natural
projective map therefore identifies SU₃(3) with PSU₃(3), and the genuine
exceptional isomorphism identifies either carrier with G₂(2)′.

For the graph extension, conjugation constructs the ambient equivalence
with G₂(2). Its restriction agrees with the original model embedding, and
the specified coefficient action is transported pointwise. This also
identifies the actual generalized Fitting subgroup, without assuming a
split extension or equality between the offender actor and its overgroup.

Source: Aschbacher–Smith, F.6.18(10)–(11), pp.309–310; B.5.1/B.5.6,
pp.99–110; 15.4.18, p.1163. The exceptional comparison is imported with
its Fong and ATLAS source attribution.
-/

public section
open Subgroup
namespace BenderSuzuki.MatrixGroups.HermitianForm
variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)

-- In field order nine the scalar determinant kernel has coprime exponents three and eight.
omit [Finite F] in
private theorem degreeThree_specialToProjective_injective
    (hc : Nat.card F = 3 ^ 2) : Function.Injective J.specialToProjective := by
  apply J.specialToProjective.ker_eq_bot_iff.mp
  apply le_bot_iff.mp
  intro x hx
  have hz : x.val ∈ center (GL (Fin 3) F) := by
    apply Matrix.ProjGenLinGroup.mk_eq_one.mp
    simpa only [J.specialToProjective_apply_val, Subgroup.coe_one] using
      congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
  obtain ⟨u, hu⟩ := hz
  have hu3 : u ^ 3 = 1 := by
    have hd := x.property.2
    change Matrix.GeneralLinearGroup.det x.val = 1 at hd
    rw [← hu, Matrix.GeneralLinearGroup.det_scalar] at hd
    simpa using hd
  have hu8 : u ^ 8 = 1 := by
    have hh := pow_card_eq_one' (x := u)
    simpa [Nat.card_units, hc] using hh
  have hu1 : u = 1 := by
    calc
      u = u ^ 8 * u := by rw [hu8, one_mul]
      _ = (u ^ 3) ^ 3 := by rw [← pow_succ, ← pow_mul]
      _ = 1 := by rw [hu3, one_pow]
  apply Subtype.ext
  change x.val = 1
  simpa only [hu1, map_one] using hu.symm

private noncomputable def degreeThree_specialProjectiveEquiv
    (hc : Nat.card F = 3 ^ 2) :
    J.specialSubgroup ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
  MulEquiv.ofBijective J.specialToProjective
    ⟨degreeThree_specialToProjective_injective J hc, J.specialToProjective_surjective⟩

end BenderSuzuki.MatrixGroups.HermitianForm

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.QuasisimpleComparison.AmbientExtensions
namespace DegreeThreeModels
open GoldschmidtAlternatives Atlas.G2.LieAutomorphismExtensions
universe u w

variable {D : Type u} [Group D] [Finite D]

omit [Finite D] in
/-- Both special and projective unitary models at fixed-field order three
are identified with the actual binary G₂ commutator. -/
theorem unitary_three_equiv (hm : UnitaryThree D 3) :
    Nonempty (D ≃* BinaryDerived) := by
  obtain ⟨F, _, _, J, hc, hf, he⟩ := hm
  let ep := J.projectiveEquivBinaryG2Derived hc hf
  rcases he with he | he
  · obtain ⟨e⟩ := he
    exact ⟨(e.trans (J.degreeThree_specialProjectiveEquiv hc)).trans ep⟩
  · obtain ⟨e⟩ := he
    exact ⟨e.trans ep⟩

/-- Recognition through conjugation preserves the embedded group and its
specified outside action, including nonsplit lifts. -/
theorem graphExtension_three_comparison {M : Type w} [Group M]
    (e₀ : M ≃* BinaryDerived) (a : MulAut M)
    (i : M →* D) (t : D) (hi : Function.Injective i)
    (hindex : i.range.index = 2) (ha : ∀ x, t * i x * t⁻¹ = i (a x))
    (hcore : pCore 2 D = ⊥) :
    ∃ e : D ≃* Atlas.G2.Model (ZMod 2),
      (∀ x, e (i x) = (e₀ x).val) ∧
      (generalizedFitting D).map e.toMonoidHom = BinaryDerived ∧
      ∀ x, e t * (e₀ x).val * (e t)⁻¹ = (e₀ (a x)).val := by
  let j : BinaryDerived →* D := i.comp e₀.symm.toMonoidHom
  have hj : Function.Injective j := hi.comp e₀.symm.injective
  have hrange : j.range = i.range := by
    ext d
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨e₀.symm x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨e₀ x, by simp [j]⟩
  obtain ⟨e, he⟩ := binary_extension_equiv j hj
    (by rw [hrange]; exact hindex) hcore
  have hei (x : M) : e (i x) = (e₀ x).val := by
    simpa only [j, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      e₀.symm_apply_apply] using he (e₀ x)
  let : IsQuasisimple BinaryDerived := binaryDerived_quasisimple
  let : IsQuasisimple M := IsQuasisimple.of_mulEquiv e₀.symm
  have hfit := generalizedFitting_eq_range_of_quasisimple_index_two i hi hindex hcore
  refine ⟨e, hei, ?_, ?_⟩
  · rw [hfit]
    ext g
    constructor
    · rintro ⟨d, ⟨x, rfl⟩, rfl⟩
      change e (i x) ∈ BinaryDerived
      rw [hei]
      exact (e₀ x).property
    · intro hg
      refine ⟨i (e₀.symm ⟨g, hg⟩), ⟨_, rfl⟩, ?_⟩
      change e (i (e₀.symm ⟨g, hg⟩)) = g
      rw [hei, e₀.apply_symm_apply]
  · intro x
    have hh := congrArg e (ha x)
    simpa only [map_mul, map_inv, hei] using hh

/-- The source coefficient-graph extension has the full binary G₂ model,
with its embedded component carried to the literal derived subgroup. -/
theorem unitary_graph_three_equiv
    (hm : UnitaryGraphExtension D 3) (hcore : pCore 2 D = ⊥) :
    ∃ e : D ≃* Atlas.G2.Model (ZMod 2),
      (generalizedFitting D).map e.toMonoidHom = BinaryDerived := by
  obtain ⟨F, _, _, J, hc, hf, hJ, he⟩ := hm
  let ep := J.projectiveEquivBinaryG2Derived hc hf
  rcases he with he | he
  · obtain ⟨i, t, hi, hindex, _, ha⟩ := he
    obtain ⟨e, _, hfit, _⟩ := graphExtension_three_comparison
      ((J.degreeThree_specialProjectiveEquiv hc).trans ep)
      (J.specialGraphAut hJ) i t hi hindex ha hcore
    exact ⟨e, hfit⟩
  · obtain ⟨i, t, hi, hindex, _, ha⟩ := he
    obtain ⟨e, _, hfit, _⟩ := graphExtension_three_comparison ep
      (J.projectiveGraphAut hJ) i t hi hindex ha hcore
    exact ⟨e, hfit⟩

end DegreeThreeModels
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.QuasisimpleComparison.AmbientExtensions
