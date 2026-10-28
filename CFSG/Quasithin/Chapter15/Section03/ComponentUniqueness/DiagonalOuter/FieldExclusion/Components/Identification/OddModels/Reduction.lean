module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.SimpleSection
public import Theory.SpecificGroups.SU3.OddThreeLocal.CyclicSylow
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import Theory.GroupAction.AutomorphismFixedTransport
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# Transport and unitary parameter exclusion for the odd models

Transport the involution's ordinary component through an actual group
isomorphism, retaining subnormality in the whole fixed group. This also
supplies nonsolvability for the concrete automorphism calculations.

For PSU₃(p) with p congruent to one modulo three, a cyclic torus has index
prime to three. Thus every Sylow three-subgroup is cyclic, excluding the
rank-two input. In particular, this excludes PSU₃(7). The unitary field
retains order p² and the stored Frobenius conjugation throughout.

Finally, a genuine PSL₃ model over a seven-element field is transported to
the canonical ZMod 7 model. Neither this field transport nor the component
transport asserts the missing involution-centralizer classification.

Source: Aschbacher--Smith, combined 1 March 2004 manuscript, proof of 15.3.38,
printed p.1137, and Theorem C, printed p.33. The cyclic unitary torus calculation
is Huppert II.10.12, used through `SU3.OddThreeLocal.CyclicSylow`.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification

variable {S : Type*} [Group S] (s : SimpleInput S)
include s

/-- Transport the ordinary fixed component, including its relative subnormality. -/
theorem SimpleInput.exists_fixed_component_of_equiv
    {H : Type*} [Group H] (e : S ≃* H) :
    ∃ D : Subgroup (MulAut.congr e s.involution).fixedSubgroup,
      IsComponent (MulAut.congr e s.involution).fixedSubgroup D ∧
        Nonempty (D ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) := by
  let f := MulAut.fixedSubgroupCongr e s.involution
  exact ⟨s.component.map f.toMonoidHom, s.isComponent.map_equiv f,
    ⟨(s.component.equivMapOfInjective f.toMonoidHom f.injective).symm.trans s.equiv⟩⟩

/-- The torus excludes every fixed-field prime congruent to one modulo three. -/
theorem SimpleInput.not_unitary_three_of_mod_one [Finite S]
    {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1) :
    ¬ ClassicalGroup.IsPSU S 3 p := by
  rintro ⟨F, hF, hfin, J, hcard, hconj, ⟨a⟩⟩
  let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_equiv S a.toEquiv
  let P : Sylow 3 (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) := default
  have hc := BenderSuzuki.MatrixGroups.HermitianForm.OddThreeLocal.cyclic_three_sylow_of_prime_mod_one
    J p hp hmod hcard hconj P
  have hr := P.primeRank_le_one_of_isCyclic hc
  rw [← primeRank_equiv 3 a, s.rank] at hr
  omega

/-- The supplied ordinary component makes every isomorphic model nonsolvable. -/
theorem SimpleInput.not_isSolvable_of_equiv {H : Type*} [Group H] (e : S ≃* H) :
    ¬ Group.IsSolvable H := by
  intro h
  let := h
  let : Group.IsSolvable S := Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  let := s.isComponent.2
  let : IsSimpleGroup (s.component ⧸ center s.component) := IsQuasisimple.simple
  let : Nontrivial s.component := (QuotientGroup.mk'_surjective (center s.component)).nontrivial
  exact Group.IsPerfect.not_isSolvable s.component inferInstance

omit s in
private theorem linear_prime_equiv {n p : ℕ} [Fact p.Prime]
    (h : ClassicalGroup.IsPSL S n p) :
    Nonempty (S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod p)) := by
  obtain ⟨F, hF, hfin, hcard, ⟨a⟩⟩ := h
  let := Fintype.ofFinite F
  let e : F ≃+* ZMod p := (ZMod.ringEquivOfPrime F (Fact.out : p.Prime)
    (by simpa only [Nat.card_eq_fintype_card] using hcard)).symm
  exact ⟨a.trans (Atlas.fieldEquivPSL (F := F) (K := ZMod p) n e)⟩

omit s in
/-- Normalize an actual seven-element coefficient field to the canonical prime field. -/
theorem linear_three_seven_equiv
    (h : ClassicalGroup.IsPSL S 3 7) :
    Nonempty (S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 7)) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact linear_prime_equiv h

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification
