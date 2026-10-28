module
public import Theory.SpecificGroups.SU3.DefiningSylowProducts.Action
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import BenderSuzuki.External.Huppert.II.theorem_10_12
/-!
# Defining-prime complements do not permute with a full PSU₃ Sylow two-subgroup

For prime fixed-field order p>3, the actual projective unitary group acts on
p³+1 isotropic points. Its root Sylow p-subgroup fixes one point and is
regular on the rest. An original subgroup of order p² or p³ can be conjugated
into this root group. The proved orbit obstruction then forces a permuting
Sylow product into the point stabilizer, contradicting its even index.

A genuine Hermitian basis change transports the calculation to every stored
Gram matrix, retaining the original field involution x↦xᵖ. No soluble-subgroup
classification or root-placement premise remains.
Source: Huppert II.10.12 and Aschbacher–Smith A.3.15 / Proposition1.3.4,
printed pp.50–51 and510–511.
-/
public section
open Subgroup MulAction BenderSuzuki.MatrixGroups BenderSuzuki.External
open scoped Pointwise Matrix
namespace BenderSuzuki.MatrixGroups.HermitianForm.DefiningSylowProducts

/-- The actual isotropic-point action excludes a defining rank-two complement. -/
theorem standard_not_permuting {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) (p : ℕ) (hp : p.Prime) (ho : Odd p) (hlarge : 3<p)
    (hcard : Nat.card E=p^2) (hfixed : Nat.card {x:E // J.conj x=x}=p)
    (hJ : J.form=!![0,0,1;0,1,0;1,0,0])
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (U : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hU : Nat.card U=p^2 ∨ Nat.card U=p^3) :
    (U:Set (ProjectiveSpecialUnitaryMatrixGroup J))*(S:Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≠
      (S:Set (ProjectiveSpecialUnitaryMatrixGroup J))*(U:Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨hX,ρ,a,_,_,hB,ht,htrans,hG,_⟩ := huppert_II_10_12 J p hcard hfixed hJ
  obtain ⟨V,_,hVB,_,_,_,_,_,hV,_,_,_,hreg,_⟩ := ht
  let X := {x : Projectivization E (Fin 3→E) // x∈
    {x | ∃(v:Fin 3→E)(hv:v≠0),x=Projectivization.mk E v hv ∧
      dotProduct (fun i=>J.conj (v i)) (J.form.mulVec v)=0}}
  let : Finite X := Nat.finite_of_card_ne_zero (by change Nat.card X=p^3+1 at hX; omega)
  let : MulAction (ProjectiveSpecialUnitaryMatrixGroup J) X := MulAction.compHom X ρ
  have hXX : Nat.card X=p^3+1 := hX
  let : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by rw [hXX]; have hh:=pow_pos hp.pos 3; omega)
  let : IsPretransitive (ProjectiveSpecialUnitaryMatrixGroup J) X := ⟨by
    intro x y
    obtain ⟨x',hx'⟩ := exists_ne x
    obtain ⟨y',hy'⟩ := exists_ne y
    obtain ⟨g,hg,_⟩ := htrans x x' y y' hx'.symm hy'.symm
    exact ⟨g,hg⟩⟩
  have hindex : 2∣(stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) a).index := by
    rw [index_stabilizer_of_transitive,hXX]
    have hh : p^3%2=1 := by rw [Nat.pow_mod,Nat.odd_iff.mp ho]
    exact Nat.dvd_of_mod_eq_zero (by omega)
  have hdiv : Nat.card (ProjectiveSpecialUnitaryMatrixGroup J)∣(p^3+1)*p^3*(p^2-1) := by
    rw [hG]
    apply Nat.div_dvd_of_dvd
    have hpp : p≤p^2 := by nlinarith
    have hs := Nat.sub_add_cancel hpp
    have hd : p+1∣p^3+1 := ⟨p^2-p+1,by nlinarith⟩
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left ((Nat.gcd_dvd_right 3 (p+1)).trans hd) _) _
  apply UnitaryDefining.root_action_not_permuting p hp ho hlarge hdiv V hV a
    (fun v=>hVB v.property) ?_ hindex S U hU
  intro v x hx hfix
  obtain ⟨w,hw,hu⟩ := hreg x x hx hx
  exact (hu v hfix).trans (hu 1 (by simp)).symm

open HermitianForm.OddPrimeSylow.NormalizedOuter
/-- All stored Hermitian forms, with the original field involution. -/
theorem not_permuting {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) (p : ℕ) (hp : p.Prime) (ho : Odd p) (hlarge : 3<p)
    (hcard : Nat.card E=p^2) (hconj : ∀x,J.conj x=x^p)
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (U : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hU : Nat.card U=p^2 ∨ Nat.card U=p^3) :
    (U:Set (ProjectiveSpecialUnitaryMatrixGroup J))*(S:Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≠
      (S:Set (ProjectiveSpecialUnitaryMatrixGroup J))*(U:Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  intro hperm
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let : Fact p.Prime := ⟨hp⟩
  have hfixed : Nat.card {x:E // J.conj x=x}=p := by
    simpa only [pow_one] using
      FiniteField.card_fixed_of_quadratic_frobenius J.conj p 1 (by decide) (by simpa only [pow_one] using hcard) (by simpa only [pow_one] using hconj)
  obtain ⟨e⟩ := FormTransport.exists_projectiveEquiv J p hcard hfixed
  let S' := S.mapSurjective (f:=e.toMonoidHom) e.surjective
  let U' := U.map e.toMonoidHom
  have hc : Nat.card U'=Nat.card U := card_map_of_injective (f:=e.toMonoidHom) e.injective
  apply standard_not_permuting (FormTransport.standardForm J) p hp ho hlarge hcard hfixed rfl S' U'
    (by rwa [hc])
  have hh := congrArg (Set.image e) hperm
  change (U.map e.toMonoidHom : Set (ProjectiveSpecialUnitaryMatrixGroup (FormTransport.standardForm J))) *
    ((S:Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map e.toMonoidHom : Set (ProjectiveSpecialUnitaryMatrixGroup (FormTransport.standardForm J))) =
      ((S:Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map e.toMonoidHom : Set (ProjectiveSpecialUnitaryMatrixGroup (FormTransport.standardForm J))) *
        (U.map e.toMonoidHom : Set (ProjectiveSpecialUnitaryMatrixGroup (FormTransport.standardForm J)))
  simpa only [Set.image_mul,Subgroup.coe_map,Sylow.coe_coe,MulEquiv.coe_toMonoidHom] using hh
end BenderSuzuki.MatrixGroups.HermitianForm.DefiningSylowProducts
