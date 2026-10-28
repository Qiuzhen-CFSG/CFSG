module

public import Theory.AlgebraicGroup.Bor1.Differential
public import Theory.AlgebraicGroup.Bor1.DiagonalizableTangentSemisimple
public import Theory.AlgebraicGroup.Representations.Algebraic.WeightSpaces

/-!
# Fixed tangent lifting for diagonalizable conjugation

For a commuting family of semisimple endomorphisms, a surjective equivariant
linear map lifts every vector fixed by the family to a fixed vector.  The
proof uses the simultaneous eigenspace decomposition and discards all joint
eigenspaces whose character is not trivial.  The algebraic-group wrapper
uses conjugation naturality of the identity differential.  A diagonalizable
closed subgroup supplies both the commuting source points and semisimplicity
of their induced tangent conjugation operators.  The module sits below the
maximal-torus and Borel developments.

This is the tangent-space form of Bor1, Chapter 3, Proposition 9.6.
-/

universe u v w

set_option linter.unusedSectionVars false

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A surjective map of finite-dimensional spaces lifts a vector fixed by a
commuting semisimple family to a vector fixed by that family. -/
public lemma fixed_lift_of_commuting_semisimple
    {ι V W : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (f : V →ₗ[k] W) (hf : Function.Surjective f)
    (a : ι → Module.End k V)
    (hcomm : ∀ i j, Commute (a i) (a j))
    (hsemi : ∀ i, (a i).IsSemisimple)
    (x : W)
    (hfixed : ∀ i, ∀ v, f (a i v) = f v) :
    ∃ v : V, f v = x ∧ ∀ i, a i v = v := by
  classical
  obtain ⟨y, rfl⟩ := hf x
  have htop : (⨆ χ : ι → k, ⨅ i, (a i).eigenspace (χ i)) = ⊤ :=
    commutingSemisimple_iSup_eigenspace_eq_top a hcomm hsemi
  have hy : y ∈ ⨆ χ : ι → k, ⨅ i, (a i).eigenspace (χ i) := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨z, hz, hsum⟩ :=
    (Submodule.mem_iSup_iff_exists_finsupp
      (fun χ : ι → k => ⨅ i, (a i).eigenspace (χ i)) y).mp hy
  let z' : V := z.sum (fun χ v => if (∀ i, χ i = 1) then v else 0)
  have hz' : f z' = f y := by
    change f (z.sum (fun χ v => if (∀ i, χ i = 1) then v else 0)) = f y
    rw [← hsum]
    simp only [Finsupp.sum]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro χ hχ
    by_cases hχ1 : ∀ i, χ i = 1
    · simp [hχ1]
    · simp only [hχ1, ite_false, map_zero]
      obtain ⟨i, hi⟩ := not_forall.mp hχ1
      have hzχ := hz χ
      rw [Submodule.mem_iInf] at hzχ
      have hmem : z χ ∈ (a i).eigenspace (χ i) := hzχ i
      have heig : a i (z χ) = χ i • z χ :=
        Module.End.mem_eigenspace_iff.mp hmem
      have hmap := hfixed i (z χ)
      have hzero : (χ i - 1) • f (z χ) = 0 := by
        calc
          (χ i - 1) • f (z χ) = f (a i (z χ)) - f (z χ) := by
            rw [heig, map_smul, sub_smul, one_smul]
          _ = 0 := sub_eq_zero.mpr hmap
      have hscalar : χ i - 1 ≠ 0 := sub_ne_zero.mpr hi
      exact (smul_eq_zero.mp hzero).resolve_left hscalar |>.symm
  refine ⟨z', hz', ?_⟩
  intro i
  change a i (z.sum (fun χ v => if (∀ j, χ j = 1) then v else 0)) =
    z.sum (fun χ v => if (∀ j, χ j = 1) then v else 0)
  simp only [Finsupp.sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro χ hχ
  by_cases hχ1 : ∀ j, χ j = 1
  · have hmem := hz χ
    rw [Submodule.mem_iInf] at hmem
    have heig : a i (z χ) = χ i • z χ :=
      Module.End.mem_eigenspace_iff.mp (hmem i)
    simp [hχ1, heig]
  · simp [hχ1]

/-- Diagonalizable closed subgroups have commutative point groups. -/
private theorem IsDiagonalizableClosedSubgroup.isMulCommutative
    {G : Variety k} [AlgebraicGroup G] {S : ClosedSubgroup G}
    (hS : IsDiagonalizableClosedSubgroup S) :
    IsMulCommutative (Variety.Point S.carrierVariety) := by
  obtain ⟨n, D, ⟨e⟩⟩ := hS
  let _ : AlgebraicGroup D.carrierVariety := D.carrierAlgebraicGroup
  rw [isMulCommutative_iff]
  intro x y
  have hdiag := dVariety_isMulCommutative (k := k) n
  rw [isMulCommutative_iff] at hdiag
  have hxy : e.hom.onPoints x * e.hom.onPoints y =
      e.hom.onPoints y * e.hom.onPoints x := by
    apply D.inclusion_injective
    exact hdiag (D.inclusion.onPoints (e.hom.onPoints x))
      (D.inclusion.onPoints (e.hom.onPoints y))
  have h := congrArg e.inv.onPoints hxy
  simpa only [map_mul, e.hom_inv_id] using h

private lemma identityTangentConjugationLinearMap_eq_id_of_central
    {Q : Variety k} [AlgebraicGroup Q]
    (q : Variety.Point Q)
    (hq : ∀ x : Variety.Point Q, Commute q x) :
    identityTangentConjugationLinearMap Q q = LinearMap.id := by
  apply LinearMap.ext
  intro D
  apply Derivation.ext
  intro p
  rw [LinearMap.id_apply]
  rw [identityTangentConjugationLinearMap_apply]
  change D ((AlgebraicGroup.conjugationByMorphism Q q).pullbackAlgHom p) = D p
  apply congrArg D
  apply Variety.PolynomialFunction.ext
  intro x
  change p ((AlgebraicGroup.conjugationByMorphism Q q).toFun x) = p x
  rw [AlgebraicGroup.conjugationByMorphism_apply]
  congr 1
  calc
    q * x * q⁻¹ = (x * q) * q⁻¹ := by rw [(hq x).eq]
    _ = x := by simp

/-- Fixed tangent lifting for a diagonalizable conjugation action. -/
public theorem identityTangentMorphismLinearMap_fixed_lift
    {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]
    (f : AlgebraicGroup.Morphism G Q)
    (S : ClosedSubgroup G)
    (hS : IsDiagonalizableClosedSubgroup S)
    (hdf : Function.Surjective (identityTangentMorphismLinearMap f))
    (hcentral : ∀ s : Variety.Point S.carrierVariety,
      ∀ q : Variety.Point Q, Commute (f.onPoints (S.includePoint s)) q)
    (x : IdentityPointDerivation Q) :
    ∃ y : IdentityPointDerivation G,
      identityTangentMorphismLinearMap f y = x ∧
        ∀ s : Variety.Point S.carrierVariety,
          identityTangentConjugationLinearMap G (S.includePoint s) y = y := by
  have hScomm := IsDiagonalizableClosedSubgroup.isMulCommutative hS
  rw [isMulCommutative_iff] at hScomm
  have hcomm : ∀ s t : Variety.Point S.carrierVariety,
      Commute (identityTangentConjugationLinearMap G (S.includePoint s))
        (identityTangentConjugationLinearMap G (S.includePoint t)) := by
    intro s t
    have hst : S.includePoint s * S.includePoint t =
        S.includePoint t * S.includePoint s := by
      calc
        S.includePoint s * S.includePoint t = S.includePoint (s * t) :=
          (S.inclusion.map_mul s t).symm
        _ = S.includePoint (t * s) := congrArg S.includePoint (hScomm s t)
        _ = S.includePoint t * S.includePoint s := S.inclusion.map_mul t s
    change (identityTangentConjugationLinearMap G (S.includePoint s)).comp
        (identityTangentConjugationLinearMap G (S.includePoint t)) =
      (identityTangentConjugationLinearMap G (S.includePoint t)).comp
        (identityTangentConjugationLinearMap G (S.includePoint s))
    rw [← identityTangentConjugationLinearMap_mul, hst,
      identityTangentConjugationLinearMap_mul]
  have hfixed : ∀ s : Variety.Point S.carrierVariety,
      ∀ y : IdentityPointDerivation G,
        identityTangentMorphismLinearMap f
            (identityTangentConjugationLinearMap G (S.includePoint s) y) =
          identityTangentMorphismLinearMap f y := by
    intro s y
    change ((identityTangentMorphismLinearMap f).comp
        (identityTangentConjugationLinearMap G (S.includePoint s))) y =
      identityTangentMorphismLinearMap f y
    rw [identityTangentMorphismLinearMap_conjugation_naturality]
    rw [identityTangentConjugationLinearMap_eq_id_of_central]
    · simp
    · intro q
      exact hcentral s q
  exact fixed_lift_of_commuting_semisimple
    (identityTangentMorphismLinearMap f) hdf
    (fun s : Variety.Point S.carrierVariety ↦
      identityTangentConjugationLinearMap G (S.includePoint s))
    hcomm
    (IsDiagonalizableClosedSubgroup.identityTangentConjugationLinearMap_isSemisimple
      S hS)
    x hfixed

/-- The point-commutative-target specialization of
`identityTangentMorphismLinearMap_fixed_lift`. -/
public theorem identityTangentMorphismLinearMap_fixed_lift_of_commutative_target
    {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]
    (f : AlgebraicGroup.Morphism G Q)
    (S : ClosedSubgroup G)
    (hS : IsDiagonalizableClosedSubgroup S)
    (hdf : Function.Surjective (identityTangentMorphismLinearMap f))
    (hQcomm : IsMulCommutative (Variety.Point Q))
    (x : IdentityPointDerivation Q) :
    ∃ y : IdentityPointDerivation G,
      identityTangentMorphismLinearMap f y = x ∧
        ∀ s : Variety.Point S.carrierVariety,
          identityTangentConjugationLinearMap G (S.includePoint s) y = y := by
  rw [isMulCommutative_iff] at hQcomm
  apply identityTangentMorphismLinearMap_fixed_lift f S hS hdf
  intro s q
  exact hQcomm _ _

end Theory.AlgebraicGroup.Bor1
