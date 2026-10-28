module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Theory.AlgebraicGroup.Representations.Operations
public import Theory.AlgebraicGroup.RootSubgroups.Defs
public import Theory.AlgebraicGroup.Tori.Character.Algebra
public import Theory.AlgebraicGroup.Tori.Semisimple

/-!
# Weight spaces of algebraic representations

This module develops simultaneous weight spaces for rational representations
restricted to closed subtori.  Over an algebraically closed field, pulling a
rational representation back to a torus and expanding its regular matrix
coefficients in characters shows that the supremum of all character weight
spaces is the whole module.  The closed-subtorus form is exported for use by
geometric representations; the ambient-torus statement is its top-subgroup
specialization.
-/

universe u v

namespace Theory.AlgebraicGroup

@[expose]
public def IsWeightVector
    {k : Type u} [Field k]
    {G : Variety k} [AlgebraicGroup G] {V : Type v}
    [AddCommGroup V] [Module k V]
    (ρ : RationalRepresentation G V) (T : ClosedSubgroup G)
    (v : V) (χ : TorusWeight T) : Prop :=
  v ≠ 0 ∧ ∀ t : Variety.Point T.carrierVariety,
    (ρ.action (T.includePoint t)).1 v = χ.pointCharacter t • v

section

variable {k : Type u} [Field k]
variable {V : Type v} [AddCommGroup V] [Module k V]

public lemma commutingSemisimple_iSupIndep_eigenspace
    {ι : Type*} (f : ι → Module.End k V)
    (hcomm : ∀ i j, Commute (f i) (f j))
    (hsemisimple : ∀ i, (f i).IsSemisimple) :
    iSupIndep (fun χ : ι → k => ⨅ i, (f i).eigenspace (χ i)) := by
  have hmaps : ∀ i j μ,
      Set.MapsTo (f i) ((f j).maxGenEigenspace μ) ((f j).maxGenEigenspace μ) := by
    intro i j μ
    exact Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) μ
  have hgen := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f hmaps
  simpa only [
    (Module.End.IsSemisimple.isFinitelySemisimple (hsemisimple _)).maxGenEigenspace_eq_eigenspace] using hgen

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

public lemma commutingSemisimple_iSup_eigenspace_eq_top
    {ι : Type*} (f : ι → Module.End k V)
    (hcomm : ∀ i j, Commute (f i) (f j))
    (hsemisimple : ∀ i, (f i).IsSemisimple) :
    (⨆ χ : ι → k, ⨅ i, (f i).eigenspace (χ i)) = ⊤ := by
  have hgen : ∀ i, ⨆ μ, (f i).maxGenEigenspace μ = ⊤ := by
    intro i
    simpa only [
      (Module.End.IsSemisimple.isFinitelySemisimple (hsemisimple i)).maxGenEigenspace_eq_eigenspace]
      using (Module.End.IsSemisimple.iSup_eigenspace_eq_top (hsemisimple i))
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    f (fun i j _ => hcomm i j) hgen
  simpa only [
    (Module.End.IsSemisimple.isFinitelySemisimple (hsemisimple _)).maxGenEigenspace_eq_eigenspace] using htop

end

section
variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public def weightSpace
    {K : Variety k} [AlgebraicGroup K] {V : Type v}
    [AddCommGroup V] [Module k V]
    (ρ : RationalRepresentation K V) (T : ClosedSubgroup K)
    (χ : TorusWeight T) : Submodule k V where
  carrier := {v | ∀ t : Variety.Point T.carrierVariety,
    (ρ.action (T.includePoint t)).1 v = χ.pointCharacter t • v}
  zero_mem' := by simp
  add_mem' hv hw t := by simp [hv t, hw t]
  smul_mem' c v hv t := by simp [hv t, smul_comm c]

@[expose]
public def representationWeights
    {K : Variety k} [AlgebraicGroup K] {V : Type v}
    [AddCommGroup V] [Module k V]
    (ρ : RationalRepresentation K V) (T : ClosedSubgroup K) : Set (TorusWeight T) :=
  {χ | weightSpace ρ T χ ≠ ⊥}

@[expose]
public noncomputable def weightMultiplicity
    {K : Variety k} [AlgebraicGroup K] {V : Type v}
    [AddCommGroup V] [Module k V]
    (ρ : RationalRepresentation K V) (T : ClosedSubgroup K)
    (χ : TorusWeight T) : ℕ :=
  Module.finrank k (weightSpace ρ T χ)

@[expose]
public def fixedSubmodule
    {K : Variety k} [AlgebraicGroup K] {V : Type v}
    [AddCommGroup V] [Module k V]
    (ρ : RationalRepresentation K V) (H : ClosedSubgroup K) : Submodule k V where
  carrier := {v | ∀ h, h ∈ H → (ρ.action h).1 v = v}
  zero_mem' := by simp
  add_mem' hv hw h hh := by simp [hv h hh, hw h hh]
  smul_mem' c v hv h hh := by simp [hv h hh]

@[expose]
public def GeneratesRepresentation
    {K : Variety k} [AlgebraicGroup K] {V : Type v}
    [AddCommGroup V] [Module k V]
    (ρ : RationalRepresentation K V) (v : V) : Prop :=
  ∀ W : Submodule k V, IsInvariantSubmodule ρ W → v ∈ W → W = ⊤

end

section

@[expose]
public def torusWeightCoordinate
    {k : Type*} [Field k] [IsAlgClosed k]
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) :
    TorusWeight T → ({α : D.Root // α ∈ D.simple} → ℤ) :=
  fun weight α => D.weightPairing weight α

@[expose]
public noncomputable def torusCartanMap
    {k : Type*} [Field k] [IsAlgClosed k]
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) [Finite {α : D.Root // α ∈ D.simple}] :
    ({α : D.Root // α ∈ D.simple} → ℤ) →+
      ({α : D.Root // α ∈ D.simple} → ℤ) := by
  classical
  letI := Fintype.ofFinite {α : D.Root // α ∈ D.simple}
  exact AddMonoidHom.mk'
    (fun coefficients α => ∑ β, coefficients β * D.pairing β α)
    (by intro coefficients coefficients'; ext α; simp [add_mul, Finset.sum_add_distrib])

/-- The coordinates of an actual root weight are its Cartan pairings with the
simple roots. -/
public lemma RootGroupData.IsRealization.torusWeightCoordinate_rootWeight
    {k : Type*} [Field k] [IsAlgClosed k]
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (hD : D.IsRealization) (α : D.Root) :
    torusWeightCoordinate D (D.rootWeight α) =
      fun β : {β : D.Root // β ∈ D.simple} => D.pairing α β := by
  funext β
  exact hD.weightPairing_rootWeight α β

end

section

variable {k : Type u} [Field k]

public lemma torusPointAction_commute
    {K : Variety k} [AlgebraicGroup K] {V : Type v}
    [AddCommGroup V] [Module k V]
    (ρ : RationalRepresentation K V) (hK : IsTorus K)
    (s t : Variety.Point K) :
    Commute (ρ.action s : Module.End k V) (ρ.action t : Module.End k V) := by
  have h : ρ.action s * ρ.action t = ρ.action t * ρ.action s := by
    have hcomm := hK.isMulCommutative
    rw [isMulCommutative_iff] at hcomm
    rw [← map_mul, ← map_mul, hcomm s t]
  exact congrArg (fun g : LinearMap.GeneralLinearGroup k V =>
    (g : Module.End k V)) h

end

section

variable {k : Type u} [Field k]

public lemma weightSpace_eq_iInf_pointEigenspace
    {K : Variety k} [AlgebraicGroup K] {V : Type v}
    [AddCommGroup V] [Module k V]
    (ρ : RationalRepresentation K V) (T : ClosedSubgroup K)
    (χ : TorusWeight T) :
    weightSpace ρ T χ =
      ⨅ t : Variety.Point T.carrierVariety,
        Module.End.eigenspace
          (ρ.action (T.includePoint t) : Module.End k V) (χ.pointCharacter t) := by
  ext v
  change (∀ t : Variety.Point T.carrierVariety,
      (ρ.action (T.includePoint t) : Module.End k V) v = χ.pointCharacter t • v) ↔ _
  simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

end

section
variable {k : Type u} [Field k]

public lemma weightSpace_inf_eq_bot_of_ne
    {K : Variety k} [AlgebraicGroup K] {V : Type v}
    [AddCommGroup V] [Module k V]
    (ρ : RationalRepresentation K V) (T : ClosedSubgroup K)
    {χ ψ : TorusWeight T} (hχψ : χ ≠ ψ) :
    weightSpace ρ T χ ⊓ weightSpace ρ T ψ = ⊥ := by
  apply le_antisymm
  · intro v hv
    by_contra hv0
    have hpoint : χ.pointCharacter ≠ ψ.pointCharacter := by
      intro h
      exact hχψ (TorusCharacter.pointCharacter_injective h)
    have hpoint' : ¬ ∀ t, χ.pointCharacter t = ψ.pointCharacter t := by
      intro h
      apply hpoint
      ext t
      exact h t
    obtain ⟨t, ht⟩ := not_forall.mp hpoint'
    have hχ := hv.1 t
    have hψ := hv.2 t
    have hzero : (χ.pointCharacter t - ψ.pointCharacter t) • v = 0 := by
      rw [sub_smul, ← hχ, ← hψ]
      exact sub_self _
    have hscalar : χ.pointCharacter t - ψ.pointCharacter t ≠ 0 := sub_ne_zero.mpr ht
    exact hv0 (smul_eq_zero.mp hzero |>.resolve_left hscalar)
  · exact bot_le

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

public lemma rationalRepresentationMatrixCoefficient_exists_characterExpansion
    {T : Variety k} [AlgebraicGroup T] {V : Type v}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (hT : IsTorus T) (ρ : RationalRepresentation T V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism T (glVarietyOf k V))
    (i j : Fin (Module.finrank k V)) :
    ∃ c : TorusCharacter T →₀ k,
      c.sum (fun χ a => a • χ.scalarPolynomialFunction) =
        rationalRepresentationMatrixCoefficient ρ e f i j := by
  have hmem := polynomialFunction_mem_span_scalarCharacters T hT.isMulCommutative
    hT.all_semisimple
    (rationalRepresentationMatrixCoefficient ρ e f i j)
  exact Finsupp.mem_span_range_iff_exists_finsupp.mp hmem

end

section

variable {k : Type u} [Field k]

/-- The actual algebraic weight spaces of any closed subgroup are independent. -/
public lemma weightSpace_iSupIndep
    {K : Variety k} [AlgebraicGroup K] {V : Type v}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : RationalRepresentation K V) (H : ClosedSubgroup K) :
    iSupIndep (fun χ : TorusWeight H => weightSpace ρ H χ) := by
  classical
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s w hw hsum χ hχ
  by_contra hne
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k hne
  let c : TorusWeight H → k := fun ψ => φ (w ψ)
  have hfun : ∑ ψ ∈ s, c ψ • ψ.scalarPolynomialFunction = 0 := by
    apply Variety.PolynomialFunction.ext
    intro t
    have heval (s' : Finset (TorusWeight H)) :
        (∑ ψ ∈ s', c ψ • ψ.scalarPolynomialFunction :
          H.carrierVariety.PolynomialFunction) t =
          ∑ ψ ∈ s', c ψ * ψ.pointCharacter t := by
      induction s' using Finset.induction_on with
      | empty => rfl
      | @insert ψ s' hψ ih =>
          rw [Finset.sum_insert hψ, Finset.sum_insert hψ]
          change (c ψ • ψ.scalarPolynomialFunction) t +
              (∑ η ∈ s', c η • η.scalarPolynomialFunction :
                H.carrierVariety.PolynomialFunction) t =
            c ψ * ψ.pointCharacter t + ∑ η ∈ s', c η * η.pointCharacter t
          rw [polynomialFunction_smul_apply,
            TorusCharacter.scalarPolynomialFunction_apply, ih]
    rw [heval s, polynomialFunction_zero_apply H.carrierVariety t]
    have haction : ∑ ψ ∈ s, (ρ.action (H.includePoint t)).1 (w ψ) = 0 := by
      rw [← map_sum, hsum, map_zero]
    have hweight : ∀ ψ ∈ s,
        (ρ.action (H.includePoint t)).1 (w ψ) = ψ.pointCharacter t • w ψ := by
      intro ψ hψ
      exact hw ψ hψ t
    have hdual : ∑ ψ ∈ s, c ψ * ψ.pointCharacter t = 0 := by
      calc
        ∑ ψ ∈ s, c ψ * ψ.pointCharacter t =
            φ (∑ ψ ∈ s, (ρ.action (H.includePoint t)).1 (w ψ)) := by
              rw [map_sum]
              apply Finset.sum_congr rfl
              intro ψ hψ
              rw [hweight ψ hψ, map_smul]
              simp [c, mul_comm]
        _ = 0 := by rw [haction, map_zero]
    simpa [mul_comm] using hdual
  have hc : ∀ ψ ∈ s, c ψ = 0 := by
    exact (linearIndependent_iff'.mp
      (torusCharacter_scalarPolynomialFunction_linearIndependent H.carrierVariety)) s c hfun
  have : (1 : k) = 0 := by simpa [c, hφ] using hc χ hχ
  exact one_ne_zero this

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

public lemma commutingSemisimple_isInternal_eigenspace
    {ι : Type*} [DecidableEq (ι → k)] (f : ι → Module.End k V)
    (hcomm : ∀ i j, Commute (f i) (f j))
    (hsemisimple : ∀ i, (f i).IsSemisimple) :
    DirectSum.IsInternal (fun χ : ι → k =>
      ⨅ i, (f i).eigenspace (χ i)) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact commutingSemisimple_iSupIndep_eigenspace f hcomm hsemisimple
  · exact commutingSemisimple_iSup_eigenspace_eq_top f hcomm hsemisimple

end

section
variable {k : Type u} [Field k] [IsAlgClosed k]

private noncomputable def coeff
    {T : Variety k} [AlgebraicGroup T] {V : Type v}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (hT : IsTorus T) (ρ : RationalRepresentation T V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism T (glVarietyOf k V))
    (i j : Fin (Module.finrank k V)) : TorusCharacter T →₀ k :=
  Classical.choose (rationalRepresentationMatrixCoefficient_exists_characterExpansion hT ρ e f i j)

private lemma coeff_spec
    {T : Variety k} [AlgebraicGroup T] {V : Type v}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (hT : IsTorus T) (ρ : RationalRepresentation T V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism T (glVarietyOf k V))
    (i j : Fin (Module.finrank k V)) :
    (coeff hT ρ e f i j).sum (fun χ a => a • χ.scalarPolynomialFunction) =
      rationalRepresentationMatrixCoefficient ρ e f i j :=
  Classical.choose_spec (rationalRepresentationMatrixCoefficient_exists_characterExpansion hT ρ e f i j)

private noncomputable def column
    {T : Variety k} [AlgebraicGroup T] {V : Type v}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (hT : IsTorus T) (ρ : RationalRepresentation T V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism T (glVarietyOf k V))
    (j : Fin (Module.finrank k V)) : TorusCharacter T →₀ V :=
  ∑ i, (coeff hT ρ e f i j).mapRange (fun a => a • e i) (zero_smul k (e i))

private lemma column_coord
    {T : Variety k} [AlgebraicGroup T] {V : Type v}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (hT : IsTorus T) (ρ : RationalRepresentation T V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism T (glVarietyOf k V))
    (j r : Fin (Module.finrank k V)) (χ : TorusCharacter T) :
    e.repr (column hT ρ e f j χ) r = coeff hT ρ e f r j χ := by
  classical
  simp [column, Finsupp.mapRange_apply, Finsupp.single_apply]

private lemma column_expansion
    {T : Variety k} [AlgebraicGroup T] {V : Type v}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (hT : IsTorus T) (ρ : RationalRepresentation T V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism T (glVarietyOf k V))
    (hf : ∀ g, glPointEquivOf k V e (f.onPoints g) = ρ.action g)
    (j : Fin (Module.finrank k V)) (t : Variety.Point T) :
    (column hT ρ e f j).sum
        (fun χ w => χ.pointCharacter t • w) =
      (ρ.action t).1 (e j) := by
  apply e.repr.injective
  ext r
  rw [map_finsuppSum]
  rw [Finsupp.sum_apply]
  have hcoord : (column hT ρ e f j).mapRange (e.coord r) (map_zero (e.coord r)) =
      coeff hT ρ e f r j := by
    ext χ
    exact column_coord hT ρ e f j r χ
  have hspec := congrArg (polynomialFunctionEvalAddHom T t)
    (coeff_spec hT ρ e f r j)
  rw [map_finsuppSum] at hspec
  simp only [polynomialFunctionEvalAddHom_apply,
    polynomialFunction_smul_apply,
    TorusCharacter.scalarPolynomialFunction_apply,
    rationalRepresentationMatrixCoefficient_apply ρ e f hf] at hspec
  calc
    (column hT ρ e f j).sum
        (fun χ w => e.repr (χ.pointCharacter t • w) r) =
        (column hT ρ e f j).sum
          (fun χ w => χ.pointCharacter t * e.repr w r) := by
            apply Finsupp.sum_congr
            intro χ hχ
            simp [Pi.smul_apply, smul_eq_mul]
    _ = ((column hT ρ e f j).mapRange (e.coord r)
        (map_zero (e.coord r))).sum
          (fun χ a => χ.pointCharacter t * a) := by
            simpa using (Finsupp.sum_mapRange_index
              (g := column hT ρ e f j)
              (f := e.coord r)
              (h := fun χ a => χ.pointCharacter t * a)
              (fun χ => mul_zero (χ.pointCharacter t))).symm
    _ = (coeff hT ρ e f r j).sum
          (fun χ a => χ.pointCharacter t * a) := by rw [hcoord]
    _ = e.repr ((ρ.action t).1 (e j)) r := by
          simpa [smul_eq_mul, mul_comm] using hspec

omit [IsAlgClosed k] in
private lemma finite_character_sum_eq_zero
    {T : Variety k} [AlgebraicGroup T] {V : Type v}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (s : Finset (TorusCharacter T)) (vectors : TorusCharacter T → V)
    (hsum : ∀ t : Variety.Point T,
      ∑ χ ∈ s, χ.pointCharacter t • vectors χ = 0) :
    ∀ χ ∈ s, vectors χ = 0 := by
  intro χ hχ
  apply (Module.forall_dual_apply_eq_zero_iff k (vectors χ)).mp
  intro l
  have hLI : LinearIndependent k
      (fun ψ : s => (ψ.1 : TorusCharacter T).scalarPolynomialFunction) :=
    (torusCharacter_scalarPolynomialFunction_linearIndependent T).comp
      Subtype.val Subtype.val_injective
  have hfun : ∑ ψ : s,
      l (vectors ψ.1) • (ψ.1 : TorusCharacter T).scalarPolynomialFunction = 0 := by
    apply Variety.PolynomialFunction.ext
    intro t
    change polynomialFunctionEvalAddHom T t
      (∑ ψ : s, l (vectors ψ.1) •
        (ψ.1 : TorusCharacter T).scalarPolynomialFunction) =
      polynomialFunctionEvalAddHom T t 0
    rw [map_sum, map_zero]
    simp_rw [polynomialFunctionEvalAddHom_apply, polynomialFunction_smul_apply,
      TorusCharacter.scalarPolynomialFunction_apply]
    calc
      (∑ ψ : s, l (vectors ψ.1) * ψ.1.pointCharacter t) =
          l (∑ ψ : s, ψ.1.pointCharacter t • vectors ψ.1) := by
            rw [map_sum]
            apply Finset.sum_congr rfl
            intro ψ _
            rw [map_smul, smul_eq_mul, mul_comm]
      _ = 0 := by
            have ht : (∑ ψ : s, ψ.1.pointCharacter t • vectors ψ.1) = 0 := by
              exact (Finset.sum_coe_sort s
                (fun ψ => ψ.pointCharacter t • vectors ψ)).trans (hsum t)
            rw [ht]
            simp
  exact (Fintype.linearIndependent_iff.mp hLI
    (fun ψ : s => l (vectors ψ.1)) hfun) ⟨χ, hχ⟩

private lemma column_isWeight
    {T : Variety k} [AlgebraicGroup T] {V : Type v}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (hT : IsTorus T) (ρ : RationalRepresentation T V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism T (glVarietyOf k V))
    (hf : ∀ g, glPointEquivOf k V e (f.onPoints g) = ρ.action g)
    (j : Fin (Module.finrank k V)) (χ : TorusCharacter T)
    (t : Variety.Point T) :
    (ρ.action t).1 (column hT ρ e f j χ) =
      χ.pointCharacter t • column hT ρ e f j χ := by
  by_cases hχ : χ ∈ (column hT ρ e f j).support
  · apply sub_eq_zero.mp
    apply finite_character_sum_eq_zero
      (column hT ρ e f j).support
      (fun ψ => (ρ.action t).1 (column hT ρ e f j ψ) -
        ψ.pointCharacter t • column hT ρ e f j ψ) ?_ χ hχ
    intro s
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib]
    have hs := column_expansion hT ρ e f hf j s
    have hts := column_expansion hT ρ e f hf j (t * s)
    change (∑ ψ ∈ (column hT ρ e f j).support,
        ψ.pointCharacter s • (ρ.action t).1 (column hT ρ e f j ψ)) -
      (∑ ψ ∈ (column hT ρ e f j).support,
        ψ.pointCharacter s •
          (ψ.pointCharacter t • column hT ρ e f j ψ)) = 0
    have hfirst : (∑ ψ ∈ (column hT ρ e f j).support,
        ψ.pointCharacter s • (ρ.action t).1 (column hT ρ e f j ψ)) =
        (ρ.action t).1 ((column hT ρ e f j).sum
          (fun ψ w => ψ.pointCharacter s • w)) := by
      rw [map_finsuppSum]
      change (column hT ρ e f j).sum
        (fun ψ w => ψ.pointCharacter s • (ρ.action t).1 w) = _
      apply Finsupp.sum_congr
      intro ψ hψ
      rw [map_smul]
    have hsecond : (∑ ψ ∈ (column hT ρ e f j).support,
        ψ.pointCharacter s •
          (ψ.pointCharacter t • column hT ρ e f j ψ)) =
        (column hT ρ e f j).sum
          (fun ψ w => ψ.pointCharacter (t * s) • w) := by
      change (column hT ρ e f j).sum
        (fun ψ w => ψ.pointCharacter s • (ψ.pointCharacter t • w)) = _
      apply Finsupp.sum_congr
      intro ψ hψ
      rw [smul_smul, map_mul]
      simp only [mul_comm]
    rw [hfirst, hs, hsecond]
    have hmul : (ρ.action t).1 ((ρ.action s).1 (e j)) =
        (ρ.action (t * s)).1 (e j) := by
      rw [map_mul]
      rfl
    rw [hmul, hts, sub_self]
  · have hz : column hT ρ e f j χ = 0 := by
      simpa [Finsupp.mem_support_iff] using hχ
    rw [hz]
    simp

/-- A rational representation restricted to a closed subtorus is spanned by
its character weight spaces. -/
public theorem closedSubtorusRepresentation_weightSpace_iSup_eq_top
    {K : Variety k} [AlgebraicGroup K] {V : Type v}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (T : ClosedSubgroup K) (hT : IsTorus T.carrierVariety) :
    (⨆ χ : TorusWeight T, weightSpace ρ T χ) = ⊤ := by
  obtain ⟨τ, hτρ, hτ⟩ := rationalRepresentation_pullback_exists T.inclusion ρ hρ
  obtain ⟨e, f, hf⟩ := hτ
  rw [Submodule.eq_top_iff_forall_basis_mem (b := e)]
  intro j
  apply (Submodule.mem_iSup_iff_exists_finsupp
    (fun χ : TorusWeight T => weightSpace ρ T χ) (e j)).mpr
  refine ⟨column hT τ e f j, ?_, ?_⟩
  · intro χ t
    have hw := column_isWeight hT τ e f hf j χ t
    rw [hτρ t] at hw
    exact hw
  · simpa using column_expansion hT τ e f hf j
      (1 : Variety.Point T.carrierVariety)

private noncomputable def topClosedSubgroupIso
    (K : Variety k) [AlgebraicGroup K] :
    AlgebraicGroup.Iso K (ClosedSubgroup.top (G := K)).carrierVariety := by
  let T : ClosedSubgroup K := ClosedSubgroup.top
  let toTop : AlgebraicGroup.Morphism K T.carrierVariety :=
    (AlgebraicGroup.Morphism.id K).codRestrictClosedSubgroup T (fun _ => trivial)
  exact {
    hom := toTop
    inv := T.inclusion
    hom_inv_id := by
      intro x
      rfl
    inv_hom_id := by
      intro y
      apply T.inclusion_injective
      dsimp [toTop]
      rfl }

omit [IsAlgClosed k] in
private lemma topClosedSubgroup_isTorus
    (K : Variety k) [AlgebraicGroup K] (hK : IsTorus K) :
    IsTorus (ClosedSubgroup.top (G := K)).carrierVariety := by
  obtain ⟨n, ⟨e⟩⟩ := hK
  exact ⟨n, ⟨(topClosedSubgroupIso K).comp e⟩⟩

public theorem torusRepresentation_weightSpace_iSup_eq_top
    {K : Variety k} [AlgebraicGroup K] {V : Type v}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (hK : IsTorus K) :
    (⨆ χ : TorusWeight (ClosedSubgroup.top (G := K)),
      weightSpace ρ (ClosedSubgroup.top (G := K)) χ) = ⊤ :=
  closedSubtorusRepresentation_weightSpace_iSup_eq_top ρ hρ ClosedSubgroup.top
    (topClosedSubgroup_isTorus K hK)

end
end Theory.AlgebraicGroup
