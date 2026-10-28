module

public import Theory.AlgebraicGroup.Representations.Algebraic.WeightSetFinite
public import Theory.AlgebraicGroup.RightTranslation.Representation
public import Theory.AlgebraicGroup.Tori.Character.Operations
public import Theory.AlgebraicGroup.Unipotent.SemisimpleCommutator
public import Theory.AlgebraicGroup.Irreducible.Product

/-!
# Regular elements in a maximal torus

For a maximal torus `T`, the finite nonzero weight spaces of the faithful
coordinate-translation representation determine a point whose weights are all
distinct.  A finite-union argument on the connected torus supplies this point.
The resulting eigenspace calculation identifies its full point centralizer with
`T.centralizer`, which gives the regular witness used by the Cartan construction.

Source: Borel, *Linear Algebraic Groups*, second edition, Chapter 3, §8.18.
-/

namespace Theory.AlgebraicGroup

open scoped BigOperators

universe u v

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G] {V : Type v}
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]

omit [IsAlgClosed k] in
theorem regularTorus_eigen_mem_weight (ρ : RationalRepresentation G V) (T : ClosedSubgroup G)
    (hTop : (⨆ χ : TorusWeight T, weightSpace ρ T χ) = ⊤)
    (t : Variety.Point T.carrierVariety)
    (χ : TorusWeight T) (v : V)
    (hχ : χ ∈ representationWeights ρ T)
    (hsep : ∀ ψ : TorusWeight T, ψ ∈ representationWeights ρ T →
      χ ∈ representationWeights ρ T → ψ ≠ χ →
      ψ.pointCharacter t ≠ χ.pointCharacter t)
    (hveigen : (ρ.action (T.includePoint t) : Module.End k V) v =
      χ.pointCharacter t • v) :
    v ∈ weightSpace ρ T χ := by
  obtain ⟨f, hfmem, hfy⟩ :=
    (Submodule.mem_iSup_iff_exists_finsupp
      (fun ψ : TorusWeight T => weightSpace ρ T ψ) v).mp (by
        rw [hTop]
        exact Submodule.mem_top)
  let s := f.support
  have hsum : ∑ i ∈ s,
      (i.pointCharacter t - χ.pointCharacter t) • f i = 0 := by
    have hcalc :
        (∑ i ∈ s, (i.pointCharacter t - χ.pointCharacter t) • f i) =
          (ρ.action (T.includePoint t) : Module.End k V)
              (f.sum (fun _i x => x)) -
            χ.pointCharacter t • f.sum (fun _i x => x) := by
      simp only [Finsupp.sum, map_sum, sub_smul, Finset.sum_sub_distrib,
        Finset.smul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [show (ρ.action (T.includePoint t) : Module.End k V) (f i) =
        i.pointCharacter t • f i from (hfmem i) t]
    rw [hcalc, hfy, hveigen]
    simp
  have hcomp : ∀ i ∈ s, i ≠ χ → f i = 0 := by
    intro i hi hne
    have hiweight : f i ∈ weightSpace ρ T i := hfmem i
    have hInd := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero
      (fun ψ : TorusWeight T => weightSpace ρ T ψ)).mp
      (weightSpace_iSupIndep ρ T)
    have hz := hInd s (fun j =>
      (j.pointCharacter t - χ.pointCharacter t) • f j)
      (fun j hj => (weightSpace ρ T j).smul_mem _ (hfmem j)) hsum i hi
    have hi' : i ∈ representationWeights ρ T := by
      have hfi0 : f i ≠ 0 := Finsupp.mem_support_iff.mp hi
      simpa [representationWeights] using
        (show weightSpace ρ T i ≠ ⊥ from by
          intro hbot
          apply hfi0
          have hzero : f i ∈ (⊥ : Submodule k V) := hbot ▸ hfmem i
          simpa only [Submodule.mem_bot] using hzero)
    have hscalar : i.pointCharacter t - χ.pointCharacter t ≠ 0 :=
      sub_ne_zero.mpr (hsep i hi' hχ hne)
    exact (smul_eq_zero.mp hz).resolve_left hscalar
  have hsumf : f.sum (fun _i x => x) = f χ := by
    rw [Finsupp.sum]
    apply Finset.sum_eq_single χ
    · intro i hi hne
      exact hcomp i hi hne
    · intro hχs
      by_contra hzero
      exact hχs (Finsupp.mem_support_iff.mpr hzero)
  rw [← hfy, hsumf]
  exact hfmem χ
omit [IsAlgClosed k] in
theorem regularTorus_commute_of_separated_weights
    {G : Variety k} [AlgebraicGroup G] {V : Type v}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : RationalRepresentation G V) (T : ClosedSubgroup G)
    (hTop : (⨆ χ : TorusWeight T, weightSpace ρ T χ) = ⊤)
    (t : Variety.Point T.carrierVariety)
    (hsep : ∀ χ ψ : TorusWeight T,
      χ ∈ representationWeights ρ T → ψ ∈ representationWeights ρ T →
      χ ≠ ψ → χ.pointCharacter t ≠ ψ.pointCharacter t)
    (A : Module.End k V)
    (hAt : Commute A (ρ.action (T.includePoint t) : Module.End k V)) :
    ∀ s : Variety.Point T.carrierVariety,
      Commute A (ρ.action (T.includePoint s) : Module.End k V) := by
  have hpres : ∀ (χ : TorusWeight T) (v : V),
      v ∈ weightSpace ρ T χ → A v ∈ weightSpace ρ T χ := by
    intro χ v hv
    by_cases hχ : χ ∈ representationWeights ρ T
    · have hAeigen :
          (ρ.action (T.includePoint t) : Module.End k V) (A v) =
            χ.pointCharacter t • A v := by
        change ((ρ.action (T.includePoint t) : Module.End k V) * A) v = _
        rw [← hAt.eq, Module.End.mul_apply, hv t, map_smul]
      exact (regularTorus_eigen_mem_weight ρ T hTop t χ (A v) hχ
        (fun ψ hψ hχ' hne => hsep ψ χ hψ hχ' hne) hAeigen)
    · have hbot : weightSpace ρ T χ = ⊥ := by
        simpa [representationWeights] using hχ
      rw [hbot] at hv
      have hvzero : v = 0 := by simpa using hv
      subst v
      simp
  intro s
  rw [commute_iff_eq]
  apply LinearMap.ext
  intro v
  apply Submodule.iSup_induction
    (fun χ : TorusWeight T => weightSpace ρ T χ)
    (motive := fun y =>
      A ((ρ.action (T.includePoint s) : Module.End k V) y) =
        (ρ.action (T.includePoint s) : Module.End k V) (A y))
    (show v ∈ ⨆ χ : TorusWeight T, weightSpace ρ T χ by
      rw [hTop]
      exact Submodule.mem_top)
  · intro χ y hy
    have hAy := hpres χ y hy
    have hyweight := hy s
    have hAyweight := hAy s
    rw [hyweight, map_smul, hAyweight]
  · simp
  · intro y z hy hz
    simpa only [map_add] using congrArg₂ (· + ·) hy hz




public theorem exists_regularTorus_separating_point
    {G : Variety k} [AlgebraicGroup G] {V : Type v}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : RationalRepresentation G V) (T : ClosedSubgroup G)
    (hT : IsTorus T.carrierVariety) :
    ∃ t : Variety.Point T.carrierVariety,
      ∀ χ ψ : TorusWeight T,
        χ ∈ representationWeights ρ T → ψ ∈ representationWeights ρ T →
        χ ≠ ψ → χ.pointCharacter t ≠ ψ.pointCharacter t := by
  classical
  let W : Finset (TorusWeight T) :=
    (representationWeights_finite ρ T).toFinset
  let P : Finset (TorusWeight T × TorusWeight T) :=
    (W.product W).filter (fun p => p.1 ≠ p.2)
  let D : Finset (Set (Variety.Point T.carrierVariety)) :=
    P.image (fun p =>
      ((p.1 * p.2⁻¹ : TorusCharacter T.carrierVariety).kernelClosedSubgroup :
        Set (Variety.Point T.carrierVariety)))
  have hW (χ : TorusWeight T) : χ ∈ W ↔ χ ∈ representationWeights ρ T := by
    exact (representationWeights_finite ρ T).mem_toFinset
  have hDclosed : ∀ z ∈ D, IsClosed z := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨p, hp, rfl⟩
    exact (p.1 * p.2⁻¹ : TorusCharacter T.carrierVariety).kernelClosedSubgroup.isClosed'
  have hDproper : ∀ z ∈ D, ¬ ((Set.univ : Set (Variety.Point T.carrierVariety)) ⊆ z) := by
    intro z hz hfull
    rcases Finset.mem_image.mp hz with ⟨p, hp, rfl⟩
    have hpne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    have hδ : (p.1 * p.2⁻¹ : TorusCharacter T.carrierVariety) ≠ 1 := by
      intro heq
      exact hpne (mul_inv_eq_one.mp heq)
    obtain ⟨a, ha⟩ := exists_unit_zpow_ne_one (k := k) (z := (1 : ℤ)) one_ne_zero
    have ha1 : (a : k) ≠ 1 := by simpa using ha
    obtain ⟨x, hx⟩ := TorusCharacter.exists_pointCharacter_eq_of_ne_one hT
      (p.1 * p.2⁻¹ : TorusCharacter T.carrierVariety) hδ (a : k) a.ne_zero
    have hxker : x ∈
        ((p.1 * p.2⁻¹ : TorusCharacter T.carrierVariety).kernelClosedSubgroup :
          Set (Variety.Point T.carrierVariety)) := hfull (Set.mem_univ x)
    have hxone : (p.1 * p.2⁻¹ : TorusCharacter T.carrierVariety).pointCharacter x = 1 := by
      change (p.1 * p.2⁻¹ : TorusCharacter T.carrierVariety).onPoints x = 1
        at hxker
      change (dPointEquiv 1
        ((p.1 * p.2⁻¹ : TorusCharacter T.carrierVariety).onPoints x) 0 : k) = 1
      rw [hxker]
      simp [dPointEquiv_one]
    exact ha1 (hx.symm.trans hxone)
  have hirr : IsIrreducible (Set.univ : Set (Variety.Point T.carrierVariety)) :=
    connectedAlgebraicGroup_irreducible T.carrierVariety hT.isConnected
  have hnotcover : ¬ ((Set.univ : Set (Variety.Point T.carrierVariety)) ⊆
      ⋃₀ (D : Set (Set (Variety.Point T.carrierVariety)))) := by
    intro hcover
    obtain ⟨z, hzD, hzsub⟩ := isIrreducible_iff_sUnion_isClosed.mp hirr D
      hDclosed hcover
    exact hDproper z hzD hzsub
  obtain ⟨t, _, ht⟩ := Set.not_subset.mp hnotcover
  refine ⟨t, ?_⟩
  intro χ ψ hχ hψ hne hEq
  have hp : (χ, ψ) ∈ P := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨(hW χ).mpr hχ, (hW ψ).mpr hψ⟩, hne⟩
  have hbad : t ∈
      ((χ * ψ⁻¹ : TorusCharacter T.carrierVariety).kernelClosedSubgroup :
        Set (Variety.Point T.carrierVariety)) := by
    change (χ * ψ⁻¹ : TorusCharacter T.carrierVariety).onPoints t = 1
    have hval : (χ * ψ⁻¹ : TorusCharacter T.carrierVariety).pointCharacter t = 1 := by
      change (dPointEquiv 1 ((χ * ψ⁻¹).onPoints t) 0 : k) = 1
      change (dPointEquiv 1 (χ.onPoints t * (ψ.onPoints t)⁻¹) 0 : k) = 1
      have hmul := congrFun (dPointEquiv_mul 1 (χ.onPoints t) ((ψ.onPoints t)⁻¹)) 0
      rw [hmul]
      simp only [Pi.mul_apply]
      rw [Units.val_mul]
      have hinv : (dPointEquiv 1 (ψ.onPoints t)⁻¹ 0 : k) =
          (dPointEquiv 1 (ψ.onPoints t) 0 : k)⁻¹ := by
        have hu := congrFun (dPointEquiv_mul 1 (ψ.onPoints t) ((ψ.onPoints t)⁻¹)) 0
        have hu' := congrArg (fun z : kˣ => (z : k)) hu
        rw [mul_inv_cancel, dPointEquiv_one] at hu'
        simp only [Pi.mul_apply] at hu'
        rw [Units.val_mul] at hu'
        exact (eq_inv_of_mul_eq_one_right (by simpa using hu'.symm))
      rw [hinv]
      have hh : (dPointEquiv 1 (χ.onPoints t) 0 : k) =
          (dPointEquiv 1 (ψ.onPoints t) 0 : k) := hEq
      rw [hh]
      exact mul_inv_cancel₀ (Units.ne_zero _)
    change (χ * ψ⁻¹ : TorusCharacter T.carrierVariety).onPoints t = 1
    apply (dPointEquiv 1).injective
    funext i
    fin_cases i
    apply Units.ext
    exact hval
  have hmemD :
      ((χ * ψ⁻¹ : TorusCharacter T.carrierVariety).kernelClosedSubgroup :
        Set (Variety.Point T.carrierVariety)) ∈ D := by
    exact Finset.mem_image.mpr ⟨(χ, ψ), hp, rfl⟩
  exact ht (Set.mem_sUnion.mpr ⟨_, hmemD, hbad⟩)

omit [IsAlgClosed k] in
public theorem regularTorus_centralizer_eq
    {G : Variety k} [AlgebraicGroup G] {V : Type v}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : RationalRepresentation G V)
    (hfaith : Function.Injective ρ.action)
    (T : ClosedSubgroup G)
    (hTop : (⨆ χ : TorusWeight T, weightSpace ρ T χ) = ⊤)
    (t : Variety.Point T.carrierVariety)
    (hsep : ∀ χ ψ : TorusWeight T,
      χ ∈ representationWeights ρ T → ψ ∈ representationWeights ρ T →
      χ ≠ ψ → χ.pointCharacter t ≠ ψ.pointCharacter t) :
    semisimpleCommutatorPointCentralizer (T.includePoint t) = T.centralizer := by
  apply SetLike.coe_injective
  ext x
  constructor
  · intro hx
    change x ∈ Subgroup.centralizer (T.toSubgroup : Set (Variety.Point G))
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have htx : (T.includePoint t) * x = x * (T.includePoint t) := by
      have hx' : x ∈ Subgroup.centralizer
          ({T.includePoint t} : Set (Variety.Point G)) := hx
      exact (Subgroup.mem_centralizer_iff.mp hx') _ (by simp)
    have hmul : ρ.action x * ρ.action (T.includePoint t) =
        ρ.action (T.includePoint t) * ρ.action x := by
      simpa only [map_mul] using congrArg ρ.action htx.symm
    have hAt : Commute (ρ.action x : Module.End k V)
        (ρ.action (T.includePoint t) : Module.End k V) := by
      change ((ρ.action x * ρ.action (T.includePoint t) :
        LinearMap.GeneralLinearGroup k V) : Module.End k V) =
        ((ρ.action (T.includePoint t) * ρ.action x :
          LinearMap.GeneralLinearGroup k V) : Module.End k V)
      exact congrArg (fun z : LinearMap.GeneralLinearGroup k V =>
        (z : Module.End k V)) hmul
    let u : Variety.Point T.carrierVariety := T.pointEquiv.symm ⟨y, hy⟩
    have hu : T.includePoint u = y := by
      change (T.pointEquiv u).val = y
      simp [u]
    have hc := regularTorus_commute_of_separated_weights ρ T hTop t hsep (ρ.action x : Module.End k V) hAt u
    have hGL : ρ.action x * ρ.action y = ρ.action y * ρ.action x := by
      rw [← hu]
      apply Units.ext
      exact hc.eq
    have hxy : x * y = y * x := by
      apply hfaith
      simpa only [map_mul] using hGL
    exact hxy.symm
  · intro hx
    change x ∈ Subgroup.centralizer ({T.includePoint t} : Set (Variety.Point G))
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyt : y = T.includePoint t := Set.mem_singleton_iff.mp hy
    subst y
    have htx : (T.includePoint t) * x = x * (T.includePoint t) :=
      (Subgroup.mem_centralizer_iff.mp hx) (T.includePoint t)
        ((T.pointEquiv t).property)
    exact htx



/-- A maximal torus contains a point whose full semisimple point centralizer is
exactly the torus centralizer. -/
public theorem exists_regularTorusElement_centralizer_eq
    {G : Variety k} [AlgebraicGroup G]
    {T : ClosedSubgroup G} (hT : IsMaximalTorus T) :
    ∃ t : Variety.Point G, t ∈ T.toSubgroup ∧
      semisimpleCommutatorPointCentralizer t = T.centralizer := by
  let ρ := coordinateTranslationRationalRepresentation G
  let V := coordinateTranslationSubmodule G
  let : Module.Finite k V := coordinateTranslationSubmodule_finite G
  have hTop : (⨆ χ : TorusWeight T, weightSpace ρ T χ) = ⊤ :=
    closedSubtorusRepresentation_weightSpace_iSup_eq_top ρ
      (coordinateTranslationRationalRepresentation_isRational G) T hT.1
  obtain ⟨t, hsep⟩ := exists_regularTorus_separating_point ρ T hT.1
  have hcentral :
      semisimpleCommutatorPointCentralizer (T.includePoint t) = T.centralizer :=
    regularTorus_centralizer_eq ρ (coordinateTranslationRepresentation_injective G)
      T hTop t hsep
  exact ⟨T.includePoint t, (T.pointEquiv t).property, hcentral⟩

/-- A maximal torus contains a point whose semisimple point centralizer has the
same identity component as the torus centralizer. -/
public theorem exists_regularTorusElement_identityComponentAmbient_eq
    {G : Variety k} [AlgebraicGroup G]
    {T : ClosedSubgroup G} (hT : IsMaximalTorus T) :
    ∃ t : Variety.Point G, t ∈ T.toSubgroup ∧
      (semisimpleCommutatorPointCentralizer t).identityComponentAmbient =
        T.centralizer.identityComponentAmbient := by
  obtain ⟨t, ht, hcentral⟩ := exists_regularTorusElement_centralizer_eq hT
  exact ⟨t, ht, congrArg ClosedSubgroup.identityComponentAmbient hcentral⟩

end Theory.AlgebraicGroup
