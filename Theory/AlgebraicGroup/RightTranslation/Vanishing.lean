module

public import Theory.AlgebraicGroup.ClosedSubgroup.VanishingIdeal
public import Theory.AlgebraicGroup.RightTranslation.Basic

universe u

/-!
The finite-dimensional right-translation space used in Chevalley's
stabilizer construction for a closed subgroup.
-/

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k]

/-- A finite generating set for the polynomial-function vanishing ideal of a
closed subgroup. -/
public structure ClosedSubgroup.VanishingIdealGeneratorData
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) where
  generators : Finset G.PolynomialFunction
  span_eq : Ideal.span (generators : Set G.PolynomialFunction) =
    H.vanishingIdeal

/-- The vanishing ideal has finite generator data. -/
public lemma ClosedSubgroup.exists_vanishingIdealGeneratorData
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    Nonempty H.VanishingIdealGeneratorData := by
  obtain ⟨generators, hspan⟩ := H.vanishingIdeal_fg
  exact ⟨⟨generators, hspan⟩⟩

/-- A fixed finite generating set for the vanishing ideal. -/
@[expose]
public noncomputable def ClosedSubgroup.vanishingIdealGeneratorData
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    H.VanishingIdealGeneratorData :=
  Classical.choice H.exists_vanishingIdealGeneratorData

/-- The sum of the right-translation orbit spans of fixed vanishing-ideal
generators. -/
@[expose]
public noncomputable def ClosedSubgroup.rightTranslateVanishingSpan
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    Submodule k G.PolynomialFunction :=
  ⨆ i : H.vanishingIdealGeneratorData.generators,
    AlgebraicGroup.rightTranslateOrbitSpan G i.1

/-- The right-translation span of the vanishing-ideal generators is finitely
generated. -/
public lemma ClosedSubgroup.rightTranslateVanishingSpan_fg
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    H.rightTranslateVanishingSpan.FG := by
  apply Submodule.fg_iSup
  intro i
  exact AlgebraicGroup.rightTranslateOrbitSpan_fg G i.1

/-- The right-translation span of the vanishing-ideal generators is a finite
dimensional vector space. -/
public noncomputable instance
    ClosedSubgroup.rightTranslateVanishingSpan_moduleFinite
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    Module.Finite k H.rightTranslateVanishingSpan :=
  Module.Finite.of_fg_top
    ((Submodule.fg_top H.rightTranslateVanishingSpan).mpr
      H.rightTranslateVanishingSpan_fg)

/-- Right translation preserves the finite-dimensional generator span. -/
public lemma ClosedSubgroup.rightTranslateVanishingSpan_stable
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (x : Variety.Point G) (q : G.PolynomialFunction)
    (hq : q ∈ H.rightTranslateVanishingSpan) :
    (AlgebraicGroup.rightMulMorphism G x).pullbackAlgHom q ∈
      H.rightTranslateVanishingSpan := by
  let T := (AlgebraicGroup.rightMulMorphism G x).pullbackAlgHom.toLinearMap
  refine Submodule.iSup_induction
    (motive := fun q => T q ∈ H.rightTranslateVanishingSpan)
    (fun i : H.vanishingIdealGeneratorData.generators =>
      AlgebraicGroup.rightTranslateOrbitSpan G i.1) hq ?_ ?_ ?_
  · intro i q hiq
    apply Submodule.mem_iSup_of_mem i
    exact AlgebraicGroup.rightTranslateOrbitSpan_stable G i.1 x q hiq
  · rw [T.map_zero]
    exact H.rightTranslateVanishingSpan.zero_mem
  · intro q r hq hr
    rw [T.map_add]
    exact H.rightTranslateVanishingSpan.add_mem hq hr

/-- Every chosen ideal generator belongs to the finite-dimensional
right-translation span. -/
public lemma ClosedSubgroup.generator_mem_rightTranslateVanishingSpan
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (i : H.vanishingIdealGeneratorData.generators) :
    i.1 ∈ H.rightTranslateVanishingSpan := by
  apply Submodule.mem_iSup_of_mem i
  apply Submodule.subset_span
  exact ⟨1, AlgebraicGroup.rightMul_pullback_one G i.1⟩

/-- Every chosen ideal generator belongs to the vanishing ideal. -/
public lemma ClosedSubgroup.generator_mem_vanishingIdeal
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (i : H.vanishingIdealGeneratorData.generators) :
    i.1 ∈ H.vanishingIdeal := by
  have hi : i.1 ∈ Ideal.span
      (H.vanishingIdealGeneratorData.generators : Set G.PolynomialFunction) :=
    Ideal.subset_span i.property
  rw [H.vanishingIdealGeneratorData.span_eq] at hi
  exact hi

/-- The finite-dimensional subspace of the generator span consisting of
functions vanishing on `H`. -/
@[expose]
public noncomputable def ClosedSubgroup.rightTranslateVanishingSubspace
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    Submodule k G.PolynomialFunction :=
  H.rightTranslateVanishingSpan ⊓ H.vanishingIdeal.restrictScalars k

/-- Every chosen ideal generator belongs to the distinguished vanishing
subspace. -/
public lemma ClosedSubgroup.generator_mem_rightTranslateVanishingSubspace
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (i : H.vanishingIdealGeneratorData.generators) :
    i.1 ∈ H.rightTranslateVanishingSubspace :=
  ⟨H.generator_mem_rightTranslateVanishingSpan i,
    H.generator_mem_vanishingIdeal i⟩

/-- Right translation by a point of `H` preserves the distinguished vanishing
subspace. -/
public lemma ClosedSubgroup.rightTranslateVanishingSubspace_stable_of_mem
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (h : Variety.Point G) (hh : h ∈ H.toSubgroup)
    (q : G.PolynomialFunction)
    (hq : q ∈ H.rightTranslateVanishingSubspace) :
    (AlgebraicGroup.rightMulMorphism G h).pullbackAlgHom q ∈
      H.rightTranslateVanishingSubspace := by
  constructor
  · exact H.rightTranslateVanishingSpan_stable h q hq.1
  · change (AlgebraicGroup.rightMulMorphism G h).pullbackAlgHom q ∈
      H.vanishingIdeal
    rw [H.mem_vanishingIdeal_iff]
    intro y hy
    change q ((AlgebraicGroup.rightMulMorphism G h).toFun y) = 0
    rw [AlgebraicGroup.rightMulMorphism_apply]
    exact (H.mem_vanishingIdeal_iff q).mp hq.2 (y * h)
      (H.toSubgroup.mul_mem hy hh)

/-- Chevalley's finite-dimensional stabilizer criterion: a point belongs to
`H` exactly when its right translation preserves the distinguished vanishing
subspace. -/
public lemma ClosedSubgroup.rightTranslateVanishingSubspace_stabilizer_iff
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (g : Variety.Point G) :
    (∀ q ∈ H.rightTranslateVanishingSubspace,
      (AlgebraicGroup.rightMulMorphism G g).pullbackAlgHom q ∈
        H.rightTranslateVanishingSubspace) ↔
      g ∈ H.toSubgroup := by
  constructor
  · intro hstable
    rw [H.mem_iff_forall_vanishingIdeal]
    let ev : G.PolynomialFunction →+* k :=
      { toFun := fun f => f g
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hgen :
        (H.vanishingIdealGeneratorData.generators :
          Set G.PolynomialFunction) ⊆ RingHom.ker ev := by
      intro f hf
      let i : H.vanishingIdealGeneratorData.generators := ⟨f, hf⟩
      have htranslated := hstable i.1
        (H.generator_mem_rightTranslateVanishingSubspace i)
      have hzero := (H.mem_vanishingIdeal_iff
        ((AlgebraicGroup.rightMulMorphism G g).pullbackAlgHom i.1)).mp
          htranslated.2 (1 : Variety.Point G) H.toSubgroup.one_mem
      change i.1 ((AlgebraicGroup.rightMulMorphism G g).toFun 1) = 0 at hzero
      rw [AlgebraicGroup.rightMulMorphism_apply, one_mul] at hzero
      exact (RingHom.mem_ker).mpr hzero
    have hle : H.vanishingIdeal ≤ RingHom.ker ev := by
      rw [← H.vanishingIdealGeneratorData.span_eq]
      exact Ideal.span_le.mpr hgen
    intro f hf
    exact (RingHom.mem_ker).mp (hle hf)
  · intro hg q hq
    exact H.rightTranslateVanishingSubspace_stable_of_mem g hg q hq

end

end Theory.AlgebraicGroup
