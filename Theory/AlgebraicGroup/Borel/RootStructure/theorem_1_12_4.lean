module

public import Theory.AlgebraicGroup.Borel.RootStructure.theorem_1_12_1
public import Theory.AlgebraicGroup.Borel.RootStructure.FundamentalCorootData

/-!
This module isolates `theorem_1_12_4` from `Theory.AlgebraicGroup.Borel.RootStructure`.
It retains the declarations following that unresolved result up to the next
unresolved result, preserving the source order and public API of the GLS3
algebraic-group development.  The theorem is stated with the notation of
Theorem 1.12.1: in particular, `T` is a maximal torus and `D` is an actual
root-group realization.  These hypotheses are needed for the generation of
`Variety.Point K` by the Chevalley root elements; the separate
`IsRootSystemRealization` hypothesis supplies the chosen root-system
coordinates used by the four presentation conclusions.

The center-shape vocabulary following the numbered theorem exposes its
case-split implementation for the three classification branches.  Public
`iff` lemmas provide stable roots-of-unity elimination rules, while the
generator-table validity predicate keeps its body hidden behind type-specific
behavior theorems.
-/

set_option warningAsError false

universe u v w

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem theorem_1_12_4
    {K : Variety k} [AlgebraicGroup K]
    (hK : IsSemisimpleAlgebraicGroup K)
    (T : ClosedSubgroup K) (D : RootGroupData K T)
    (hT : IsMaximalTorus T) (hD : D.IsRealization)
    (C : ChevalleyData K D)
    {ι R M N : Type u} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic]
    [P.IsReduced] (base : P.Base) (e : D.Root ≃ ι)
    (hRealization : IsRootSystemRealization D P e base)
    (hChevalley : IsChevalleySystem D C P e base) :
    (IsUniversalVersion K →
      ∃ data : ChevalleyRelationData D P e base,
      ∃ presentationIso :
        PresentedGroup (universalChevalleyRelators data) ≃* Variety.Point K,
        ∀ generator, presentationIso (PresentedGroup.of generator) =
          evaluateFormalChevalleyGenerator C generator) ∧
    (IsAdjointVersion K →
      ∃ data : ChevalleyRelationData D P e base,
      ∃ presentationIso :
        PresentedGroup (adjointChevalleyRelators data) ≃* Variety.Point K,
        ∀ generator, presentationIso (PresentedGroup.of generator) =
          evaluateFormalChevalleyGenerator C generator) ∧
    (∀ {Ku : Variety k} [AlgebraicGroup Ku]
      (hKu : IsUniversalVersion Ku)
      (Tu : ClosedSubgroup Ku) (Du : RootGroupData Ku Tu)
      (Cu : ChevalleyData Ku Du)
      {ι' R' M' N' : Type u} [Finite ι'] [Field R'] [CharZero R']
      [AddCommGroup M'] [Module R' M'] [AddCommGroup N'] [Module R' N']
      (P' : RootPairing ι' R' M' N') [P'.IsRootSystem]
      [P'.IsCrystallographic] [P'.IsReduced]
      (base' : P'.Base) (e' : Du.Root ≃ ι')
      (hRealization' : IsRootSystemRealization Du P' e' base')
      (hChevalley' : IsChevalleySystem Du Cu P' e' base')
      (φ : AlgebraicGroup.Morphism Ku K) (hφ : IsIsogeny φ),
      ∃ data : ChevalleyRelationData Du P' e' base',
      ∃ extra : CentralKernelHTorusRelations Cu φ,
      ∃ presentationIso :
        PresentedGroup (intermediateChevalleyRelators data Cu φ extra) ≃*
          Variety.Point K,
        ∀ generator, presentationIso (PresentedGroup.of generator) =
          φ.onPoints (evaluateFormalChevalleyGenerator Cu generator)) ∧
    (∀ {Ku Kₐ : Variety k} [AlgebraicGroup Ku] [AlgebraicGroup Kₐ]
      (hKu : IsUniversalVersion Ku) (hKₐ : IsAdjointVersion Kₐ)
      (Tu : ClosedSubgroup Ku) (T₀ : ClosedSubgroup K) (Tₐ : ClosedSubgroup Kₐ)
      (Du : RootGroupData Ku Tu) (D₀ : RootGroupData K T₀)
      (Dₐ : RootGroupData Kₐ Tₐ)
      (hTu : IsMaximalTorus Tu) (hT₀ : IsMaximalTorus T₀)
      (hTₐ : IsMaximalTorus Tₐ)
      (hDu : Du.IsRealization) (hD₀ : D₀.IsRealization)
      (hDₐ : Dₐ.IsRealization)
      {ι' X' Y' : Type u} [Finite ι']
      [AddCommGroup X'] [Module ℝ X'] [AddCommGroup Y'] [Module ℝ Y']
      (P' : RootPairing ι' ℝ X' Y') [P'.IsRootSystem]
      [P'.IsCrystallographic] [P'.IsReduced]
      (base' : P'.Base)
      (eu : Du.Root ≃ ι') (e₀ : D₀.Root ≃ ι') (eₐ : Dₐ.Root ≃ ι')
      (hPu : IsRootSystemRealization Du P' eu base')
      (hP₀ : IsRootSystemRealization D₀ P' e₀ base')
      (hPₐ : IsRootSystemRealization Dₐ P' eₐ base'),
      ∃ Cu' : { C : ChevalleyData Ku Du // IsChevalleySystem Du C P' eu base' },
      ∃ C₀ : { C : ChevalleyData K D₀ // IsChevalleySystem D₀ C P' e₀ base' },
      ∃ Cₐ : { C : ChevalleyData Kₐ Dₐ // IsChevalleySystem Dₐ C P' eₐ base' },
      ∃ φ : { f : AlgebraicGroup.Morphism Ku K // IsIsogeny f },
      ∃ ψ : { f : AlgebraicGroup.Morphism K Kₐ // IsIsogeny f },
        (fun (i : ι') (t : k) => φ.1.onPoints (Cu'.1.x (eu.symm i) t),
         fun (i : ι') (t : k) => ψ.1.onPoints (C₀.1.x (e₀.symm i) t)) =
        (fun (i : ι') (t : k) => C₀.1.x (e₀.symm i) t,
         fun (i : ι') (t : k) => Cₐ.1.x (eₐ.symm i) t)) := by sorry

public inductive SemisimpleCenterShape
  | rootsOfUnity (order : ℕ)
  | productOfSecondRoots
  | trivial

@[expose] public def universalCenterShape (classification : RootClassification) :
    SemisimpleCenterShape :=
  match classification.kind with
  | .A => .rootsOfUnity (classification.rank + 1)
  | .B | .C => .rootsOfUnity 2
  | .D =>
      if classification.rank % 2 = 0 then .productOfSecondRoots
      else .rootsOfUnity 4
  | .E6 => .rootsOfUnity 3
  | .E7 => .rootsOfUnity 2
  | .E8 | .F4 | .G2 => .trivial

@[expose] public def HasCenterShape
    {K : Variety k} [AlgebraicGroup K]
    (shape : SemisimpleCenterShape) : Prop :=
  match shape with
  | .rootsOfUnity order =>
      Nonempty
        (Subgroup.center (Variety.Point K) ≃* rootsOfUnity order k)
  | .productOfSecondRoots =>
      Nonempty
        (Subgroup.center (Variety.Point K) ≃*
          (rootsOfUnity 2 k × rootsOfUnity 2 k))
  | .trivial => Subgroup.center (Variety.Point K) = ⊥

omit [IsAlgClosed k] in
/-- Public elimination rule for the roots-of-unity case of `HasCenterShape`. -/
public theorem hasCenterShape_rootsOfUnity_iff
    {K : Variety k} [AlgebraicGroup K] (order : ℕ) :
    HasCenterShape (K := K) (.rootsOfUnity order) ↔
      Nonempty
        (Subgroup.center (Variety.Point K) ≃* rootsOfUnity order k) :=
  Iff.rfl

@[expose] public def IsCenterHomomorphicImageOfShape
    {K : Variety k} [AlgebraicGroup K]
    (shape : SemisimpleCenterShape) : Prop :=
  match shape with
  | .rootsOfUnity order =>
      ∃ f : rootsOfUnity order k →* Subgroup.center (Variety.Point K),
        Function.Surjective f
  | .productOfSecondRoots =>
      ∃ f : (rootsOfUnity 2 k × rootsOfUnity 2 k) →*
          Subgroup.center (Variety.Point K),
        Function.Surjective f
  | .trivial => Subgroup.center (Variety.Point K) = ⊥

omit [IsAlgClosed k] in
/-- Public elimination rule for the roots-of-unity case of
`IsCenterHomomorphicImageOfShape`. -/
public theorem isCenterHomomorphicImageOfShape_rootsOfUnity_iff
    {K : Variety k} [AlgebraicGroup K] (order : ℕ) :
    IsCenterHomomorphicImageOfShape (K := K) (.rootsOfUnity order) ↔
      ∃ f : rootsOfUnity order k →* Subgroup.center (Variety.Point K),
        Function.Surjective f :=
  Iff.rfl

public def IsValidGeneratorTableClassification
    (classification : RootClassification) : Prop :=
  match classification.kind with
  | .A => 1 ≤ classification.rank
  | .B | .C => 2 ≤ classification.rank
  | .D => 4 ≤ classification.rank
  | .E6 => classification.rank = 6
  | .E7 => classification.rank = 7
  | .E8 => classification.rank = 8
  | .F4 => classification.rank = 4
  | .G2 => classification.rank = 2

/-- A type-`D` generator table is valid exactly in ranks at least four. -/
public theorem isValidGeneratorTableClassification_typeD_iff (m : ℕ) :
    IsValidGeneratorTableClassification ⟨.D, m⟩ ↔ 4 ≤ m :=
  Iff.rfl

/- The exceptional `E₈` row is valid only at its fixed rank. -/
public theorem isValidGeneratorTableClassification_typeE8_iff (m : ℕ) :
    IsValidGeneratorTableClassification ⟨.E8, m⟩ ↔ m = 8 :=
  Iff.rfl

public structure NumberedDynkinBase
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) (classification : RootClassification) where
  rootNumbering : Fin classification.rank ≃ base.support
  cartan_table : ∀ i j,
    base.cartanMatrixIn ℤ (rootNumbering i) (rootNumbering j) =
      dynkinCartanEntry classification i j

public def numberedCorootWord
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (C : ChevalleyData K D)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {base : P.Base} (e : D.Root ≃ ι)
    {classification : RootClassification}
    (numbered : NumberedDynkinBase P base classification)
    (parameters : Fin classification.rank → kˣ) : Variety.Point K :=
  (List.ofFn fun i =>
    C.h (e.symm (numbered.rootNumbering i)) (parameters i)).prod

public def centerGeneratorTable
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (C : ChevalleyData K D)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {base : P.Base} (e : D.Root ≃ ι)
    (classification : RootClassification)
    (numbered : NumberedDynkinBase P base classification) :
    Set (Variety.Point K) :=
  match classification.kind with
  | .A =>
      {g | ∃ ω : kˣ, ω ^ (classification.rank + 1) = 1 ∧
        g = numberedCorootWord C e numbered
          (fun i => ω ^ (i.val + 1))}
  | .B =>
      {numberedCorootWord C e numbered fun i =>
        if i.val + 1 = classification.rank then -1 else 1}
  | .C =>
      {numberedCorootWord C e numbered fun i =>
        if Odd (i.val + 1) then -1 else 1}
  | .D =>
      if classification.rank % 2 = 0 then
        {numberedCorootWord C e numbered fun i =>
            if Odd (i.val + 1) then -1 else 1,
          numberedCorootWord C e numbered fun i =>
            if i.val + 1 = classification.rank - 1 ∨
                i.val + 1 = classification.rank then -1 else 1}
      else
        {g | ∃ ω : kˣ, ω ^ 2 = -1 ∧
          g = numberedCorootWord C e numbered fun i =>
            if i.val + 1 = classification.rank - 1 then ω
            else if i.val + 1 = classification.rank then -ω
            else if Odd (i.val + 1) then -1
            else 1}
  | .E6 =>
      {g | ∃ ω : kˣ, ω ^ 3 = 1 ∧
        g = numberedCorootWord C e numbered fun i =>
          if i.val + 1 = 1 ∨ i.val + 1 = 5 then ω
          else if i.val + 1 = 2 ∨ i.val + 1 = 6 then ω ^ 2
          else 1}
  | .E7 =>
      {numberedCorootWord C e numbered fun i =>
        if i.val + 1 = 4 ∨ i.val + 1 = 5 ∨ i.val + 1 = 7 then -1
        else 1}
  | .E8 | .F4 | .G2 => ∅

end Theory.AlgebraicGroup
