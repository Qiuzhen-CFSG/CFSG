module

public import Theory.AlgebraicGroup.Borel.RootStructure.theorem_1_11_5

/-!
This module isolates `theorem_1_12_1` from `Theory.AlgebraicGroup.Borel.RootStructure`.
It retains the declarations following that unresolved result up to the next
unresolved result, preserving the source order and public API of the GLS3
algebraic-group development.
-/

set_option warningAsError false

universe u v w

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem theorem_1_12_1
    {K : Variety k} [AlgebraicGroup K] (hK : IsSemisimpleAlgebraicGroup K)
    (T : ClosedSubgroup K) (D : RootGroupData K T)
    (hT : IsMaximalTorus T) (hD : D.IsRealization)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic]
    [P.IsReduced] (e : D.Root ≃ ι) (b : P.Base)
    (hActual : IsRootSystemRealization D P e b) :
    ∃ C : ChevalleyData K D, SourceChevalleyRelations D C P e b := by sorry

public inductive FormalChevalleyGenerator (Root : Type u) (K : Type u) [Monoid K]
  | x (root : Root) (parameter : K)
  | n (root : Root) (parameter : Kˣ)
  | h (root : Root) (parameter : Kˣ)

public def formalChevalleyX {Root : Type u} {K : Type u} [Monoid K]
    (α : Root) (t : K) : FreeGroup (FormalChevalleyGenerator Root K) :=
  FreeGroup.of (.x α t)

public def formalChevalleyN {Root : Type u} {K : Type u} [Monoid K]
    (α : Root) (t : Kˣ) : FreeGroup (FormalChevalleyGenerator Root K) :=
  FreeGroup.of (.n α t)

public def formalChevalleyH {Root : Type u} {K : Type u} [Monoid K]
    (α : Root) (t : Kˣ) : FreeGroup (FormalChevalleyGenerator Root K) :=
  FreeGroup.of (.h α t)

@[simp] public theorem formalChevalleyX_eq {Root : Type u} {K : Type u} [Monoid K]
    (α : Root) (t : K) :
    formalChevalleyX α t = FreeGroup.of (.x α t) := by
  rfl

@[simp] public theorem formalChevalleyN_eq {Root : Type u} {K : Type u} [Monoid K]
    (α : Root) (t : Kˣ) :
    formalChevalleyN α t = FreeGroup.of (.n α t) := by
  rfl

@[simp] public theorem formalChevalleyH_eq {Root : Type u} {K : Type u} [Monoid K]
    (α : Root) (t : Kˣ) :
    formalChevalleyH α t = FreeGroup.of (.h α t) := by
  rfl

public def formalRelation {Root : Type u} {K : Type u} [Monoid K]
    (lhs rhs : FreeGroup (FormalChevalleyGenerator Root K)) :
    FreeGroup (FormalChevalleyGenerator Root K) := lhs * rhs⁻¹

@[simp] public theorem formalRelation_eq
    {Root : Type u} {K : Type u} [Monoid K]
    (lhs rhs : FreeGroup (FormalChevalleyGenerator Root K)) :
    formalRelation lhs rhs = lhs * rhs⁻¹ := by
  rfl

public structure ChevalleyRelationData
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι R M N : Type u} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base) where
  commutatorOrder : D.Root → D.Root → List (ChevalleyCommutatorTerm D.Root)
  commutatorCoefficient : D.Root → D.Root → ChevalleyCommutatorTerm D.Root → k
  commutatorOrderNodup : ∀ α β,
    AreLinearlyIndependentRoots D P e α β → (commutatorOrder α β).Nodup
  commutatorOrderSorted : ∀ α β,
    AreLinearlyIndependentRoots D P e α β →
      (commutatorOrder α β).Pairwise (fun q r => q.i + q.j ≤ r.i + r.j)
  commutatorOrderMem : ∀ α β,
    AreLinearlyIndependentRoots D P e α β → ∀ q,
      q ∈ commutatorOrder α β ↔ IsValidChevalleyCommutatorTerm D P e α β q
  commutatorCoefficientExpected : ∀ α β,
    AreLinearlyIndependentRoots D P e α β → ∀ q ∈ commutatorOrder α β,
      HasExpectedChevalleyCoefficient D P e α β q (commutatorCoefficient α β q)
  corootCoefficient : D.Root → base.support → ℤ
  corootExpansion : ∀ α,
    P.coroot (e α) = ∑ i, corootCoefficient α i • P.coroot i
  reflectionSign : D.Root → D.Root → kˣ
  reflectionSignValue : ∀ α β,
    reflectionSign α β = 1 ∨ reflectionSign α β = -1

public inductive IsCommonChevalleyRelator
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T}
    {ι R M N : Type u} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {e : D.Root ≃ ι} {base : P.Base}
    (data : ChevalleyRelationData D P e base) :
    FreeGroup (FormalChevalleyGenerator D.Root k) → Prop
  | nDefinition (α : D.Root) (t : kˣ) :
      IsCommonChevalleyRelator data <| formalRelation
        (formalChevalleyN α t)
        (formalChevalleyX α (t : k) * formalChevalleyX (D.neg α) (-((t : k)⁻¹)) *
          formalChevalleyX α (t : k))
  | hDefinition (α : D.Root) (t : kˣ) :
      IsCommonChevalleyRelator data <| formalRelation
        (formalChevalleyH α t)
        ((formalChevalleyN α 1)⁻¹ * formalChevalleyN α t)
  | rootAddition (α : D.Root) (t s : k) :
      IsCommonChevalleyRelator data <| formalRelation
        (formalChevalleyX α t * formalChevalleyX α s) (formalChevalleyX α (t + s))
  | rootCommutator (α β : D.Root)
      (_hIndependent : AreLinearlyIndependentRoots D P e α β) (t s : k) :
      IsCommonChevalleyRelator data <| formalRelation
        ((formalChevalleyX α t)⁻¹ * (formalChevalleyX β s)⁻¹ *
          formalChevalleyX α t * formalChevalleyX β s)
        ((data.commutatorOrder α β).map fun q =>
          formalChevalleyX q.root
            (data.commutatorCoefficient α β q * t ^ q.i * s ^ q.j)).prod
  | torusCommutes (α β : D.Root) (t s : kˣ) :
      IsCommonChevalleyRelator data <| formalRelation
        ((formalChevalleyH α t)⁻¹ * (formalChevalleyH β s)⁻¹ *
          formalChevalleyH α t * formalChevalleyH β s) 1
  | torusMultiplication (α : D.Root) (t s : kˣ) :
      IsCommonChevalleyRelator data <| formalRelation
        (formalChevalleyH α t * formalChevalleyH α s)
        (formalChevalleyH α (t * s))
  | corootExpansion (α : D.Root) (t : kˣ) :
      IsCommonChevalleyRelator data <| formalRelation
        (formalChevalleyH α t)
        (base.support.attach.toList.map fun i : base.support =>
          formalChevalleyH (e.symm i) (t ^ data.corootCoefficient α i)).prod
  | torusConjugatesRoot (α β : D.Root) (t : k) (s : kˣ) :
      IsCommonChevalleyRelator data <| formalRelation
        ((formalChevalleyH β s)⁻¹ * formalChevalleyX α t * formalChevalleyH β s)
        (formalChevalleyX α ((s : k) ^ D.pairing α β * t))
  | reflectionConjugatesRoot (α β : D.Root) (t : k) :
      IsCommonChevalleyRelator data <| formalRelation
        ((formalChevalleyN β 1)⁻¹ * formalChevalleyX α t * formalChevalleyN β 1)
        (formalChevalleyX (D.reflect β α) ((data.reflectionSign α β : k) * t))
  | reflectionConjugatesTorus (α β : D.Root) (t : kˣ) :
      IsCommonChevalleyRelator data <| formalRelation
        ((formalChevalleyN β 1)⁻¹ * formalChevalleyH α t * formalChevalleyN β 1)
        (formalChevalleyH (D.reflect β α) t)
  | reflectionConjugatesReflection (α β : D.Root) (t : kˣ) :
      IsCommonChevalleyRelator data <| formalRelation
        ((formalChevalleyN β 1)⁻¹ * formalChevalleyN α t * formalChevalleyN β 1)
        (formalChevalleyN (D.reflect β α) (data.reflectionSign α β * t))
  | reflectionSquare (α : D.Root) :
      IsCommonChevalleyRelator data <| formalRelation
        (formalChevalleyN α 1 * formalChevalleyN α 1)
        (formalChevalleyH α (-1))

public def universalChevalleyRelators
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T}
    {ι R M N : Type u} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {e : D.Root ≃ ι} {base : P.Base}
    (data : ChevalleyRelationData D P e base) :
    Set (FreeGroup (FormalChevalleyGenerator D.Root k)) :=
  { word | IsCommonChevalleyRelator data word }

public theorem mem_universalChevalleyRelators
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T}
    {ι R M N : Type u} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {e : D.Root ≃ ι} {base : P.Base}
    (data : ChevalleyRelationData D P e base)
    (word : FreeGroup (FormalChevalleyGenerator D.Root k)) :
    word ∈ universalChevalleyRelators data ↔ IsCommonChevalleyRelator data word := by
  rfl

public def adjointTorusRelators
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T}
    {ι R M N : Type u} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {e : D.Root ≃ ι} {base : P.Base} :
    Set (FreeGroup (FormalChevalleyGenerator D.Root k)) :=
  { word | ∃ t : base.support → kˣ,
      (∀ j, (∏ i, t i ^ D.pairing (e.symm j) (e.symm i)) = 1) ∧
      word = formalRelation
        (base.support.attach.toList.map fun i : base.support =>
          formalChevalleyH (e.symm i) (t i)).prod 1 }

public def adjointChevalleyRelators
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T}
    {ι R M N : Type u} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {e : D.Root ≃ ι} {base : P.Base}
    (data : ChevalleyRelationData D P e base) :
    Set (FreeGroup (FormalChevalleyGenerator D.Root k)) :=
  universalChevalleyRelators data ∪ adjointTorusRelators
    (D := D) (P := P) (e := e) (base := base)

public theorem mem_adjointChevalleyRelators
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T}
    {ι R M N : Type u} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {e : D.Root ≃ ι} {base : P.Base}
    (data : ChevalleyRelationData D P e base)
    (word : FreeGroup (FormalChevalleyGenerator D.Root k)) :
    word ∈ adjointChevalleyRelators data ↔
      word ∈ universalChevalleyRelators data ∨
        word ∈ adjointTorusRelators (D := D) (P := P) (e := e) (base := base) := by
  rfl

public def evaluateFormalChevalleyGenerator
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (C : ChevalleyData K D) :
    FormalChevalleyGenerator D.Root k → Variety.Point K
  | .x α t => C.x α t
  | .n α t => C.n α t
  | .h α t => C.h α t

@[simp] public theorem evaluateFormalChevalleyGenerator_x
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (C : ChevalleyData K D) (α : D.Root) (t : k) :
    evaluateFormalChevalleyGenerator C (.x α t) = C.x α t := by
  rfl

@[simp] public theorem evaluateFormalChevalleyGenerator_n
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (C : ChevalleyData K D) (α : D.Root) (t : kˣ) :
    evaluateFormalChevalleyGenerator C (.n α t) = C.n α t := by
  rfl

@[simp] public theorem evaluateFormalChevalleyGenerator_h
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (C : ChevalleyData K D) (α : D.Root) (t : kˣ) :
    evaluateFormalChevalleyGenerator C (.h α t) = C.h α t := by
  rfl

public theorem mem_universalChevalleyRelators_iff
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T}
    {ι R M N : Type u} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {e : D.Root ≃ ι} {base : P.Base}
    (data : ChevalleyRelationData D P e base) (word) :
    word ∈ universalChevalleyRelators data ↔ IsCommonChevalleyRelator data word := by
  rfl

@[simp] public theorem lift_evaluate_formalChevalleyX
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (C : ChevalleyData K D) (α : D.Root) (t : k) :
    FreeGroup.lift (evaluateFormalChevalleyGenerator C) (formalChevalleyX α t) =
      C.x α t := by
  rw [formalChevalleyX_eq, FreeGroup.lift_apply_of,
    evaluateFormalChevalleyGenerator_x]

@[simp] public theorem lift_evaluate_formalChevalleyN
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (C : ChevalleyData K D) (α : D.Root) (t : kˣ) :
    FreeGroup.lift (evaluateFormalChevalleyGenerator C) (formalChevalleyN α t) =
      C.n α t := by
  rw [formalChevalleyN_eq, FreeGroup.lift_apply_of,
    evaluateFormalChevalleyGenerator_n]

@[simp] public theorem lift_evaluate_formalChevalleyH
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (C : ChevalleyData K D) (α : D.Root) (t : kˣ) :
    FreeGroup.lift (evaluateFormalChevalleyGenerator C) (formalChevalleyH α t) =
      C.h α t := by
  rw [formalChevalleyH_eq, FreeGroup.lift_apply_of,
    evaluateFormalChevalleyGenerator_h]

public theorem lift_evaluate_formalRelation
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (C : ChevalleyData K D) (lhs rhs) :
    FreeGroup.lift (evaluateFormalChevalleyGenerator C) (formalRelation lhs rhs) =
      FreeGroup.lift (evaluateFormalChevalleyGenerator C) lhs *
        (FreeGroup.lift (evaluateFormalChevalleyGenerator C) rhs)⁻¹ := by
  rw [formalRelation_eq, map_mul, map_inv]

public def FormalHTorusWord (Root : Type u) (K : Type u) [Monoid K] :=
  FreeGroup (Root × Kˣ)

public instance formalHTorusWordGroup (Root : Type u) (K : Type u) [Monoid K] :
    Group (FormalHTorusWord Root K) :=
  inferInstanceAs (Group (FreeGroup (Root × Kˣ)))

public def includeFormalHTorusWord {Root : Type u} {K : Type u} [Monoid K] :
    FormalHTorusWord Root K →* FreeGroup (FormalChevalleyGenerator Root K) :=
  show FreeGroup (Root × Kˣ) →* FreeGroup (FormalChevalleyGenerator Root K) from
    FreeGroup.lift fun z => formalChevalleyH z.1 z.2

public def evaluateFormalHTorusWord
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (C : ChevalleyData K D) :
    FormalHTorusWord D.Root k →* Variety.Point K :=
  show FreeGroup (D.Root × kˣ) →* Variety.Point K from
    FreeGroup.lift fun z => C.h z.1 z.2

public structure CentralKernelHTorusRelations
    {Ku K : Variety k} [AlgebraicGroup Ku] [AlgebraicGroup K]
    {Tu : ClosedSubgroup Ku} {Du : RootGroupData Ku Tu}
    (Cu : ChevalleyData Ku Du) (φ : AlgebraicGroup.Morphism Ku K) where
  words : Set (FormalHTorusWord Du.Root k)
  evaluatesCentrally : ∀ w ∈ words,
    evaluateFormalHTorusWord Cu w ∈ Subgroup.center (Variety.Point Ku)
  generatesKernel :
    Subgroup.closure (evaluateFormalHTorusWord Cu '' words) = φ.kernel

public def intermediateChevalleyRelators
    {Ku K : Variety k} [AlgebraicGroup Ku] [AlgebraicGroup K]
    {Tu : ClosedSubgroup Ku} {Du : RootGroupData Ku Tu}
    {ι R M N : Type u} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {eu : Du.Root ≃ ι} {base : P.Base}
    (data : ChevalleyRelationData Du P eu base)
    (Cu : ChevalleyData Ku Du) (φ : AlgebraicGroup.Morphism Ku K)
    (extra : CentralKernelHTorusRelations Cu φ) :
    Set (FreeGroup (FormalChevalleyGenerator Du.Root k)) :=
  universalChevalleyRelators data ∪ includeFormalHTorusWord '' extra.words

end Theory.AlgebraicGroup
