module

public import Theory.AlgebraicGroup.RootData.Realization
public import Theory.AlgebraicGroup.Morphism.Isogeny

/-!
This module contains the root-model vocabulary and the kernel-checked assembly
interface for Chevalley universal and adjoint versions.  A `RootSystemModel`
records an actual maximal-torus root datum identified with a finite reduced
crystallographic real root pairing.  `SemisimpleVersion` packages such a model
with its carrier group, while the two root-version predicates record the
isogenies to and from every other version.  The final constructor below is a
small bookkeeping definition: the geometric Chevalley construction supplies
its carriers, maps, and canonical comparison isomorphisms separately, and
this module derives pairwise uniqueness and assembles them without using the
unresolved numbered theorem 1.10.3(d).

The definitions mirror GLS3, Chapter 1, Sections 1.9--1.10.  Keeping them in
this lower layer lets concrete Chevalley constructions import the contracts
without inheriting the unresolved compatibility theorem.
-/

universe u v w

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public structure RootSystemModel
    {ι E E' : Type u} [Finite ι]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup E'] [Module ℝ E']
    (P : RootPairing ι ℝ E E') [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (G : Variety k) [AlgebraicGroup G] where
  torus : ClosedSubgroup G
  maximalTorus : IsMaximalTorus torus
  rootData : RootGroupData G torus
  realization : rootData.IsRealization
  base : P.Base
  rootEquiv : rootData.Root ≃ ι
  actual : IsActualBasedRootPairing rootData P base rootEquiv

public structure SemisimpleVersion
    {ι E E' : Type u} [Finite ι]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup E'] [Module ℝ E']
    (P : RootPairing ι ℝ E E') [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] where
  carrier : Variety k
  group : AlgebraicGroup carrier
  semisimple : let := group; IsSemisimpleAlgebraicGroup carrier
  rootModel : let := group; RootSystemModel P carrier

public def SemisimpleVersion.Isomorphic
    {ι E E' : Type u} [Finite ι]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup E'] [Module ℝ E']
    {P : RootPairing ι ℝ E E'} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (V W : SemisimpleVersion (k := k) P) : Prop :=
  letI := V.group
  letI := W.group
  Nonempty (AlgebraicGroup.Iso V.carrier W.carrier)

omit [IsAlgClosed k] in
public theorem SemisimpleVersion.isomorphic_symm
    {ι E E' : Type u} [Finite ι]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup E'] [Module ℝ E']
    {P : RootPairing ι ℝ E E'} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {V W : SemisimpleVersion (k := k) P}
    (h : SemisimpleVersion.Isomorphic (P := P) V W) :
    SemisimpleVersion.Isomorphic (P := P) W V := by
  letI := V.group
  letI := W.group
  change Nonempty (AlgebraicGroup.Iso V.carrier W.carrier) at h
  change Nonempty (AlgebraicGroup.Iso W.carrier V.carrier)
  rcases h with ⟨e⟩
  exact ⟨e.symm⟩

omit [IsAlgClosed k] in
public theorem SemisimpleVersion.isomorphic_trans
    {ι E E' : Type u} [Finite ι]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup E'] [Module ℝ E']
    {P : RootPairing ι ℝ E E'} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {U V W : SemisimpleVersion (k := k) P}
    (hUV : SemisimpleVersion.Isomorphic (P := P) U V)
    (hVW : SemisimpleVersion.Isomorphic (P := P) V W) :
    SemisimpleVersion.Isomorphic (P := P) U W := by
  letI := U.group
  letI := V.group
  letI := W.group
  change Nonempty (AlgebraicGroup.Iso U.carrier V.carrier) at hUV
  change Nonempty (AlgebraicGroup.Iso V.carrier W.carrier) at hVW
  change Nonempty (AlgebraicGroup.Iso U.carrier W.carrier)
  rcases hUV with ⟨eUV⟩
  rcases hVW with ⟨eVW⟩
  exact ⟨eVW.comp eUV⟩

omit [IsAlgClosed k] in
public theorem SemisimpleVersion.isomorphic_of_common_target
    {ι E E' : Type u} [Finite ι]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup E'] [Module ℝ E']
    {P : RootPairing ι ℝ E E'} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {U V W : SemisimpleVersion (k := k) P}
    (hVU : SemisimpleVersion.Isomorphic (P := P) V U)
    (hWU : SemisimpleVersion.Isomorphic (P := P) W U) :
    SemisimpleVersion.Isomorphic (P := P) V W := by
  exact SemisimpleVersion.isomorphic_trans hVU
    (SemisimpleVersion.isomorphic_symm hWU)

public structure IsUniversalRootVersion
    {ι E E' : Type u} [Finite ι]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup E'] [Module ℝ E']
    {P : RootPairing ι ℝ E E'} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (V : SemisimpleVersion (k := k) P) : Prop where
  mapsTo : ∀ W : SemisimpleVersion (k := k) P,
    letI := V.group
    letI := W.group
    ∃ φ : AlgebraicGroup.Morphism V.carrier W.carrier, IsIsogeny φ

public structure IsAdjointRootVersion
    {ι E E' : Type u} [Finite ι]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup E'] [Module ℝ E']
    {P : RootPairing ι ℝ E E'} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (V : SemisimpleVersion (k := k) P) : Prop where
  mapsFrom : ∀ W : SemisimpleVersion (k := k) P,
    letI := W.group
    letI := V.group
    ∃ φ : AlgebraicGroup.Morphism W.carrier V.carrier, IsIsogeny φ

/-- Data exported by a concrete Chevalley construction once the two extreme
versions and their comparison maps have been constructed.  The fields are
deliberately geometric, and the constructor below only rearranges these
supplied maps.
-/
public structure ChevalleyVersionPackage
    {ι E E' : Type u} [Finite ι]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup E'] [Module ℝ E']
    (P : RootPairing ι ℝ E E') [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] where
  universal : SemisimpleVersion (k := k) P
  adjoint : SemisimpleVersion (k := k) P
  universal_maps : IsUniversalRootVersion universal
  adjoint_maps : IsAdjointRootVersion adjoint
  universal_pairwise : ∀ V W : SemisimpleVersion (k := k) P,
    IsUniversalRootVersion V → IsUniversalRootVersion W →
      SemisimpleVersion.Isomorphic (P := P) V W
  adjoint_pairwise : ∀ V W : SemisimpleVersion (k := k) P,
    IsAdjointRootVersion V → IsAdjointRootVersion W →
      SemisimpleVersion.Isomorphic (P := P) V W

namespace ChevalleyVersionPackage

variable {ι E E' : Type u} [Finite ι]
variable [AddCommGroup E] [Module ℝ E] [AddCommGroup E'] [Module ℝ E']
variable {P : RootPairing ι ℝ E E'} [P.IsRootSystem]
variable [P.IsCrystallographic] [P.IsReduced]

public def of_canonical_comparisons
    (universal adjoint : SemisimpleVersion (k := k) P)
    (universal_maps : IsUniversalRootVersion universal)
    (adjoint_maps : IsAdjointRootVersion adjoint)
    (universal_compare : ∀ V : SemisimpleVersion (k := k) P,
      IsUniversalRootVersion V →
        SemisimpleVersion.Isomorphic (P := P) V universal)
    (adjoint_compare : ∀ V : SemisimpleVersion (k := k) P,
      IsAdjointRootVersion V →
        SemisimpleVersion.Isomorphic (P := P) V adjoint) :
    ChevalleyVersionPackage (k := k) P := by
  refine
    { universal := universal
      adjoint := adjoint
      universal_maps := universal_maps
      adjoint_maps := adjoint_maps
      universal_pairwise := ?_
      adjoint_pairwise := ?_ }
  · intro V W hV hW
    exact SemisimpleVersion.isomorphic_of_common_target
      (universal_compare V hV) (universal_compare W hW)
  · intro V W hV hW
    exact SemisimpleVersion.isomorphic_of_common_target
      (adjoint_compare V hV) (adjoint_compare W hW)

omit [IsAlgClosed k] in
public theorem universal_exists
    (C : ChevalleyVersionPackage (k := k) P) :
    ∃ V : SemisimpleVersion (k := k) P, IsUniversalRootVersion V :=
  ⟨C.universal, C.universal_maps⟩

omit [IsAlgClosed k] in
public theorem adjoint_exists
    (C : ChevalleyVersionPackage (k := k) P) :
    ∃ V : SemisimpleVersion (k := k) P, IsAdjointRootVersion V :=
  ⟨C.adjoint, C.adjoint_maps⟩

omit [IsAlgClosed k] in
public theorem classification
    (C : ChevalleyVersionPackage (k := k) P) :
    (∃ V : SemisimpleVersion (k := k) P, IsUniversalRootVersion V) ∧
    (∃ V : SemisimpleVersion (k := k) P, IsAdjointRootVersion V) ∧
    (∀ V W : SemisimpleVersion (k := k) P,
      IsUniversalRootVersion V → IsUniversalRootVersion W →
        SemisimpleVersion.Isomorphic (P := P) V W) ∧
    (∀ V W : SemisimpleVersion (k := k) P,
      IsAdjointRootVersion V → IsAdjointRootVersion W →
        SemisimpleVersion.Isomorphic (P := P) V W) := by
  exact ⟨universal_exists C, adjoint_exists C,
    C.universal_pairwise, C.adjoint_pairwise⟩

end ChevalleyVersionPackage

end Theory.AlgebraicGroup
