module

public import Theory.AlgebraicGroup.Bor1.MorphicActionOrbitRange
public import Theory.AlgebraicGroup.Variety.GeometricComponents
public import Theory.AlgebraicGroup.Variety.OpenSubvariety
public import Theory.AlgebraicGroup.Variety.GeometricDimension
public import Theory.AlgebraicGroup.Variety.GeometricClosedImage
public import Theory.AlgebraicGroup.Variety.AffineGroupScheme

/-!
# Orbit geometry for morphic algebraic-group actions

This module develops the locally closed, smooth geometric carrier of an orbit and
proves that every morphic action on a nonempty geometric variety has a smooth closed orbit.
The final argument orders the closed supports of scheme-theoretic orbit-range closures by
inclusion. Noetherianity gives a minimal support; if its orbit were not closed, a rational
point in the closed boundary would have an orbit closure strictly contained in that support.

The construction uses the canonical reduced scheme-theoretic range closure and translation
equivariance from `MorphicActionOrbitRange`. It follows the minimal-closed-orbit argument in
Bor1, Proposition 1.8, without quotient descent.
-/

set_option linter.style.haveILetI false

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open Topology

namespace Theory.AlgebraicGroup.Variety.Geometric

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

private theorem dense_constructible_contains_open_of_noetherian
    {α : Type u} [TopologicalSpace α] [NoetherianSpace α] [Nonempty α]
    {S : Set α} (hS : IsConstructible S) (hSdense : Dense S) :
    ∃ U : Set α, IsOpen U ∧ U.Nonempty ∧ U ⊆ S := by
  classical
  let I : Type u := {C : Set α // C ∈ irreducibleComponents α}
  have hIfinite : Set.Finite (irreducibleComponents α) :=
    NoetherianSpace.finite_irreducibleComponents
  have hlocal (C : I) : ∃ U : Set α, IsOpen U ∧ U.Nonempty ∧ U ⊆ S := by
    let O : Set α := (⋃₀ (irreducibleComponents α \ {C.1}))ᶜ
    have hOopen : IsOpen O := by
      dsimp [O]
      rw [isOpen_compl_iff, Set.sUnion_eq_biUnion]
      exact hIfinite.sdiff.isClosed_biUnion fun W hW ↦
        isClosed_of_mem_irreducibleComponents W hW.1
    have hOeq : closure O = C.1 :=
      closure_sUnion_irreducibleComponents_sdiff_singleton hIfinite C.1 C.2
    have hOsub : O ⊆ C.1 := by
      intro x hx
      rw [← hOeq]
      exact subset_closure hx
    have hOne : O.Nonempty := by
      by_contra hO
      have hOeqempty : O = ∅ := Set.not_nonempty_iff_eq_empty.mp hO
      have hCempty : C.1 = ∅ := by
        rw [← hOeq, hOeqempty, closure_empty]
      obtain ⟨x, hx⟩ := C.2.1.nonempty
      rw [hCempty] at hx
      exact hx
    have hOpre : IsPreirreducible O := by
      intro u v hu hv huO hvO
      obtain ⟨x, hxO, hxu⟩ := huO
      obtain ⟨y, hyO, hyv⟩ := hvO
      obtain ⟨z, hzC, hzu, hzvO⟩ :=
        C.2.1.isPreirreducible u (v ∩ O) hu (hv.inter hOopen)
          ⟨x, hOsub hxO, hxu⟩ ⟨y, hOsub hyO, hyv, hyO⟩
      exact ⟨z, hzvO.2, hzu, hzvO.1⟩
    let T : Set O := Subtype.val ⁻¹' S
    have hTconstructible : IsConstructible T :=
      hS.preimage_of_isOpenEmbedding hOopen.isOpenEmbedding_subtypeVal
    have hTdense : Dense T := by
      rw [Subtype.dense_iff]
      intro x hxO
      apply mem_closure_iff.mpr
      intro U hU hxU
      obtain ⟨z, hzUO, hzS⟩ :=
        hSdense.inter_open_nonempty (U ∩ O) (hU.inter hOopen)
          ⟨x, hxU, hxO⟩
      refine ⟨z, hzUO.1, ?_⟩
      exact ⟨⟨z, hzUO.2⟩, hzS, rfl⟩
    letI : Nonempty O := hOne.to_subtype
    letI : PreirreducibleSpace O := Subtype.preirreducibleSpace hOpre
    obtain ⟨q, hqopen, hqne, hqT⟩ :=
      IsConstructible.exists_isOpen_nonempty_subset_of_dense hTconstructible hTdense
    refine ⟨Subtype.val '' q, ?_, hqne.image Subtype.val, ?_⟩
    · exact hOopen.isOpenEmbedding_subtypeVal.isOpenMap q hqopen
    · rintro z ⟨y, hyq, rfl⟩
      exact hqT hyq
  let q : I → Set α := fun C => Classical.choose (hlocal C)
  have hqopen (C : I) : IsOpen (q C) := (Classical.choose_spec (hlocal C)).1
  have hqne (C : I) : (q C).Nonempty := (Classical.choose_spec (hlocal C)).2.1
  have hqS (C : I) : q C ⊆ S := (Classical.choose_spec (hlocal C)).2.2
  refine ⟨⋃ C : I, q C, isOpen_iUnion hqopen, ?_, ?_⟩
  · obtain ⟨x⟩ := (inferInstance : Nonempty α)
    let C : I := ⟨irreducibleComponent x,
      show irreducibleComponent x ∈ irreducibleComponents α from
        irreducibleComponent_mem_irreducibleComponents x⟩
    obtain ⟨y, hy⟩ := hqne C
    exact ⟨y, Set.mem_iUnion.mpr ⟨C, hy⟩⟩
  · intro x hx
    obtain ⟨C, hxC⟩ := Set.mem_iUnion.mp hx
    exact hqS C hxC

omit [IsAlgClosed k] in
private theorem constructible_nonempty_inter_closedPoints
    {V : Geometric k} {S : Set V.toScheme}
    (hS : IsConstructible S) (hSne : S.Nonempty) :
    (S ∩ closedPoints V.toScheme).Nonempty := by
  let Z : Set V.toScheme := closure S
  letI : NoetherianSpace Z := inferInstance
  letI : Nonempty Z := by
    obtain ⟨x, hx⟩ := hSne
    exact ⟨⟨x, subset_closure hx⟩⟩
  let T : Set Z := Subtype.val ⁻¹' S
  have hTconstructible : IsConstructible T := by
    apply hS.preimage_of_isClosedEmbedding
      isClosed_closure.isClosedEmbedding_subtypeVal
    exact NoetherianSpace.isCompact _
  have hTdense : Dense T := by
    rw [Subtype.dense_iff]
    intro x hx
    apply mem_closure_iff.mpr
    intro U hU hxU
    obtain ⟨y, hyU, hyS⟩ :=
      mem_closure_iff.mp (show x ∈ closure S from hx)
        U hU hxU
    exact ⟨y, hyU, ⟨⟨y, subset_closure hyS⟩, hyS, rfl⟩⟩
  obtain ⟨U, hUopen, hUne, hUT⟩ :=
    dense_constructible_contains_open_of_noetherian hTconstructible hTdense
  letI : JacobsonSpace V.toScheme :=
    LocallyOfFiniteType.jacobsonSpace V.structureMap
  letI : JacobsonSpace Z :=
    JacobsonSpace.of_isClosedEmbedding isClosed_closure.isClosedEmbedding_subtypeVal
  obtain ⟨z, hzU, hzclosed⟩ :=
    nonempty_inter_closedPoints hUne hUopen.isLocallyClosed
  refine ⟨z.1, hUT hzU, ?_⟩
  have hpre :
      (Subtype.val : Z → V.toScheme) ⁻¹' closedPoints V.toScheme =
        closedPoints Z :=
    isClosed_closure.isClosedEmbedding_subtypeVal.preimage_closedPoints
  change z ∈ (Subtype.val : Z → V.toScheme) ⁻¹' closedPoints V.toScheme
  rw [hpre]
  exact hzclosed

end Theory.AlgebraicGroup.Variety.Geometric

namespace Theory.AlgebraicGroup.Variety.Geometric.MorphicAction

open Theory.AlgebraicGroup.Variety.Geometric

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

private noncomputable abbrev sourceLeftTranslation
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    (g : Theory.AlgebraicGroup.Variety.Point G) :
    Morphism (ofAffine G) (ofAffine G) :=
  ofAffine_morphism (Theory.AlgebraicGroup.leftMulMorphism G g)

omit [IsAlgClosed k] in
private theorem rangeClosure_factor_range_iff
    {V W : Geometric k} (f : Morphism V W)
    (z : f.schemeTheoreticRangeClosure.toGeometric.toScheme) :
    z ∈ Set.range f.toSchemeTheoreticRangeClosure.hom ↔
      f.schemeTheoreticRangeClosure.inclusion.hom z ∈ Set.range f.hom := by
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨w, ?_⟩
    have hcomp := congrArg (fun q => q w)
      (f.toSchemeTheoreticRangeClosure_comp_inclusion)
    exact hcomp.symm
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    have hcomp := congrArg (fun q => q w)
      (f.toSchemeTheoreticRangeClosure_comp_inclusion)
    apply f.schemeTheoreticRangeClosure.inclusion.hom.isClosedEmbedding.injective
    exact hcomp.trans hw

private theorem orbitRangeClosureTranslation_image_range
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X)
    (x : Point X) (g : Theory.AlgebraicGroup.Variety.Point G) :
    (A.orbitMorphismRangeClosureTranslation x g).hom ''
        Set.range (A.orbitMorphismAt x).toSchemeTheoreticRangeClosure.hom =
      Set.range (A.orbitMorphismAt x).toSchemeTheoreticRangeClosure.hom := by
  let f := A.orbitMorphismAt x
  let C : ClosedSubvariety X := f.schemeTheoreticRangeClosure
  let fg := f.toSchemeTheoreticRangeClosure
  have hsubset (g : Theory.AlgebraicGroup.Variety.Point G) :
      (A.orbitMorphismRangeClosureTranslation x g).hom ''
          Set.range fg.hom ⊆ Set.range fg.hom := by
    rintro z ⟨w, ⟨v, rfl⟩, hz⟩
    apply (rangeClosure_factor_range_iff f z).2
    have hzambient :
        (A.translationMorphism g).hom
            (C.inclusion.hom (fg.hom v)) ∈ Set.range f.hom := by
      rw [← A.translationMorphism_image_orbitMorphismAt_range x g]
      exact ⟨C.inclusion.hom (fg.hom v),
        (rangeClosure_factor_range_iff f (fg.hom v)).1 ⟨v, rfl⟩, rfl⟩
    obtain ⟨u, hu⟩ := hzambient
    refine ⟨u, ?_⟩
    have hinc := congrArg Morphism.hom
      (A.orbitMorphismRangeClosureTranslation_inclusion x g)
    have hpoint0 := congrArg (fun q => q (fg.hom v)) hinc
    have hpoint :
        C.inclusion.hom
            ((A.orbitMorphismRangeClosureTranslation x g).hom
              (fg.hom v)) =
          (A.translationMorphism g).hom
            (C.inclusion.hom (fg.hom v)) := by
      change C.inclusion.hom
          ((A.orbitMorphismRangeClosureTranslation x g).hom
            (fg.hom v)) =
        (A.translationMorphism g).hom
          (C.inclusion.hom (fg.hom v)) at hpoint0
      exact hpoint0
    rw [hz] at hpoint
    exact (hpoint.trans hu.symm).symm
  apply Set.Subset.antisymm (hsubset g)
  rintro z ⟨v, rfl⟩
  have hz :
      (A.orbitMorphismRangeClosureTranslation x g⁻¹).hom
          (fg.hom v) ∈ Set.range fg.hom := by
    apply hsubset g⁻¹
    exact ⟨fg.hom v, ⟨v, rfl⟩, rfl⟩
  refine ⟨(A.orbitMorphismRangeClosureTranslation x g⁻¹).hom
      (fg.hom v), hz, ?_⟩
  have hinv := congrArg (fun q => q (fg.hom v))
    (A.orbitMorphismRangeClosureTranslationIso x g).inv_hom_id
  exact hinv

private theorem orbitRangeClosure_point_translate
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X)
    (x : Point X)
    (p0 p : Point (A.orbitMorphismRangeClosure x).toGeometric)
    (hp0 : p0 ∈
      Set.range (A.orbitMorphismAt x).toSchemeTheoreticRangeClosure)
    (hp : p ∈
      Set.range (A.orbitMorphismAt x).toSchemeTheoreticRangeClosure) :
    ∃ g : Theory.AlgebraicGroup.Variety.Point G,
      A.orbitMorphismRangeClosureTranslation x g p0 = p := by
  let f := A.orbitMorphismAt x
  let C := A.orbitMorphismRangeClosure x
  let fC := f.toSchemeTheoreticRangeClosure
  have hp0' : p0 ∈ Set.range fC := by
    exact hp0
  have hp' : p ∈ Set.range fC := by
    exact hp
  obtain ⟨a, ha⟩ := hp0'
  obtain ⟨b, hb⟩ := hp'
  let aG := affinePointEquiv G a
  let bG := affinePointEquiv G b
  let g := bG * aG⁻¹
  have haOrbit :
      A.orbitMorphismAt x a =
        A.toMulAction.smul aG x := by
    rw [show a = (affinePointEquiv G).symm aG by
      exact (affinePointEquiv G).symm_apply_apply a |>.symm]
    exact A.orbitMorphismAt_apply x aG
  have hbOrbit :
      A.orbitMorphismAt x b =
        A.toMulAction.smul bG x := by
    rw [show b = (affinePointEquiv G).symm bG by
      exact (affinePointEquiv G).symm_apply_apply b |>.symm]
    exact A.orbitMorphismAt_apply x bG
  have htrans :
      A.translationMorphism g
          (A.orbitMorphismAt x a) =
        A.orbitMorphismAt x b := by
    have htrans0 :
        A.translationMorphism g (A.orbitMorphismAt x a) =
          A.toMulAction.smul g (A.orbitMorphismAt x a) :=
      A.translationMorphism_apply g _
    have htrans1 :
        A.toMulAction.smul g (A.orbitMorphismAt x a) =
          A.toMulAction.smul g (A.toMulAction.smul aG x) :=
      congrArg (A.toMulAction.smul g) haOrbit
    have htrans2 :
        A.toMulAction.smul g (A.toMulAction.smul aG x) =
          A.toMulAction.smul bG x := by
      dsimp [g]
      calc
        A.toMulAction.smul (bG * aG⁻¹)
            (A.toMulAction.smul aG x) =
            A.toMulAction.smul bG
              (A.toMulAction.smul aG⁻¹
                (A.toMulAction.smul aG x)) :=
          A.toMulAction.mul_smul bG aG⁻¹
            (A.toMulAction.smul aG x)
        _ = A.toMulAction.smul bG
              (A.toMulAction.smul (aG⁻¹ * aG) x) := by
          congr 1
          exact (A.toMulAction.mul_smul aG⁻¹ aG x).symm
        _ = A.toMulAction.smul bG x := by
          rw [inv_mul_cancel]
          exact congrArg (A.toMulAction.smul bG)
            (A.toMulAction.one_smul x)
    exact htrans0.trans (htrans1.trans (htrans2.trans hbOrbit.symm))
  have htransClosed :
      C.inclusion
          (A.orbitMorphismRangeClosureTranslation x g (fC a)) =
        C.inclusion (fC b) := by
    have hinc :=
      (A.orbitMorphismRangeClosureTranslation_inclusion x g)
    have hpoint := congrArg (fun q : Morphism C.toGeometric X =>
      q (fC a)) hinc
    change C.inclusion
        (A.orbitMorphismRangeClosureTranslation x g (fC a)) =
      A.translationMorphism g (C.inclusion (fC a)) at hpoint
    have hfa : C.inclusion (fC a) = f a := by
      exact f.toSchemeTheoreticRangeClosure_inclusion_apply a
    have hfb : C.inclusion (fC b) = f b := by
      exact f.toSchemeTheoreticRangeClosure_inclusion_apply b
    rw [hfa, htrans, ← hfb] at hpoint
    exact hpoint
  have hclosedEq :
      (A.orbitMorphismRangeClosureTranslation x g (fC a)).1
          (IsLocalRing.closedPoint k) =
        (p.1 (IsLocalRing.closedPoint k)) := by
    apply C.inclusion.hom.isClosedEmbedding.injective
    have hpoint := congrArg (fun q : Point X =>
      q.1 (IsLocalRing.closedPoint k)) htransClosed
    rw [show p = fC b by exact hb.symm]
    exact hpoint
  refine ⟨g, ?_⟩
  rw [← ha]
  apply (pointEquivClosedPoint C.toGeometric.structureMap).injective
  apply Subtype.ext
  exact hclosedEq

/-- The scheme-point orbit is open in its reduced scheme-theoretic closure. -/
public theorem orbitRangeClosure_range_isOpen
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X)
    (x : Point X) :
    IsOpen
      (Set.range
        (A.orbitMorphismAt x).toSchemeTheoreticRangeClosure.hom) := by
  let f := A.orbitMorphismAt x
  let C : ClosedSubvariety X := f.schemeTheoreticRangeClosure
  let fC := f.toSchemeTheoreticRangeClosure
  have hconstructible :
      IsConstructible (Set.range fC.hom) :=
    fC.range_isConstructible
  have hdense : Dense (Set.range fC.hom) :=
    f.denseRange_toSchemeTheoreticRangeClosure
  letI : Nonempty C.toGeometric.toScheme := by
    exact ⟨fC.hom
      (((affinePointEquiv G).symm 1).1 (IsLocalRing.closedPoint k))⟩
  letI : Nonempty f.schemeTheoreticRangeClosure.toGeometric.toScheme := by
    exact ⟨fC.hom
      (((affinePointEquiv G).symm 1).1 (IsLocalRing.closedPoint k))⟩
  obtain ⟨U, hUopen, hUne, hUsub⟩ :=
    dense_constructible_contains_open_of_noetherian hconstructible hdense
  let O : Set C.toGeometric.toScheme :=
    ⋃ g : Theory.AlgebraicGroup.Variety.Point G,
      (A.orbitMorphismRangeClosureTranslation x g).hom '' U
  have hOopen : IsOpen O := by
    exact isOpen_iUnion fun g =>
      (Scheme.homeoOfIso
        (A.orbitMorphismRangeClosureTranslationIso x g)).isOpenMap U hUopen
  have hOsub : O ⊆ Set.range fC.hom := by
    intro z hz
    obtain ⟨g, zg, hzU⟩ := Set.mem_iUnion.mp hz
    apply (orbitRangeClosureTranslation_image_range A x g).subset
    exact ⟨zg, hUsub hzU.1, hzU.2⟩
  have hclosedPoint :
      ∀ z : C.toGeometric.toScheme,
        z ∈ Set.range fC.hom →
          z ∈ closedPoints C.toGeometric.toScheme →
            z ∈ O := by
    intro z hzrange hzclosed
    have hzpair :
        z ∈ Set.range fC.hom ∩
          closedPoints f.schemeTheoreticRangeClosure.toGeometric.toScheme :=
      ⟨hzrange, hzclosed⟩
    rw [← fC.image_pointRange_eq_range_inter_closedPoints] at hzpair
    obtain ⟨p, hpRange, hpz⟩ := hzpair
    obtain ⟨p0, hp0U⟩ :=
      exists_point_closedPoint_mem_of_isOpen C.toGeometric hUopen hUne
    have hp0Range : p0 ∈ Set.range fC := by
      apply (fC.point_mem_range_iff_closedPoint_mem_range p0).2
      exact hUsub hp0U
    obtain ⟨a, ha⟩ := hp0Range
    obtain ⟨b, hb⟩ := hpRange
    let aG := affinePointEquiv G a
    let bG := affinePointEquiv G b
    let g := bG * aG⁻¹
    have haOrbit :
        A.orbitMorphismAt x a =
          A.toMulAction.smul aG x := by
      rw [show a = (affinePointEquiv G).symm aG by
        exact (affinePointEquiv G).symm_apply_apply a |>.symm]
      exact A.orbitMorphismAt_apply x aG
    have hbOrbit :
        A.orbitMorphismAt x b =
          A.toMulAction.smul bG x := by
      rw [show b = (affinePointEquiv G).symm bG by
        exact (affinePointEquiv G).symm_apply_apply b |>.symm]
      exact A.orbitMorphismAt_apply x bG
    have htrans :
        A.translationMorphism g
            (A.orbitMorphismAt x a) =
          A.orbitMorphismAt x b := by
      have htrans0 :
          A.translationMorphism g (A.orbitMorphismAt x a) =
            A.toMulAction.smul g (A.orbitMorphismAt x a) :=
        A.translationMorphism_apply g _
      have htrans1 :
          A.toMulAction.smul g (A.orbitMorphismAt x a) =
            A.toMulAction.smul g (A.toMulAction.smul aG x) :=
        congrArg (A.toMulAction.smul g) haOrbit
      have htrans2 :
          A.toMulAction.smul g (A.toMulAction.smul aG x) =
            A.toMulAction.smul bG x := by
        dsimp [g]
        calc
          A.toMulAction.smul (bG * aG⁻¹)
              (A.toMulAction.smul aG x) =
              A.toMulAction.smul bG
                (A.toMulAction.smul aG⁻¹
                  (A.toMulAction.smul aG x)) :=
            A.toMulAction.mul_smul bG aG⁻¹
              (A.toMulAction.smul aG x)
          _ = A.toMulAction.smul bG
                (A.toMulAction.smul (aG⁻¹ * aG) x) := by
            congr 1
            exact (A.toMulAction.mul_smul aG⁻¹ aG x).symm
          _ = A.toMulAction.smul bG x := by
            rw [inv_mul_cancel]
            exact congrArg (A.toMulAction.smul bG)
              (A.toMulAction.one_smul x)
      exact htrans0.trans (htrans1.trans (htrans2.trans hbOrbit.symm))
    have htransClosed :
        C.inclusion (A.orbitMorphismRangeClosureTranslation x g
            (fC a)) =
          C.inclusion (fC b) := by
      have hinc :=
        (A.orbitMorphismRangeClosureTranslation_inclusion x g)
      have hpoint := congrArg (fun q : Morphism C.toGeometric X =>
        q (fC a)) hinc
      change C.inclusion
          (A.orbitMorphismRangeClosureTranslation x g (fC a)) =
        A.translationMorphism g (C.inclusion (fC a)) at hpoint
      have hfa : C.inclusion (fC a) = f a := by
        exact f.toSchemeTheoreticRangeClosure_inclusion_apply a
      have hfb : C.inclusion (fC b) = f b := by
        exact f.toSchemeTheoreticRangeClosure_inclusion_apply b
      rw [hfa, htrans, ← hfb] at hpoint
      exact hpoint
    have hclosedEq :
        (A.orbitMorphismRangeClosureTranslation x g
          (fC a)).1 (IsLocalRing.closedPoint k) =
          (p.1 (IsLocalRing.closedPoint k)) := by
      apply C.inclusion.hom.isClosedEmbedding.injective
      have hpoint := congrArg (fun q : Point X =>
        q.1 (IsLocalRing.closedPoint k)) htransClosed
      rw [show p = fC b by exact hb.symm]
      exact hpoint
    have heq :
        A.orbitMorphismRangeClosureTranslation x g (fC a) = p := by
      apply (pointEquivClosedPoint C.toGeometric.structureMap).injective
      apply Subtype.ext
      exact hclosedEq
    have hmem :
        (A.orbitMorphismRangeClosureTranslation x g (fC a)).1
            (IsLocalRing.closedPoint k) ∈ O := by
      apply Set.mem_iUnion.mpr
      refine ⟨g, ?_⟩
      have haU : (fC a).1 (IsLocalRing.closedPoint k) ∈ U := by
        rw [ha]
        exact hp0U
      exact ⟨(fC a).1 (IsLocalRing.closedPoint k), haU, rfl⟩
    rw [heq] at hmem
    exact hpz ▸ hmem
  have hrange_sub : Set.range fC.hom ⊆ O := by
    intro z hz
    by_contra hnot
    have hdiff :
        (Set.range fC.hom \ O).Nonempty := ⟨z, hz, hnot⟩
    have hdiffconstructible :
        IsConstructible (Set.range fC.hom \ O) :=
      hconstructible.sdiff
        ((NoetherianSpace.isCompact O).isConstructible hOopen)
    obtain ⟨q, hqrange, hqclosed⟩ :=
      constructible_nonempty_inter_closedPoints
        hdiffconstructible hdiff
    exact hqrange.2 (hclosedPoint q hqrange.1 hqclosed)
  rw [Set.Subset.antisymm hrange_sub hOsub]
  exact hOopen

private theorem orbitRangeClosure_range_subset_smoothLocus
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X)
    (x : Point X) :
    Set.range
        (A.orbitMorphismAt x).toSchemeTheoreticRangeClosure.hom ⊆
      ((A.orbitMorphismRangeClosure x).toGeometric.structureMap.smoothLocus : Set
        (A.orbitMorphismRangeClosure x).toGeometric.toScheme) := by
  let f := A.orbitMorphismAt x
  let C : ClosedSubvariety X := f.schemeTheoreticRangeClosure
  let fC := f.toSchemeTheoreticRangeClosure
  have hconstructible :
      IsConstructible (Set.range fC.hom) :=
    fC.range_isConstructible
  have hdense : Dense (Set.range fC.hom) :=
    f.denseRange_toSchemeTheoreticRangeClosure
  letI : Nonempty C.toGeometric.toScheme := by
    exact ⟨fC.hom
      (((affinePointEquiv G).symm 1).1 (IsLocalRing.closedPoint k))⟩
  letI : Nonempty f.schemeTheoreticRangeClosure.toGeometric.toScheme := by
    exact ⟨fC.hom
      (((affinePointEquiv G).symm 1).1 (IsLocalRing.closedPoint k))⟩
  obtain ⟨U, hUopen, hUne, hUsub⟩ :=
    dense_constructible_contains_open_of_noetherian hconstructible hdense
  let S : Set C.toGeometric.toScheme :=
    C.toGeometric.structureMap.smoothLocus
  have hSopen : IsOpen S := C.toGeometric.structureMap.smoothLocus.2
  have hSdense : Dense S :=
    C.toGeometric.structureMap.dense_smoothLocus_of_perfectField
  have hUSne : (U ∩ S).Nonempty :=
    hSdense.inter_open_nonempty U hUopen hUne
  obtain ⟨p0, hp0US⟩ :=
    exists_point_closedPoint_mem_of_isOpen C.toGeometric
      (hUopen.inter hSopen) hUSne
  have hp0U : p0.1 (IsLocalRing.closedPoint k) ∈ U :=
    hp0US.1
  have hp0S : p0.1 (IsLocalRing.closedPoint k) ∈ S :=
    hp0US.2
  have hp0Range : p0 ∈ Set.range fC := by
    apply (fC.point_mem_range_iff_closedPoint_mem_range p0).2
    exact hUsub hp0U
  have hclosedPoint :
      ∀ z : C.toGeometric.toScheme,
        z ∈ Set.range fC.hom →
          z ∈ closedPoints C.toGeometric.toScheme →
            z ∈ S := by
    intro z hzrange hzclosed
    have hzpair :
        z ∈ Set.range fC.hom ∩
          closedPoints f.schemeTheoreticRangeClosure.toGeometric.toScheme :=
      ⟨hzrange, hzclosed⟩
    rw [← fC.image_pointRange_eq_range_inter_closedPoints] at hzpair
    obtain ⟨p, hpRange, hpz⟩ := hzpair
    obtain ⟨g, hgp⟩ :=
      orbitRangeClosure_point_translate A x p0 p hp0Range hpRange
    have himage :
        (A.orbitMorphismRangeClosureTranslation x g).hom '' S = S :=
      A.orbitMorphismRangeClosureTranslation_image_smoothLocus x g
    have htranslated :
        (A.orbitMorphismRangeClosureTranslation x g p0).1
            (IsLocalRing.closedPoint k) ∈ S := by
      rw [← himage]
      exact ⟨p0.1 (IsLocalRing.closedPoint k), hp0S, rfl⟩
    have hpS : p.1 (IsLocalRing.closedPoint k) ∈ S := by
      rw [← hgp]
      exact htranslated
    exact hpz ▸ hpS
  intro z hz
  by_contra hnot
  have hdiff : (Set.range fC.hom \ S).Nonempty := ⟨z, hz, hnot⟩
  have hdiffconstructible :
      IsConstructible (Set.range fC.hom \ S) :=
    hconstructible.sdiff ((NoetherianSpace.isCompact S).isConstructible hSopen)
  obtain ⟨q, hqrange, hqclosed⟩ :=
    constructible_nonempty_inter_closedPoints hdiffconstructible hdiff
  exact hqrange.2 (hclosedPoint q hqrange.1 hqclosed)

/-- The scheme-point range of an orbit morphism is locally closed. -/
public theorem orbitMorphismAt_range_isLocallyClosed
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X)
    (x : Point X) :
    IsLocallyClosed (Set.range (A.orbitMorphismAt x).hom) := by
  let f := A.orbitMorphismAt x
  let C : ClosedSubvariety X := f.schemeTheoreticRangeClosure
  let fC := f.toSchemeTheoreticRangeClosure
  have himage :
      C.inclusion.hom '' Set.range fC.hom =
        Set.range f.hom := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (rangeClosure_factor_range_iff f w).1 hw
    · rintro ⟨w, rfl⟩
      refine ⟨fC.hom w, ⟨w, rfl⟩, ?_⟩
      have hcomp := congrArg (fun q => q w)
        (f.toSchemeTheoreticRangeClosure_comp_inclusion)
      exact hcomp.symm
  rw [← himage]
  exact
    (orbitRangeClosure_range_isOpen A x).isLocallyClosed.image
      C.inclusion.hom.isClosedEmbedding.isInducing
      C.inclusion.hom.isClosedEmbedding.isClosed_range.isLocallyClosed

/-- The rational-point orbit support is the closed-point part of the scheme orbit range. -/
public theorem orbitSupport_eq_range_inter_closedPoints
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X)
    (x : Point X) :
    A.orbitSupport x =
      Set.range (A.orbitMorphismAt x).hom ∩ closedPoints X.toScheme := by
  letI : MulAction (Theory.AlgebraicGroup.Variety.Point G) (Point X) :=
    A.toMulAction
  let f := A.orbitMorphismAt x
  have hsupport := A.orbitSupport_eq_rationalPointSupport_range x
  rw [hsupport]
  rw [Theory.AlgebraicGroup.Variety.Geometric.MorphicAction.rationalPointSupport_eq_closedPoint_image]
  rw [← f.image_pointRange_eq_range_inter_closedPoints]
  ext z
  constructor
  · rintro ⟨y, ⟨g, rfl⟩, rfl⟩
    refine ⟨f ((affinePointEquiv G).symm g), ⟨_, rfl⟩, ?_⟩
    exact congrArg (fun q : Point X =>
      q.1 (IsLocalRing.closedPoint k)) (A.orbitMorphismAt_apply x g)
  · rintro ⟨y, ⟨w, hw⟩, rfl⟩
    let g := affinePointEquiv G w
    have hw' :
        f w = A.toMulAction.smul g x := by
      rw [show w = (affinePointEquiv G).symm g by
        exact (affinePointEquiv G).symm_apply_apply w |>.symm]
      exact A.orbitMorphismAt_apply x g
    refine ⟨A.toMulAction.smul g x, ⟨g, ?_⟩, ?_⟩
    · exact rfl
    · exact congrArg (fun q : Point X =>
        q.1 (IsLocalRing.closedPoint k)) (hw'.symm.trans hw)

/-- The topological closure of the rational-point orbit support is the support of the reduced
scheme-theoretic range closure. -/
public theorem orbitSupport_closure_eq_orbitMorphismRangeClosure_range
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X)
    (x : Point X) :
    closure (A.orbitSupport x) =
      Set.range (A.orbitMorphismRangeClosure x).inclusion.hom := by
  letI : JacobsonSpace X.toScheme :=
    LocallyOfFiniteType.jacobsonSpace X.structureMap
  rw [orbitSupport_eq_range_inter_closedPoints,
    JacobsonSpace.closure_inter_closedPoints_eq_closure
      (orbitMorphismAt_range_isLocallyClosed A x),
    ← A.orbitMorphismRangeClosure_range x]

private noncomputable def orbitOpenCarrier
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X) (x : Point X) :
    OpenSubvariety (A.orbitMorphismRangeClosure x).toGeometric :=
  openSubvariety _ ⟨
    Set.range (A.orbitMorphismAt x).toSchemeTheoreticRangeClosure.hom,
    orbitRangeClosure_range_isOpen A x⟩

private theorem orbitOpenCarrier_range
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X) (x : Point X) :
    Set.range (orbitOpenCarrier A x).inclusion.hom =
      Set.range (A.orbitMorphismAt x).toSchemeTheoreticRangeClosure.hom := by
  exact openSubvariety_range _ _

/-- The orbit through `x`, equipped with its reduced locally closed geometric structure. -/
public noncomputable def orbitSubvariety
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X) (x : Point X) :
    LocallyClosedSubvariety X :=
  { toGeometric := (orbitOpenCarrier A x).toGeometric
    inclusion := Morphism.comp (orbitOpenCarrier A x).inclusion
      (A.orbitMorphismRangeClosure x).inclusion
    isImmersion := by
      change IsImmersion
        ((orbitOpenCarrier A x).inclusion.hom ≫
          (A.orbitMorphismRangeClosure x).inclusion.hom)
      infer_instance }

/-- The locally closed orbit carrier has exactly the scheme-point range of the orbit morphism. -/
public theorem orbitSubvariety_range
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X) (x : Point X) :
    Set.range (orbitSubvariety A x).inclusion.hom =
      Set.range (A.orbitMorphismAt x).hom := by
  let f := A.orbitMorphismAt x
  let C := A.orbitMorphismRangeClosure x
  let fC := f.toSchemeTheoreticRangeClosure
  let U := orbitOpenCarrier A x
  change Set.range (U.inclusion.hom ≫ C.inclusion.hom) = Set.range f.hom
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    orbitOpenCarrier_range]
  ext z
  constructor
  · rintro ⟨w, ⟨v, rfl⟩, rfl⟩
    exact (rangeClosure_factor_range_iff f (fC.hom v)).1 ⟨v, rfl⟩
  · rintro ⟨w, rfl⟩
    refine ⟨fC.hom w, ?_, ?_⟩
    · exact ⟨w, rfl⟩
    · have hcomp := congrArg (fun q => q w)
        (f.toSchemeTheoreticRangeClosure_comp_inclusion)
      exact hcomp.symm

omit [IsAlgClosed k] in
private theorem openSubvariety_smooth_of_range_subset
    {C : Geometric k} (U : OpenSubvariety C)
    (hU :
      Set.range U.inclusion.hom ⊆
        (C.structureMap.smoothLocus : Set C.toScheme)) :
    Smooth U.toGeometric.structureMap := by
  have hpre :
      Eq (U.inclusion.hom ⁻¹ᵁ C.structureMap.smoothLocus)
        (⊤ : U.toGeometric.toScheme.Opens) := by
    apply TopologicalSpace.Opens.ext
    exact Set.eq_univ_of_forall (fun z => by
      exact hU ⟨z, rfl⟩)
  rw [← U.inclusion.commutes]
  rw [← Scheme.Hom.smoothLocus_eq_top_iff]
  simpa [Scheme.Hom.preimage_smoothLocus_eq] using hpre

/-- Every orbit of a morphic action is smooth over the ground field. -/
public theorem orbitSubvariety_smooth
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X) (x : Point X) :
    Smooth (orbitSubvariety A x).toGeometric.structureMap := by
  let f := A.orbitMorphismAt x
  let U := orbitOpenCarrier A x
  apply openSubvariety_smooth_of_range_subset U
  rw [orbitOpenCarrier_range]
  exact orbitRangeClosure_range_subset_smoothLocus A x

/-- The boundary of the orbit inside its reduced scheme-theoretic closure. -/
public noncomputable def orbitBoundaryInClosure
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X) (x : Point X) :
    Set (A.orbitMorphismRangeClosure x).toGeometric.toScheme :=
  (Set.range (A.orbitMorphismAt x).toSchemeTheoreticRangeClosure.hom)ᶜ

/-- The orbit boundary is closed inside the reduced scheme-theoretic closure. -/
public theorem orbitBoundaryInClosure_isClosed
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X) (x : Point X) :
    IsClosed (orbitBoundaryInClosure A x) :=
  (orbitRangeClosure_range_isOpen A x).isClosed_compl

/-- On every irreducible component of an orbit closure, the boundary has strictly smaller
dimension than that component.  This is the componentwise form required when the acting
algebraic group is disconnected. -/
public theorem orbitBoundary_component_dimension_lt
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X) (x : Point X)
    (Z : IrreducibleComponent (A.orbitMorphismRangeClosure x).toGeometric) :
    topologicalKrullDim
        ((irreducibleComponentSubvariety
          (A.orbitMorphismRangeClosure x).toGeometric Z).inclusion.hom ⁻¹'
            orbitBoundaryInClosure A x) <
      dimension (irreducibleComponentSubvariety
        (A.orbitMorphismRangeClosure x).toGeometric Z).toGeometric := by
  let f := A.orbitMorphismAt x
  let C := A.orbitMorphismRangeClosure x
  let fC := f.toSchemeTheoreticRangeClosure
  let CZ := irreducibleComponentSubvariety C.toGeometric Z
  let B : Set CZ.toGeometric.toScheme :=
    CZ.inclusion.hom ⁻¹' orbitBoundaryInClosure A x
  change topologicalKrullDim B < dimension CZ.toGeometric
  apply closed_subset_dimension_lt CZ.toGeometric
  · exact (orbitBoundaryInClosure_isClosed A x).preimage
      CZ.inclusion.hom.continuous
  · intro hB
    obtain ⟨U, hUopen, hUne, hUZ⟩ :=
      NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z.1 Z.2
    have hdense : Dense (Set.range fC.hom) :=
      f.denseRange_toSchemeTheoreticRangeClosure
    obtain ⟨z, hzU, hzfC⟩ :=
      hdense.inter_open_nonempty U hUopen hUne
    have hzZ : z ∈ Set.range CZ.inclusion.hom := by
      rw [irreducibleComponentSubvariety_range]
      exact hUZ hzU
    obtain ⟨c, rfl⟩ := hzZ
    have hcB : c ∈ B := by rw [hB]; trivial
    change CZ.inclusion.hom c ∉ Set.range fC.hom at hcB
    exact hcB hzfC

/-- The boundary of an orbit in its scheme-theoretic closure, viewed in the ambient variety. -/
public noncomputable def orbitBoundary
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X) (x : Point X) :
    Set X.toScheme :=
  Set.range (A.orbitMorphismRangeClosure x).inclusion.hom \
    Set.range (A.orbitMorphismAt x).hom

/-- The boundary of an orbit is closed in the ambient variety. -/
public theorem orbitBoundary_isClosed
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X) (x : Point X) :
    IsClosed (orbitBoundary A x) := by
  let f := A.orbitMorphismAt x
  let C := f.schemeTheoreticRangeClosure
  let fC := f.toSchemeTheoreticRangeClosure
  change IsClosed (Set.range C.inclusion.hom \ Set.range f.hom)
  have hD : IsClosed (Set.range fC.hom)ᶜ :=
    (orbitRangeClosure_range_isOpen A x).isClosed_compl
  have himage :
      IsClosed (C.inclusion.hom '' (Set.range fC.hom)ᶜ) :=
    C.inclusion.hom.isClosedEmbedding.isClosedMap _ hD
  have heq :
      C.inclusion.hom '' (Set.range fC.hom)ᶜ =
        Set.range C.inclusion.hom \ Set.range f.hom := by
    ext z
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨⟨c, rfl⟩, ?_⟩
      intro hz
      exact hc ((rangeClosure_factor_range_iff f c).2 hz)
    · intro hz
      have hzC : z ∈ Set.range C.inclusion.hom := hz.1
      have hzR : z ∉ Set.range f.hom := hz.2
      rcases hzC with ⟨c, hc⟩
      subst z
      refine ⟨c, ?_, rfl⟩
      intro hc
      exact hzR ((rangeClosure_factor_range_iff f c).1 hc)
  rw [← heq]
  exact himage

/-- The closed topological support of the reduced scheme-theoretic orbit closure. -/
public noncomputable def orbitRangeClosureSupport
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X) (x : Point X) :
    Closeds X.toScheme :=
  ⟨Set.range (A.orbitMorphismRangeClosure x).inclusion.hom,
    (A.orbitMorphismRangeClosure x).inclusion.hom.isClosedEmbedding.isClosed_range⟩

private theorem orbitRangeClosureSupport_le_of_closedPoint_mem
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X) (x y : Point X)
    (hy : y.1 (IsLocalRing.closedPoint k) ∈ orbitRangeClosureSupport A x) :
    orbitRangeClosureSupport A y ≤ orbitRangeClosureSupport A x := by
  letI : MulAction (Theory.AlgebraicGroup.Variety.Point G) (Point X) :=
    A.toMulAction
  change Set.range (A.orbitMorphismRangeClosure y).inclusion.hom ⊆
    Set.range (A.orbitMorphismRangeClosure x).inclusion.hom
  rw [← orbitSupport_closure_eq_orbitMorphismRangeClosure_range A y]
  apply closure_minimal
  · rw [A.orbitSupport_eq_rationalPointSupport_range,
      rationalPointSupport_eq_closedPoint_image]
    rintro z ⟨q, ⟨g, rfl⟩, rfl⟩
    change (A.toMulAction.smul g y).1 (IsLocalRing.closedPoint k) ∈
      Set.range (A.orbitMorphismRangeClosure x).inclusion.hom
    have hz : (A.translationMorphism g).hom
        (y.1 (IsLocalRing.closedPoint k)) ∈
          (A.translationMorphism g).hom ''
            Set.range (A.orbitMorphismRangeClosure x).inclusion.hom :=
      ⟨y.1 (IsLocalRing.closedPoint k), hy, rfl⟩
    rw [A.translationMorphism_image_orbitMorphismRangeClosure] at hz
    exact A.translationMorphism_hom_closedPoint g y ▸ hz
  · exact (orbitRangeClosureSupport A x).isClosed

private theorem orbitRangeClosureSupport_lt_of_closedPoint_mem_boundary
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X) (x y : Point X)
    (hy : y.1 (IsLocalRing.closedPoint k) ∈ orbitBoundary A x) :
    orbitRangeClosureSupport A y < orbitRangeClosureSupport A x := by
  letI : MulAction (Theory.AlgebraicGroup.Variety.Point G) (Point X) :=
    A.toMulAction
  let B : Closeds X.toScheme :=
    ⟨orbitBoundary A x, orbitBoundary_isClosed A x⟩
  have hySupport :
      y.1 (IsLocalRing.closedPoint k) ∈ orbitRangeClosureSupport A x :=
    hy.1
  have hleB : orbitRangeClosureSupport A y ≤ B := by
    change Set.range (A.orbitMorphismRangeClosure y).inclusion.hom ⊆
      orbitBoundary A x
    rw [← orbitSupport_closure_eq_orbitMorphismRangeClosure_range A y]
    apply closure_minimal
    · rw [A.orbitSupport_eq_rationalPointSupport_range,
        rationalPointSupport_eq_closedPoint_image]
      rintro z ⟨q, ⟨g, rfl⟩, rfl⟩
      change (A.toMulAction.smul g y).1 (IsLocalRing.closedPoint k) ∈
        orbitBoundary A x
      have htranslated :
          (A.translationMorphism g).hom
              (y.1 (IsLocalRing.closedPoint k)) ∈ orbitBoundary A x := by
        refine ⟨?_, ?_⟩
        · have hz : (A.translationMorphism g).hom
            (y.1 (IsLocalRing.closedPoint k)) ∈
            (A.translationMorphism g).hom ''
              Set.range (A.orbitMorphismRangeClosure x).inclusion.hom :=
            ⟨y.1 (IsLocalRing.closedPoint k), hySupport, rfl⟩
          rwa [A.translationMorphism_image_orbitMorphismRangeClosure] at hz
        · intro hzOrbit
          have hzImage : (A.translationMorphism g).hom
              (y.1 (IsLocalRing.closedPoint k)) ∈
            (A.translationMorphism g).hom ''
              Set.range (A.orbitMorphismAt x).hom := by
            rw [A.translationMorphism_image_orbitMorphismAt_range]
            exact hzOrbit
          obtain ⟨w, hwOrbit, hw⟩ := hzImage
          have hwy : w = y.1 (IsLocalRing.closedPoint k) :=
            (Scheme.homeoOfIso (A.translationIso g)).injective hw
          exact hy.2 (hwy ▸ hwOrbit)
      exact A.translationMorphism_hom_closedPoint g y ▸ htranslated
    · exact orbitBoundary_isClosed A x
  have hB_le : B ≤ orbitRangeClosureSupport A x := by
    change orbitBoundary A x ⊆
      Set.range (A.orbitMorphismRangeClosure x).inclusion.hom
    exact Set.sdiff_subset
  have hB_ne : B ≠ orbitRangeClosureSupport A x := by
    intro hB
    let a : (ofAffine G).toScheme :=
      ((affinePointEquiv G).symm 1).1 (IsLocalRing.closedPoint k)
    let z : X.toScheme := (A.orbitMorphismAt x).hom a
    have hzOrbit : z ∈ Set.range (A.orbitMorphismAt x).hom :=
      ⟨a, rfl⟩
    have hzSupport : z ∈ orbitRangeClosureSupport A x := by
      change z ∈ Set.range (A.orbitMorphismRangeClosure x).inclusion.hom
      rw [A.orbitMorphismRangeClosure_range]
      exact subset_closure hzOrbit
    have hzB : z ∈ B := by
      rw [hB]
      exact hzSupport
    have hzBoundary : z ∈ orbitBoundary A x := hzB
    exact hzBoundary.2 hzOrbit
  exact lt_of_le_of_lt hleB (lt_of_le_of_ne hB_le hB_ne)

/-- A morphic action on a nonempty geometric variety has a smooth closed orbit. -/
public theorem exists_smooth_closed_orbit
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X) [Nonempty X.toScheme] :
    ∃ x : Point X,
      Smooth (A.orbitSubvariety x).toGeometric.structureMap ∧
        IsClosed (Set.range (A.orbitMorphismAt x).hom) := by
  let S : Set (Closeds X.toScheme) :=
    Set.range (orbitRangeClosureSupport A)
  have hSne : S.Nonempty := by
    obtain ⟨x, _⟩ :=
      exists_point_closedPoint_mem_of_isOpen X isOpen_univ Set.univ_nonempty
    exact ⟨orbitRangeClosureSupport A x, ⟨x, rfl⟩⟩
  obtain ⟨Z, hZS, hZmin⟩ := exists_minimal_closed X S hSne
  obtain ⟨x, rfl⟩ := hZS
  refine ⟨x, orbitSubvariety_smooth A x, ?_⟩
  by_contra hnotClosed
  have hboundaryNonempty : (orbitBoundary A x).Nonempty := by
    change (Set.range (A.orbitMorphismRangeClosure x).inclusion.hom \
      Set.range (A.orbitMorphismAt x).hom).Nonempty
    rw [Set.sdiff_nonempty]
    intro hclosureSubset
    apply hnotClosed
    have heq : Set.range (A.orbitMorphismAt x).hom =
        Set.range (A.orbitMorphismRangeClosure x).inclusion.hom := by
      apply Set.Subset.antisymm
      · rw [A.orbitMorphismRangeClosure_range]
        exact subset_closure
      · exact hclosureSubset
    rw [heq]
    exact (orbitRangeClosureSupport A x).isClosed
  letI : JacobsonSpace X.toScheme :=
    LocallyOfFiniteType.jacobsonSpace X.structureMap
  obtain ⟨z, hzBoundary, hzClosed⟩ :=
    nonempty_inter_closedPoints hboundaryNonempty
      (orbitBoundary_isClosed A x).isLocallyClosed
  let y : Point X :=
    (pointEquivClosedPoint X.structureMap).symm ⟨z, hzClosed⟩
  have hyClosedPoint :
      y.1 (IsLocalRing.closedPoint k) = z :=
    congrArg Subtype.val
      ((pointEquivClosedPoint X.structureMap).apply_symm_apply
        ⟨z, hzClosed⟩)
  have hyBoundary :
      y.1 (IsLocalRing.closedPoint k) ∈ orbitBoundary A x := by
    rw [hyClosedPoint]
    exact hzBoundary
  have hlt :=
    orbitRangeClosureSupport_lt_of_closedPoint_mem_boundary A x y hyBoundary
  exact hZmin (orbitRangeClosureSupport A y) ⟨y, rfl⟩ hlt
