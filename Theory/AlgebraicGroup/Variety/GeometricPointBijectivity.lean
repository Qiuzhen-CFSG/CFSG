module

public import Theory.AlgebraicGroup.Variety.GeometricClosedImage
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective

/-!
# Rational-point bijectivity and underlying scheme points

This module proves the finite-type Jacobson argument used implicitly in
Borovoi, *Linear Algebraic Groups* (`Bor1`), AG.10 and in the proof of
Theorem 10.4.  A morphism between the reduced separated finite-type geometric
carriers is bijective on underlying scheme points whenever it is bijective on
rational points over an algebraically closed field.  The conclusion is only a
point-set bijection, not an isomorphism of schemes; in particular, no
separability or characteristic-zero hypothesis is used.

For surjectivity, Chevalley's theorem makes the scheme-point range
constructible.  A nonempty complement would contain a closed point because a
finite-type scheme over a field is Noetherian and Jacobson.  Closed points are
rational over the algebraically closed base, contradicting rational-point
surjectivity.  For injectivity, consider the scheme kernel pair.  Separatedness
makes the diagonal image closed.  Every closed kernel-pair point defines two
rational source points with the same image, so rational injectivity puts it on
the diagonal.  Jacobson density then makes the diagonal surjective, hence the
morphism universally injective and therefore injective on scheme points.  The
kernel pair is used directly and need not itself be reduced.
-/

set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
open Topology

namespace Theory.AlgebraicGroup.Variety.Geometric

universe u

variable {k : Type u} [Field k]

private theorem dense_constructible_contains_open_of_noetherian
    {alpha : Type u} [TopologicalSpace alpha] [NoetherianSpace alpha]
    [Nonempty alpha] {S : Set alpha} (hS : IsConstructible S)
    (hSdense : Dense S) :
    exists U : Set alpha, IsOpen U ∧ U.Nonempty ∧ U ⊆ S := by
  classical
  let I : Type u := {C : Set alpha // C ∈ irreducibleComponents alpha}
  have hIfinite : Set.Finite (irreducibleComponents alpha) :=
    NoetherianSpace.finite_irreducibleComponents
  have hlocal (C : I) : exists U : Set alpha, IsOpen U ∧ U.Nonempty ∧ U ⊆ S := by
    let O : Set alpha := (Set.sUnion (irreducibleComponents alpha \ {C.1}))ᶜ
    have hOopen : IsOpen O := by
      dsimp [O]
      rw [isOpen_compl_iff, Set.sUnion_eq_biUnion]
      exact hIfinite.sdiff.isClosed_biUnion fun W hW =>
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
      intro s t hs ht hsO htO
      obtain ⟨x, hxO, hxs⟩ := hsO
      obtain ⟨y, hyO, hyt⟩ := htO
      obtain ⟨z, hzC, hzs, hztO⟩ :=
        C.2.1.isPreirreducible s (t ∩ O) hs (ht.inter hOopen)
          ⟨x, hOsub hxO, hxs⟩ ⟨y, hOsub hyO, hyt, hyO⟩
      exact ⟨z, hztO.2, hzs, hztO.1⟩
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
      exact ⟨z, hzUO.1, ⟨⟨z, hzUO.2⟩, hzS, rfl⟩⟩
    letI : Nonempty O := hOne.to_subtype
    letI : PreirreducibleSpace O := Subtype.preirreducibleSpace hOpre
    obtain ⟨U, hUopen, hUne, hUT⟩ :=
      IsConstructible.exists_isOpen_nonempty_subset_of_dense hTconstructible hTdense
    refine ⟨Subtype.val '' U, ?_, hUne.image Subtype.val, ?_⟩
    · exact hOopen.isOpenEmbedding_subtypeVal.isOpenMap U hUopen
    · rintro z ⟨y, hyU, rfl⟩
      exact hUT hyU
  let U : I → Set alpha := fun C => Classical.choose (hlocal C)
  have hUopen (C : I) : IsOpen (U C) := (Classical.choose_spec (hlocal C)).1
  have hUne (C : I) : (U C).Nonempty := (Classical.choose_spec (hlocal C)).2.1
  have hUS (C : I) : U C ⊆ S := (Classical.choose_spec (hlocal C)).2.2
  refine ⟨⋃ C : I, U C, isOpen_iUnion hUopen, ?_, ?_⟩
  · obtain ⟨x⟩ := (inferInstance : Nonempty alpha)
    let C : I := ⟨irreducibleComponent x,
      show irreducibleComponent x ∈ irreducibleComponents alpha from
        irreducibleComponent_mem_irreducibleComponents x⟩
    obtain ⟨y, hy⟩ := hUne C
    exact ⟨y, Set.mem_iUnion.mpr ⟨C, hy⟩⟩
  · intro x hx
    obtain ⟨C, hxC⟩ := Set.mem_iUnion.mp hx
    exact hUS C hxC

private theorem constructible_nonempty_inter_closedPoints
    {V : Geometric k} {S : Set V.toScheme}
    (hS : IsConstructible S) (hSne : S.Nonempty) :
    (S ∩ closedPoints V.toScheme).Nonempty := by
  letI : CompactSpace V.toScheme :=
    QuasiCompact.compactSpace_of_compactSpace V.structureMap
  letI : IsNoetherian V.toScheme :=
    { __ := LocallyOfFiniteType.isLocallyNoetherian V.structureMap }
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
      mem_closure_iff.mp (show x ∈ closure S from hx) U hU hxU
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

private theorem morphism_locallyOfFiniteType {V W : Geometric k}
    (f : Morphism V W) : LocallyOfFiniteType f.hom := by
  haveI : LocallyOfFiniteType (f.hom ≫ W.structureMap) := by
    rw [f.commutes]
    infer_instance
  exact locallyOfFiniteType_of_comp f.hom W.structureMap

private theorem morphism_isSeparated {V W : Geometric k}
    (f : Morphism V W) : IsSeparated f.hom := by
  haveI : IsSeparated (f.hom ≫ W.structureMap) := by
    rw [f.commutes]
    infer_instance
  exact IsSeparated.of_comp f.hom W.structureMap

private theorem Morphism.injective_hom_of_injective_points
    [IsAlgClosed k] {V W : Geometric k} (f : Morphism V W)
    (hf : Function.Injective (fun x : Point V => f x)) :
    Function.Injective f.hom := by
  letI : LocallyOfFiniteType f.hom := morphism_locallyOfFiniteType f
  letI : IsSeparated f.hom := morphism_isSeparated f
  let P := pullback f.hom f.hom
  let p : P ⟶ Spec (.of k) := pullback.fst f.hom f.hom ≫ V.structureMap
  haveI : LocallyOfFiniteType p := by
    dsimp [p]
    infer_instance
  haveI : JacobsonSpace P := LocallyOfFiniteType.jacobsonSpace p
  have hclosed : IsClosed (Set.range (pullback.diagonal f.hom)) :=
    (pullback.diagonal f.hom).isClosedMap.isClosed_range
  have hclosedPoints : closedPoints P ⊆ Set.range (pullback.diagonal f.hom) := by
    intro z hz
    let q : Spec (.of k) ⟶ P := pointOfClosedPoint p z hz
    have hqfst : q ≫ pullback.fst f.hom f.hom ≫ V.structureMap = 𝟙 _ := by
      simpa [p, Category.assoc] using pointOfClosedPoint_comp p z hz
    have hqsnd : q ≫ pullback.snd f.hom f.hom ≫ V.structureMap = 𝟙 _ := by
      have hqfst' : q ≫ pullback.fst f.hom f.hom ≫ f.hom ≫ W.structureMap = 𝟙 _ := by
        simpa only [Category.assoc, f.commutes] using hqfst
      have hcon := congrArg (fun g => q ≫ g ≫ W.structureMap)
        (pullback.condition : pullback.fst f.hom f.hom ≫ f.hom =
          pullback.snd f.hom f.hom ≫ f.hom).symm
      simpa only [Category.assoc, f.commutes] using hcon.trans hqfst'
    let x : Point V := ⟨q ≫ pullback.fst f.hom f.hom, hqfst⟩
    let y : Point V := ⟨q ≫ pullback.snd f.hom f.hom, hqsnd⟩
    have hxy : f x = f y := by
      apply Subtype.ext
      exact congrArg (fun g => q ≫ g) (pullback.condition :
        pullback.fst f.hom f.hom ≫ f.hom =
          pullback.snd f.hom f.hom ≫ f.hom)
    have hproj : q ≫ pullback.fst f.hom f.hom =
        q ≫ pullback.snd f.hom f.hom := by
      exact congrArg Subtype.val (hf hxy)
    have hq : (q ≫ pullback.fst f.hom f.hom) ≫ pullback.diagonal f.hom = q := by
      apply pullback.hom_ext
      · simp
      · simpa [Category.assoc] using hproj
    refine ⟨(q ≫ pullback.fst f.hom f.hom) default, ?_⟩
    calc
      (pullback.diagonal f.hom) ((q ≫ pullback.fst f.hom f.hom) default) =
          ((q ≫ pullback.fst f.hom f.hom) ≫ pullback.diagonal f.hom) default := rfl
      _ = q default := congrArg (fun g => g default) hq
      _ = z := pointOfClosedPoint_apply p z hz default
  have hrange : Set.range (pullback.diagonal f.hom) = Set.univ := by
    rw [← Set.univ_subset_iff, ← closure_closedPoints]
    exact (closure_mono hclosedPoints).trans hclosed.closure_eq.le
  have hui : UniversallyInjective f.hom := by
    apply (UniversallyInjective.iff_diagonal f.hom).mpr
    rw [surjective_iff, ← Set.range_eq_univ]
    exact hrange
  letI : UniversallyInjective f.hom := hui
  exact f.hom.injective

private theorem Morphism.surjective_hom_of_surjective_points
    [IsAlgClosed k] {V W : Geometric k} (f : Morphism V W)
    (hf : Function.Surjective (fun x : Point V => f x)) :
    Function.Surjective f.hom := by
  intro y
  by_contra hy
  have hcompl_ne : (Set.range f.hom)ᶜ.Nonempty := ⟨y, hy⟩
  obtain ⟨z, hzcompl, hzclosed⟩ :=
    constructible_nonempty_inter_closedPoints f.range_isConstructible.compl hcompl_ne
  let zPoint : Point W :=
    (pointEquivClosedPoint W.structureMap).symm ⟨z, hzclosed⟩
  have hzPointRange : zPoint ∈ Set.range f := hf zPoint
  have hzrange : zPoint.1 (IsLocalRing.closedPoint k) ∈ Set.range f.hom :=
    (f.point_mem_range_iff_closedPoint_mem_range zPoint).mp hzPointRange
  have hzPoint : zPoint.1 (IsLocalRing.closedPoint k) = z :=
    congrArg Subtype.val
      ((pointEquivClosedPoint W.structureMap).apply_symm_apply ⟨z, hzclosed⟩)
  exact hzcompl (hzPoint ▸ hzrange)

/-- A geometric morphism over an algebraically closed field that is bijective
on rational points is bijective on the underlying points of its schemes. -/
public theorem Morphism.bijective_hom_of_bijective_points
    [IsAlgClosed k] {V W : Geometric k} (f : Morphism V W)
    (hf : Function.Bijective (fun x : Point V => f x)) :
    Function.Bijective f.hom :=
  ⟨f.injective_hom_of_injective_points hf.1,
    f.surjective_hom_of_surjective_points hf.2⟩

end Theory.AlgebraicGroup.Variety.Geometric
