module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Theory.AlgebraicGroup.Variety.ClosedLocus

set_option linter.style.haveILetI false

/-!
# Open and locally closed geometric subvarieties

An open subset of a reduced separated finite-type geometric variety carries its induced open
subscheme structure.  Finite type, separatedness, and reducedness pass through the open
immersion; quasi-compactness follows because a finite-type variety over a field is Noetherian,
so every open subset of its underlying space is compact.  The resulting `OpenSubvariety`
therefore remains inside the existing `Geometric` category, with its inclusion and mapping
universal property exposed explicitly.

A locally closed subset `S` is open in its closure.  We realize that statement canonically by
taking the existing reduced closed subvariety on `closure S`, then restricting it to the
preimage of the open coborder of `S`.  The identity
`coborder S \u2229 closure S = S` gives exact support, while the universal properties of the
closed and open immersions give restriction, composition, uniqueness, and rational-point
membership.  This factorization deliberately reuses `ClosedSubvariety` instead of changing its
API.

This is the scheme-theoretic induced-subvariety convention used in Borovoi, *Linear Algebraic
Groups* (`Bor1`), Section 1.7, and supplies the locally closed carriers needed for the orbit
geometry of Proposition 1.8.  The construction is independent of group actions and quotient
descent.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry

namespace Theory.AlgebraicGroup.Variety.Geometric

universe u

variable {k : Type u} [Field k]

/-- An open subvariety, represented by an open immersion with its induced variety data. -/
structure OpenSubvariety (V : Geometric k) where
  toGeometric : Geometric k
  inclusion : Morphism toGeometric V
  isOpenImmersion : IsOpenImmersion inclusion.hom

instance {V : Geometric k} (U : OpenSubvariety V) :
    IsOpenImmersion U.inclusion.hom := U.isOpenImmersion

/-- The open subvariety supported on `U`. -/
def openSubvariety (V : Geometric k) (U : V.toScheme.Opens) : OpenSubvariety V := by
  letI : IsLocallyNoetherian V.toScheme :=
    LocallyOfFiniteType.isLocallyNoetherian V.structureMap
  letI : CompactSpace V.toScheme :=
    QuasiCompact.compactSpace_of_compactSpace V.structureMap
  letI : IsNoetherian V.toScheme := { }
  let W : Geometric k :=
    { toScheme := U
      structureMap := U.ι ≫ V.structureMap
      finiteType := by infer_instance
      quasiCompact := by infer_instance
      separated := by infer_instance
      reduced := by infer_instance }
  exact
    { toGeometric := W
      inclusion :=
        { hom := U.ι
          commutes := rfl }
      isOpenImmersion := by infer_instance }

@[simp]
theorem openSubvariety_range (V : Geometric k) (U : V.toScheme.Opens) :
    Set.range (openSubvariety V U).inclusion.hom = U := by
  exact Scheme.Opens.range_ι U

theorem openSubvariety_isOpenImmersion (V : Geometric k) (U : V.toScheme.Opens) :
    IsOpenImmersion (openSubvariety V U).inclusion.hom := by
  infer_instance

/-- Restrict a morphism whose range lies in an open support. -/
def restrictToOpenSubvariety {V W : Geometric k} (U : V.toScheme.Opens)
    (f : Morphism W V) (hf : Set.range f.hom ⊆ U) :
    Morphism W (openSubvariety V U).toGeometric :=
  { hom := IsOpenImmersion.lift (openSubvariety V U).inclusion.hom f.hom <| by
      simpa only [openSubvariety_range] using hf
    commutes := by
      rw [← (openSubvariety V U).inclusion.commutes, ← Category.assoc,
        IsOpenImmersion.lift_fac, f.commutes] }

@[simp]
theorem restrictToOpenSubvariety_inclusion {V W : Geometric k}
    (U : V.toScheme.Opens) (f : Morphism W V) (hf : Set.range f.hom ⊆ U) :
    Morphism.comp (restrictToOpenSubvariety U f hf) (openSubvariety V U).inclusion = f := by
  apply Morphism.ext
  exact IsOpenImmersion.lift_fac _ _ _

theorem restrictToOpenSubvariety_unique {V W : Geometric k}
    (U : V.toScheme.Opens) (f : Morphism W V) (hf : Set.range f.hom ⊆ U)
    (g : Morphism W (openSubvariety V U).toGeometric)
    (hg : Morphism.comp g (openSubvariety V U).inclusion = f) :
    g = restrictToOpenSubvariety U f hf := by
  apply Morphism.ext
  apply (cancel_mono (openSubvariety V U).inclusion.hom).mp
  exact congrArg Morphism.hom
    (hg.trans (restrictToOpenSubvariety_inclusion U f hf).symm)

theorem existsUnique_restrictToOpenSubvariety {V W : Geometric k}
    (U : V.toScheme.Opens) (f : Morphism W V) (hf : Set.range f.hom ⊆ U) :
    ∃! g : Morphism W (openSubvariety V U).toGeometric,
      Morphism.comp g (openSubvariety V U).inclusion = f := by
  refine ⟨restrictToOpenSubvariety U f hf,
    restrictToOpenSubvariety_inclusion U f hf, ?_⟩
  intro g hg
  exact restrictToOpenSubvariety_unique U f hf g hg

theorem restrictToOpenSubvariety_comp {V W X : Geometric k}
    (U : V.toScheme.Opens) (f : Morphism W V) (hf : Set.range f.hom ⊆ U)
    (g : Morphism X W) :
    restrictToOpenSubvariety U (Morphism.comp g f) (by
      rintro y ⟨x, rfl⟩
      apply hf
      refine ⟨g.hom x, ?_⟩
      rw [Morphism.comp_hom, Scheme.Hom.comp_apply]) =
      Morphism.comp g (restrictToOpenSubvariety U f hf) := by
  apply Morphism.ext
  apply (cancel_mono (openSubvariety V U).inclusion.hom).mp
  change IsOpenImmersion.lift _ _ _ ≫ _ =
    (g.hom ≫ IsOpenImmersion.lift _ _ _) ≫ _
  rw [IsOpenImmersion.lift_fac, Category.assoc, IsOpenImmersion.lift_fac]
  exact Morphism.comp_hom g f

theorem point_mem_openSubvariety_iff (V : Geometric k) (U : V.toScheme.Opens)
    (x : Point V) :
    x.1 (IsLocalRing.closedPoint k) ∈ U ↔
      ∃! y : Point (openSubvariety V U).toGeometric,
        (openSubvariety V U).inclusion y = x := by
  constructor
  · intro hx
    have hrange : Set.range x.1 ⊆ U := by
      rintro _ ⟨z, rfl⟩
      have hz : z = IsLocalRing.closedPoint k := Subsingleton.elim _ _
      subst z
      exact hx
    let y : Point (openSubvariety V U).toGeometric :=
      ⟨IsOpenImmersion.lift (openSubvariety V U).inclusion.hom x.1
          (by simpa only [openSubvariety_range] using hrange),
        by
          rw [← (openSubvariety V U).inclusion.commutes,
            ← Category.assoc, IsOpenImmersion.lift_fac, x.2]⟩
    have hy : (openSubvariety V U).inclusion y = x := by
      apply Subtype.ext
      exact IsOpenImmersion.lift_fac _ _ _
    refine ⟨y, hy, ?_⟩
    intro y' hy'
    apply Subtype.ext
    apply (cancel_mono (openSubvariety V U).inclusion.hom).mp
    exact congrArg (fun p : Point V ↦ p.1) (hy'.trans hy.symm)
  · rintro ⟨y, hy, -⟩
    have hval := congrArg (fun p : Point V ↦ p.1) hy
    rw [← hval]
    have hmem : (openSubvariety V U).inclusion.hom
        (y.1 (IsLocalRing.closedPoint k)) ∈
        Set.range (openSubvariety V U).inclusion.hom :=
      ⟨y.1 (IsLocalRing.closedPoint k), rfl⟩
    rwa [openSubvariety_range] at hmem

/-- Every open support has a geometric carrier with the expected points and mapping property. -/
theorem exists_openSubvariety (V : Geometric k) (S : Set V.toScheme)
    (hS : IsOpen S) :
    ∃ U : OpenSubvariety V,
      Set.range U.inclusion.hom = S ∧
      (∀ x : Point V, x.1 (IsLocalRing.closedPoint k) ∈ S ↔
        ∃! y : Point U.toGeometric, U.inclusion y = x) ∧
      (∀ (W : Geometric k) (f : Morphism W V), Set.range f.hom ⊆ S →
        ∃! g : Morphism W U.toGeometric, Morphism.comp g U.inclusion = f) := by
  let O : V.toScheme.Opens := ⟨S, hS⟩
  refine ⟨openSubvariety V O, openSubvariety_range V O, ?_, ?_⟩
  · intro x
    exact point_mem_openSubvariety_iff V O x
  · intro W f hf
    exact existsUnique_restrictToOpenSubvariety O f hf

/-- A locally closed subvariety, represented by a locally closed immersion. -/
structure LocallyClosedSubvariety (V : Geometric k) where
  toGeometric : Geometric k
  inclusion : Morphism toGeometric V
  isImmersion : IsImmersion inclusion.hom

instance {V : Geometric k} (S : LocallyClosedSubvariety V) :
    IsImmersion S.inclusion.hom := S.isImmersion

/-- The open part of the reduced closure which supports a locally closed set. -/
abbrev reducedLocallyClosedClosure (V : Geometric k) (S : Set V.toScheme) :
    ClosedSubvariety V :=
  reducedClosedSubvariety V ⟨closure S, isClosed_closure⟩

/-- The open subset of the reduced closure which supports a locally closed set. -/
def locallyClosedOpen (V : Geometric k) (S : Set V.toScheme)
    (hS : IsLocallyClosed S) :
    (reducedLocallyClosedClosure V S).toGeometric.toScheme.Opens :=
  (reducedLocallyClosedClosure V S).inclusion.hom ⁻¹ᵁ
    ⟨coborder S, hS.isOpen_coborder⟩

/-- The open carrier inside the reduced closure of a locally closed set. -/
abbrev reducedLocallyClosedOpenCarrier (V : Geometric k) (S : Set V.toScheme)
    (hS : IsLocallyClosed S) :
    OpenSubvariety (reducedLocallyClosedClosure V S).toGeometric :=
  openSubvariety _ (locallyClosedOpen V S hS)

/-- The canonical reduced locally closed subvariety supported on `S`. -/
def reducedLocallyClosedSubvariety (V : Geometric k) (S : Set V.toScheme)
    (hS : IsLocallyClosed S) : LocallyClosedSubvariety V := by
  exact
    { toGeometric := (reducedLocallyClosedOpenCarrier V S hS).toGeometric
      inclusion := Morphism.comp
        (reducedLocallyClosedOpenCarrier V S hS).inclusion
        (reducedLocallyClosedClosure V S).inclusion
      isImmersion := by
        change IsImmersion
          ((reducedLocallyClosedOpenCarrier V S hS).inclusion.hom ≫
            (reducedLocallyClosedClosure V S).inclusion.hom)
        infer_instance }

@[simp]
theorem reducedLocallyClosedSubvariety_inclusion (V : Geometric k)
    (S : Set V.toScheme) (hS : IsLocallyClosed S) :
    (reducedLocallyClosedSubvariety V S hS).inclusion =
      Morphism.comp (reducedLocallyClosedOpenCarrier V S hS).inclusion
        (reducedLocallyClosedClosure V S).inclusion := by
  rfl

@[simp]
theorem reducedLocallyClosedSubvariety_range (V : Geometric k)
    (S : Set V.toScheme) (hS : IsLocallyClosed S) :
    Set.range (reducedLocallyClosedSubvariety V S hS).inclusion.hom = S := by
  change Set.range ⇑((reducedLocallyClosedOpenCarrier V S hS).inclusion.hom ≫
      (reducedLocallyClosedClosure V S).inclusion.hom) = S
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    openSubvariety_range]
  change (reducedLocallyClosedClosure V S).inclusion.hom ''
      ((reducedLocallyClosedClosure V S).inclusion.hom ⁻¹'
        coborder S) = S
  rw [Set.image_preimage_eq_inter_range,
    reducedClosedSubvariety_range]
  change coborder S ∩ closure S = S
  exact coborder_inter_closure

theorem reducedLocallyClosedSubvariety_isImmersion (V : Geometric k)
    (S : Set V.toScheme) (hS : IsLocallyClosed S) :
    IsImmersion (reducedLocallyClosedSubvariety V S hS).inclusion.hom := by
  infer_instance

/-- The closed-locus restriction of a map into `S` lands in the required open of the closure. -/
theorem restrictToReducedClosedSubvariety_range_subset_locallyClosedOpen
    {V W : Geometric k}
    (S : Set V.toScheme) (hS : IsLocallyClosed S) (f : Morphism W V)
    (hf : Set.range f.hom ⊆ S) :
    Set.range (restrictToReducedClosedSubvariety
      ⟨closure S, isClosed_closure⟩ f (hf.trans subset_closure)).hom ⊆
      locallyClosedOpen V S hS := by
  rintro z ⟨w, rfl⟩
  change (reducedLocallyClosedClosure V S).inclusion.hom
      ((restrictToReducedClosedSubvariety
        ⟨closure S, isClosed_closure⟩ f (hf.trans subset_closure)).hom w) ∈
    coborder S
  rw [← Scheme.Hom.comp_apply]
  have hfac := congrArg Morphism.hom
    (restrictToReducedClosedSubvariety_inclusion
      ⟨closure S, isClosed_closure⟩ f (hf.trans subset_closure))
  change (restrictToReducedClosedSubvariety
      ⟨closure S, isClosed_closure⟩ f (hf.trans subset_closure)).hom ≫
    (reducedLocallyClosedClosure V S).inclusion.hom = f.hom at hfac
  rw [hfac]
  exact subset_coborder (hf ⟨w, rfl⟩)

/-- Restrict a morphism from a reduced source to the canonical locally closed carrier. -/
def restrictToReducedLocallyClosedSubvariety {V W : Geometric k}
    (S : Set V.toScheme) (hS : IsLocallyClosed S) (f : Morphism W V)
    (hf : Set.range f.hom ⊆ S) :
    Morphism W (reducedLocallyClosedSubvariety V S hS).toGeometric :=
  restrictToOpenSubvariety (locallyClosedOpen V S hS)
    (restrictToReducedClosedSubvariety
      ⟨closure S, isClosed_closure⟩ f (hf.trans subset_closure))
    (restrictToReducedClosedSubvariety_range_subset_locallyClosedOpen S hS f hf)

@[simp]
theorem restrictToReducedLocallyClosedSubvariety_inclusion
    {V W : Geometric k} (S : Set V.toScheme) (hS : IsLocallyClosed S)
    (f : Morphism W V) (hf : Set.range f.hom ⊆ S) :
    Morphism.comp (restrictToReducedLocallyClosedSubvariety S hS f hf)
      (reducedLocallyClosedSubvariety V S hS).inclusion = f := by
  apply Morphism.ext
  change (restrictToOpenSubvariety (locallyClosedOpen V S hS)
      (restrictToReducedClosedSubvariety
        ⟨closure S, isClosed_closure⟩ f (hf.trans subset_closure)) _).hom ≫
      ((reducedLocallyClosedOpenCarrier V S hS).inclusion.hom ≫
        (reducedLocallyClosedClosure V S).inclusion.hom) = f.hom
  rw [← Category.assoc]
  have hopen := congrArg Morphism.hom
    (restrictToOpenSubvariety_inclusion (locallyClosedOpen V S hS)
      (restrictToReducedClosedSubvariety
        ⟨closure S, isClosed_closure⟩ f (hf.trans subset_closure))
      (restrictToReducedClosedSubvariety_range_subset_locallyClosedOpen S hS f hf))
  change (restrictToOpenSubvariety (locallyClosedOpen V S hS)
      (restrictToReducedClosedSubvariety
        ⟨closure S, isClosed_closure⟩ f (hf.trans subset_closure)) _).hom ≫
    (reducedLocallyClosedOpenCarrier V S hS).inclusion.hom =
      (restrictToReducedClosedSubvariety
        ⟨closure S, isClosed_closure⟩ f (hf.trans subset_closure)).hom at hopen
  rw [hopen]
  exact congrArg Morphism.hom
    (restrictToReducedClosedSubvariety_inclusion
      ⟨closure S, isClosed_closure⟩ f (hf.trans subset_closure))

theorem restrictToReducedLocallyClosedSubvariety_unique
    {V W : Geometric k} (S : Set V.toScheme) (hS : IsLocallyClosed S)
    (f : Morphism W V) (hf : Set.range f.hom ⊆ S)
    (g : Morphism W (reducedLocallyClosedSubvariety V S hS).toGeometric)
    (hg : Morphism.comp g (reducedLocallyClosedSubvariety V S hS).inclusion = f) :
    g = restrictToReducedLocallyClosedSubvariety S hS f hf := by
  apply Morphism.ext
  apply (cancel_mono (reducedLocallyClosedSubvariety V S hS).inclusion.hom).mp
  exact congrArg Morphism.hom
    (hg.trans (restrictToReducedLocallyClosedSubvariety_inclusion S hS f hf).symm)

theorem existsUnique_restrictToReducedLocallyClosedSubvariety
    {V W : Geometric k} (S : Set V.toScheme) (hS : IsLocallyClosed S)
    (f : Morphism W V) (hf : Set.range f.hom ⊆ S) :
    ∃! g : Morphism W (reducedLocallyClosedSubvariety V S hS).toGeometric,
      Morphism.comp g (reducedLocallyClosedSubvariety V S hS).inclusion = f := by
  refine ⟨restrictToReducedLocallyClosedSubvariety S hS f hf,
    restrictToReducedLocallyClosedSubvariety_inclusion S hS f hf, ?_⟩
  intro g hg
  exact restrictToReducedLocallyClosedSubvariety_unique S hS f hf g hg

theorem restrictToReducedLocallyClosedSubvariety_comp
    {V W X : Geometric k} (S : Set V.toScheme) (hS : IsLocallyClosed S)
    (f : Morphism W V) (hf : Set.range f.hom ⊆ S) (g : Morphism X W) :
    restrictToReducedLocallyClosedSubvariety S hS (Morphism.comp g f) (by
      rintro y ⟨x, rfl⟩
      apply hf
      refine ⟨g.hom x, ?_⟩
      rw [Morphism.comp_hom, Scheme.Hom.comp_apply]) =
      Morphism.comp g (restrictToReducedLocallyClosedSubvariety S hS f hf) := by
  apply Morphism.ext
  apply (cancel_mono
    (reducedLocallyClosedSubvariety V S hS).inclusion.hom).mp
  have hleft := congrArg Morphism.hom
    (restrictToReducedLocallyClosedSubvariety_inclusion S hS
      (Morphism.comp g f) (by
        rintro y ⟨x, rfl⟩
        apply hf
        refine ⟨g.hom x, ?_⟩
        rw [Morphism.comp_hom, Scheme.Hom.comp_apply]))
  have hright := congrArg Morphism.hom
    (restrictToReducedLocallyClosedSubvariety_inclusion S hS f hf)
  change (restrictToReducedLocallyClosedSubvariety S hS (Morphism.comp g f) _).hom ≫
    (reducedLocallyClosedSubvariety V S hS).inclusion.hom =
      g.hom ≫ f.hom at hleft
  change (restrictToReducedLocallyClosedSubvariety S hS f hf).hom ≫
    (reducedLocallyClosedSubvariety V S hS).inclusion.hom = f.hom at hright
  change _ ≫ _ = (g.hom ≫ _) ≫ _
  rw [hleft, Category.assoc, hright]

theorem point_mem_reducedLocallyClosedSubvariety_iff
    (V : Geometric k) (S : Set V.toScheme) (hS : IsLocallyClosed S)
    (x : Point V) :
    x.1 (IsLocalRing.closedPoint k) ∈ S ↔
      ∃! y : Point (reducedLocallyClosedSubvariety V S hS).toGeometric,
        (reducedLocallyClosedSubvariety V S hS).inclusion y = x := by
  constructor
  · intro hx
    obtain ⟨z, hz, -⟩ :=
      (point_mem_reducedClosedSubvariety_iff V
        ⟨closure S, isClosed_closure⟩ x).mp (subset_closure hx)
    have hzOpen : z.1 (IsLocalRing.closedPoint k) ∈ locallyClosedOpen V S hS := by
      change (reducedLocallyClosedClosure V S).inclusion.hom
          (z.1 (IsLocalRing.closedPoint k)) ∈ coborder S
      have hval := congrArg (fun p : Point V ↦ p.1) hz
      change z.1 ≫ (reducedLocallyClosedClosure V S).inclusion.hom = x.1 at hval
      have heval := congrArg
        (fun q : Spec (.of k) ⟶ V.toScheme ↦ q (IsLocalRing.closedPoint k)) hval
      change (reducedLocallyClosedClosure V S).inclusion.hom
        (z.1 (IsLocalRing.closedPoint k)) =
          x.1 (IsLocalRing.closedPoint k) at heval
      rw [heval]
      exact subset_coborder hx
    obtain ⟨y, hyOpen, -⟩ :=
      (point_mem_openSubvariety_iff
        (reducedLocallyClosedClosure V S).toGeometric
        (locallyClosedOpen V S hS) z).mp hzOpen
    have hy : (reducedLocallyClosedSubvariety V S hS).inclusion y = x := by
      apply Subtype.ext
      have hopen := congrArg (fun p : Point (reducedLocallyClosedClosure V S).toGeometric ↦ p.1)
        hyOpen
      have hclosed := congrArg (fun p : Point V ↦ p.1) hz
      change y.1 ≫ (reducedLocallyClosedOpenCarrier V S hS).inclusion.hom = z.1 at hopen
      change z.1 ≫ (reducedLocallyClosedClosure V S).inclusion.hom = x.1 at hclosed
      change (y.1 ≫ (reducedLocallyClosedOpenCarrier V S hS).inclusion.hom) ≫
        (reducedLocallyClosedClosure V S).inclusion.hom = x.1
      rw [hopen, hclosed]
    refine ⟨y, hy, ?_⟩
    intro y' hy'
    apply Subtype.ext
    apply (cancel_mono
      (reducedLocallyClosedSubvariety V S hS).inclusion.hom).mp
    exact congrArg (fun p : Point V ↦ p.1) (hy'.trans hy.symm)
  · rintro ⟨y, hy, -⟩
    have hval := congrArg (fun p : Point V ↦ p.1) hy
    rw [← hval]
    have hmem : (reducedLocallyClosedSubvariety V S hS).inclusion.hom
        (y.1 (IsLocalRing.closedPoint k)) ∈
        Set.range (reducedLocallyClosedSubvariety V S hS).inclusion.hom :=
      ⟨y.1 (IsLocalRing.closedPoint k), rfl⟩
    rwa [reducedLocallyClosedSubvariety_range] at hmem

/-- Every locally closed support has a reduced geometric carrier with the expected universal
property for maps from geometric (hence reduced) sources. -/
theorem exists_reducedLocallyClosedSubvariety (V : Geometric k)
    (S : Set V.toScheme) (hS : IsLocallyClosed S) :
    ∃ T : LocallyClosedSubvariety V,
      Set.range T.inclusion.hom = S ∧
      (∀ x : Point V, x.1 (IsLocalRing.closedPoint k) ∈ S ↔
        ∃! y : Point T.toGeometric, T.inclusion y = x) ∧
      (∀ (W : Geometric k) (f : Morphism W V), Set.range f.hom ⊆ S →
        ∃! g : Morphism W T.toGeometric, Morphism.comp g T.inclusion = f) := by
  refine ⟨reducedLocallyClosedSubvariety V S hS,
    reducedLocallyClosedSubvariety_range V S hS, ?_, ?_⟩
  · intro x
    exact point_mem_reducedLocallyClosedSubvariety_iff V S hS x
  · intro W f hf
    exact existsUnique_restrictToReducedLocallyClosedSubvariety S hS f hf

end Theory.AlgebraicGroup.Variety.Geometric
