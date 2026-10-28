module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Theory.AlgebraicGroup.Variety.Complete

set_option linter.style.haveILetI false

/-!
# Reduced closed loci of geometric varieties

Every closed subset of a scheme-backed geometric variety is given its canonical reduced
closed-subscheme structure.  The construction uses the ideal sheaf of functions vanishing on
the subset.  Its affine restrictions are quotients by radical vanishing ideals, so the resulting
scheme is reduced; the closed immersion has exactly the prescribed topological support.

Maps from reduced geometric sources factor uniquely through this closed subscheme when their
underlying maps land in its support.  This gives the rational-point membership criterion and
focused constructions for equalizers, arbitrary intersections, and common equalizers.  In
particular, intersecting the equalizers of the action maps with the identity produces the common
fixed locus of all rational points of a closed subgroup.  Closed-subvariety inheritance supplies
completeness for every locus constructed here.

This is the scheme-theoretic form of Borovoi, *Linear Algebraic Groups* (`Bor1`), Section 1.7:
closed sets and intersections carry their reduced subvariety structures.  The completeness
statements use Bor1 10.1, namely that closed subvarieties of complete varieties are complete.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

namespace Theory.AlgebraicGroup.Variety.Geometric

universe u

variable {k : Type u} [Field k]

@[ext]
theorem Morphism.ext {V W : Geometric k} {f g : Morphism V W}
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- The subscheme defined by the vanishing ideal of a closed support is reduced. -/
theorem isReduced_vanishingIdeal_subscheme
    {X : Scheme.{u}} (Z : Closeds X) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  change IsReduced I.subscheme
  rw [IsReduced.iff_of_openCover _ I.subschemeCover.openCover]
  intro U
  change IsReduced (Spec (.of
    (Γ(X, (show X.affineOpens from U).1) ⧸
      I.ideal (show X.affineOpens from U))))
  rw [affine_isReduced_iff]
  apply (Ideal.isRadical_iff_quotient_reduced _).mp
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
  exact PrimeSpectrum.isRadical_vanishingIdeal _

/-- The canonical reduced closed subvariety supported on `Z`.

Its ideal sheaf is the sheaf of functions vanishing at every point of `Z`; affine-locally this
is the radical vanishing ideal, rather than extra certificate data attached to the carrier.
-/
def reducedClosedSubvariety (V : Geometric k)
    (Z : Closeds V.toScheme) : ClosedSubvariety V := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  let W : Geometric k :=
    { toScheme := I.subscheme
      structureMap := I.subschemeι ≫ V.structureMap
      finiteType := by infer_instance
      quasiCompact := by infer_instance
      separated := by infer_instance
      reduced := isReduced_vanishingIdeal_subscheme Z }
  exact
    { toGeometric := W
      inclusion :=
        { hom := I.subschemeι
          commutes := rfl }
      isClosedImmersion := by infer_instance }

/-- The canonical reduced closed subvariety has precisely the requested support. -/
@[simp]
theorem reducedClosedSubvariety_range (V : Geometric k)
    (Z : Closeds V.toScheme) :
    Set.range (reducedClosedSubvariety V Z).inclusion.hom = Z := by
  change Set.range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = Z
  rw [Scheme.IdealSheafData.range_subschemeι,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]

/-- The support inclusion is a closed immersion. -/
theorem reducedClosedSubvariety_isClosedImmersion (V : Geometric k)
    (Z : Closeds V.toScheme) :
    IsClosedImmersion (reducedClosedSubvariety V Z).inclusion.hom := by
  infer_instance

/-- A quasi-compact map from a reduced scheme which lands in `Z` annihilates the vanishing
ideal sheaf of `Z`. -/
theorem vanishingIdeal_le_ker_of_isReduced
    {X Y : Scheme.{u}} [IsReduced Y] (Z : Closeds X)
    (f : Y ⟶ X) [QuasiCompact f] (hf : Set.range f ⊆ Z) :
    Scheme.IdealSheafData.vanishingIdeal Z ≤ f.ker := by
  have hsupport : f.ker.support ≤ Z := by
    change (f.ker.support : Set X) ⊆ (Z : Set X)
    rw [Scheme.Hom.support_ker]
    exact Z.isClosed.closure_subset_iff.mpr hf
  calc
    Scheme.IdealSheafData.vanishingIdeal Z ≤
        Scheme.IdealSheafData.vanishingIdeal f.ker.support :=
      Scheme.IdealSheafData.vanishingIdeal_antimono hsupport
    _ = f.ker.radical := Scheme.IdealSheafData.vanishingIdeal_support
    _ = f.ker := by
      apply Scheme.IdealSheafData.ext
      funext U
      rw [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
      apply Ideal.IsRadical.radical
      intro x hx
      obtain ⟨n, hn⟩ := hx
      change (f.app U).hom x = 0
      have : IsNilpotent ((f.app U).hom x) :=
        ⟨n, by simpa only [map_pow, RingHom.mem_ker] using hn⟩
      exact this.eq_zero

/-- Restrict a morphism from a reduced geometric source to a reduced closed support. -/
def restrictToReducedClosedSubvariety
    {V W : Geometric k} (Z : Closeds V.toScheme) (f : Morphism W V)
    (hf : Set.range f.hom ⊆ Z) :
    Morphism W (reducedClosedSubvariety V Z).toGeometric := by
  haveI : QuasiCompact (f.hom ≫ V.structureMap) :=
    f.commutes.symm ▸ inferInstance
  letI : QuasiCompact f.hom := QuasiCompact.of_comp f.hom V.structureMap
  let hker := vanishingIdeal_le_ker_of_isReduced Z f.hom hf
  let hI : (reducedClosedSubvariety V Z).inclusion.hom.ker ≤ f.hom.ker := by
    change (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι.ker ≤ f.hom.ker
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact hker
  exact
    { hom := IsClosedImmersion.lift
        (reducedClosedSubvariety V Z).inclusion.hom f.hom hI
      commutes := by
        rw [← (reducedClosedSubvariety V Z).inclusion.commutes,
          ← Category.assoc, IsClosedImmersion.lift_fac, f.commutes] }

/-- Restriction followed by the closed immersion is the original morphism. -/
@[simp]
theorem restrictToReducedClosedSubvariety_inclusion
    {V W : Geometric k} (Z : Closeds V.toScheme) (f : Morphism W V)
    (hf : Set.range f.hom ⊆ Z) :
    Morphism.comp (restrictToReducedClosedSubvariety Z f hf)
      (reducedClosedSubvariety V Z).inclusion = f := by
  apply Morphism.ext
  change IsClosedImmersion.lift _ _ _ ≫ _ = f.hom
  exact IsClosedImmersion.lift_fac _ _ _

/-- A morphism into the reduced closed locus is determined by its composite with the inclusion. -/
theorem restrictToReducedClosedSubvariety_unique
    {V W : Geometric k} (Z : Closeds V.toScheme) (f : Morphism W V)
    (hf : Set.range f.hom ⊆ Z)
    (g : Morphism W (reducedClosedSubvariety V Z).toGeometric)
    (hg : Morphism.comp g (reducedClosedSubvariety V Z).inclusion = f) :
    g = restrictToReducedClosedSubvariety Z f hf := by
  apply Morphism.ext
  apply (cancel_mono (reducedClosedSubvariety V Z).inclusion.hom).mp
  exact congrArg Morphism.hom
    (hg.trans (restrictToReducedClosedSubvariety_inclusion Z f hf).symm)

/-- Universal property of the canonical reduced closed locus for reduced geometric sources. -/
theorem existsUnique_restrictToReducedClosedSubvariety
    {V W : Geometric k} (Z : Closeds V.toScheme) (f : Morphism W V)
    (hf : Set.range f.hom ⊆ Z) :
    ∃! g : Morphism W (reducedClosedSubvariety V Z).toGeometric,
      Morphism.comp g (reducedClosedSubvariety V Z).inclusion = f := by
  refine ⟨restrictToReducedClosedSubvariety Z f hf,
    restrictToReducedClosedSubvariety_inclusion Z f hf, ?_⟩
  intro g hg
  exact restrictToReducedClosedSubvariety_unique Z f hf g hg

/-- A rational point belongs to a closed support exactly when it lifts uniquely to its reduced
closed subvariety. -/
theorem point_mem_reducedClosedSubvariety_iff
    (V : Geometric k) (Z : Closeds V.toScheme) (x : Point V) :
    x.1 (IsLocalRing.closedPoint k) ∈ Z ↔
      ∃! y : Point (reducedClosedSubvariety V Z).toGeometric,
        (reducedClosedSubvariety V Z).inclusion y = x := by
  constructor
  · intro hx
    have hrange : Set.range x.1 ⊆ Z := by
      rintro _ ⟨z, rfl⟩
      have hz : z = IsLocalRing.closedPoint k := Subsingleton.elim _ _
      subst z
      exact hx
    haveI : QuasiCompact (x.1 ≫ V.structureMap) := x.2.symm ▸ inferInstance
    letI : QuasiCompact x.1 := QuasiCompact.of_comp x.1 V.structureMap
    let hker := vanishingIdeal_le_ker_of_isReduced Z x.1 hrange
    let hI : (reducedClosedSubvariety V Z).inclusion.hom.ker ≤ x.1.ker := by
      change (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι.ker ≤ x.1.ker
      rw [Scheme.IdealSheafData.ker_subschemeι]
      exact hker
    let y : Point (reducedClosedSubvariety V Z).toGeometric :=
      ⟨IsClosedImmersion.lift
          (reducedClosedSubvariety V Z).inclusion.hom x.1 hI,
        by
          rw [← (reducedClosedSubvariety V Z).inclusion.commutes,
            ← Category.assoc, IsClosedImmersion.lift_fac, x.2]⟩
    have hy : (reducedClosedSubvariety V Z).inclusion y = x := by
      apply Subtype.ext
      exact IsClosedImmersion.lift_fac _ _ _
    refine ⟨y, hy, ?_⟩
    intro y' hy'
    apply Subtype.ext
    apply (cancel_mono (reducedClosedSubvariety V Z).inclusion.hom).mp
    exact congrArg (fun p : Point V => p.1) (hy'.trans hy.symm)
  · rintro ⟨y, hy, -⟩
    have hval := congrArg (fun p : Point V => p.1) hy
    rw [← hval]
    change (y.1 ≫ (reducedClosedSubvariety V Z).inclusion.hom)
      (IsLocalRing.closedPoint k) ∈ Z
    have hmem :
        (reducedClosedSubvariety V Z).inclusion.hom
            (y.1 (IsLocalRing.closedPoint k)) ∈
          Set.range (reducedClosedSubvariety V Z).inclusion.hom :=
      ⟨y.1 (IsLocalRing.closedPoint k), rfl⟩
    rw [reducedClosedSubvariety_range] at hmem
    exact hmem

/-- Reduced closed subvarieties of a complete geometric variety are complete. -/
theorem reducedClosedSubvariety_isComplete
    {V : Geometric k} (Z : Closeds V.toScheme) (hV : IsComplete V) :
    IsComplete (reducedClosedSubvariety V Z).toGeometric :=
  (reducedClosedSubvariety V Z).isComplete hV

/-- Every closed subset of a geometric variety is the exact support of a reduced closed
subvariety, with the expected point, mapping, and completeness properties. -/
theorem exists_reducedClosedSubvariety (V : Geometric k)
    (S : Set V.toScheme) (hS : IsClosed S) :
    ∃ Z : ClosedSubvariety V,
      Set.range Z.inclusion.hom = S ∧
      (∀ x : Point V, x.1 (IsLocalRing.closedPoint k) ∈ S ↔
        ∃! y : Point Z.toGeometric, Z.inclusion y = x) ∧
      (∀ (W : Geometric k) (f : Morphism W V), Set.range f.hom ⊆ S →
        ∃! g : Morphism W Z.toGeometric, Morphism.comp g Z.inclusion = f) ∧
      (IsComplete V → IsComplete Z.toGeometric) := by
  let C : Closeds V.toScheme := ⟨S, hS⟩
  refine ⟨reducedClosedSubvariety V C, reducedClosedSubvariety_range V C, ?_, ?_, ?_⟩
  · intro x
    exact point_mem_reducedClosedSubvariety_iff V C x
  · intro W f hf
    exact existsUnique_restrictToReducedClosedSubvariety C f hf
  · exact reducedClosedSubvariety_isComplete C

/-! ## Basic morphism constructions -/

/-- The constant morphism from `V` with value the rational point `x`. -/
def Morphism.constant (V : Geometric k) {W : Geometric k} (x : Point W) :
    Morphism V W where
  hom := V.structureMap ≫ x.1
  commutes := by rw [Category.assoc, x.2, Category.comp_id]

/-- A constant morphism takes every rational point to its defining value. -/
@[simp]
theorem Morphism.constant_apply (V : Geometric k) {W : Geometric k}
    (x : Point W) (y : Point V) : Morphism.constant V x y = x := by
  apply Subtype.ext
  change y.1 ≫ V.structureMap ≫ x.1 = x.1
  rw [← Category.assoc, y.2, Category.id_comp]

/-- Pair two geometric morphisms into the geometric product. -/
def Morphism.prodLift [IsAlgClosed k] {U V W : Geometric k}
    (f : Morphism U V) (g : Morphism U W) : Morphism U (prod V W) where
  hom := pullback.lift f.hom g.hom (by rw [f.commutes, g.commutes])
  commutes := by
    change pullback.lift f.hom g.hom _ ≫
      pullback.fst V.structureMap W.structureMap ≫ V.structureMap = U.structureMap
    rw [pullback.lift_fst_assoc, f.commutes]

/-- The first projection of a paired morphism is its first component. -/
@[simp]
theorem Morphism.prodLift_fst [IsAlgClosed k] {U V W : Geometric k}
    (f : Morphism U V) (g : Morphism U W) :
    Morphism.comp (Morphism.prodLift f g) (fst V W) = f := by
  apply Morphism.ext
  exact pullback.lift_fst _ _ _

/-- The second projection of a paired morphism is its second component. -/
@[simp]
theorem Morphism.prodLift_snd [IsAlgClosed k] {U V W : Geometric k}
    (f : Morphism U V) (g : Morphism U W) :
    Morphism.comp (Morphism.prodLift f g) (snd V W) = g := by
  apply Morphism.ext
  exact pullback.lift_snd _ _ _

/-- On rational points, pairing morphisms agrees with `prodPointEquiv`. -/
@[simp]
theorem Morphism.prodPointEquiv_prodLift_apply [IsAlgClosed k]
    {U V W : Geometric k} (f : Morphism U V) (g : Morphism U W) (x : Point U) :
    prodPointEquiv V W (Morphism.prodLift f g x) = (f x, g x) := by
  apply Prod.ext
  · apply Subtype.ext
    change x.1 ≫ pullback.lift f.hom g.hom _ ≫
      pullback.fst V.structureMap W.structureMap = x.1 ≫ f.hom
    rw [pullback.lift_fst]
  · apply Subtype.ext
    change x.1 ≫ pullback.lift f.hom g.hom _ ≫
      pullback.snd V.structureMap W.structureMap = x.1 ≫ g.hom
    rw [pullback.lift_snd]

/-! ## Equalizers -/

/-- Regard a geometric morphism as a morphism in the category of schemes over `Spec k`. -/
def Morphism.toOver {V W : Geometric k} (f : Morphism V W) :
    Over.mk V.structureMap ⟶ Over.mk W.structureMap :=
  Over.homMk f.hom f.commutes

/-- The scheme-theoretic equalizer inclusion of two geometric morphisms. -/
def equalizerInclusion {V W : Geometric k} (f g : Morphism V W) :
    (equalizer f.toOver g.toOver).left ⟶ V.toScheme :=
  (equalizer.ι f.toOver g.toOver).left

/-- The scheme-theoretic equalizer inclusion is a closed immersion because the target is
separated over the base field. -/
theorem equalizerInclusion_isClosedImmersion {V W : Geometric k}
    (f g : Morphism V W) : IsClosedImmersion (equalizerInclusion f g) := by
  letI : IsSeparated (Over.mk W.structureMap).hom := W.separated
  change IsClosedImmersion (equalizer.ι f.toOver g.toOver).left
  exact AlgebraicGeometry.isClosedImmersion_equalizer_ι_left _ _

/-- The closed support of the scheme-theoretic equalizer. -/
def equalizerSupport {V W : Geometric k}
    (f g : Morphism V W) : Closeds V.toScheme :=
  ⟨Set.range (equalizerInclusion f g),
    (equalizerInclusion_isClosedImmersion f g).isClosedEmbedding.isClosed_range⟩

/-- The equalizer support is exactly the range of its scheme-theoretic inclusion. -/
theorem equalizerSupport_eq_range {V W : Geometric k}
    (f g : Morphism V W) :
    (equalizerSupport f g : Set V.toScheme) = Set.range (equalizerInclusion f g) := rfl

/-- The reduced equalizer of two geometric morphisms. -/
def reducedEqualizer {V W : Geometric k}
    (f g : Morphism V W) : ClosedSubvariety V :=
  reducedClosedSubvariety V (equalizerSupport f g)

/-- The reduced equalizer has the same support as the scheme-theoretic equalizer. -/
@[simp]
theorem reducedEqualizer_range {V W : Geometric k} (f g : Morphism V W) :
    Set.range (reducedEqualizer f g).inclusion.hom =
      Set.range (equalizerInclusion f g) := by
  change Set.range
    (reducedClosedSubvariety V (equalizerSupport f g)).inclusion.hom = _
  rw [reducedClosedSubvariety_range, equalizerSupport_eq_range]

/-- The canonical comparison from the reduced equalizer to the scheme-theoretic equalizer. -/
def reducedEqualizerToEqualizer
    {V W : Geometric k} (f g : Morphism V W) :
    (reducedEqualizer f g).toGeometric.toScheme ⟶
      (equalizer f.toOver g.toOver).left := by
  let e := equalizerInclusion f g
  let j := (reducedEqualizer f g).inclusion.hom
  haveI : IsClosedImmersion e := equalizerInclusion_isClosedImmersion f g
  haveI : QuasiCompact e := by infer_instance
  have heSupport : e.ker.support = equalizerSupport f g := by
    apply SetLike.coe_injective
    change (e.ker.support : Set V.toScheme) = Set.range e
    rw [Scheme.Hom.support_ker, e.isClosedEmbedding.isClosed_range.closure_eq]
  have hker : e.ker ≤ j.ker := by
    change e.ker ≤
      (Scheme.IdealSheafData.vanishingIdeal (equalizerSupport f g)).subschemeι.ker
    rw [Scheme.IdealSheafData.ker_subschemeι, ← heSupport,
      Scheme.IdealSheafData.vanishingIdeal_support]
    exact Scheme.IdealSheafData.le_radical e.ker
  exact IsClosedImmersion.lift e j hker

/-- The comparison to the scheme-theoretic equalizer factors its reduced inclusion. -/
theorem reducedEqualizerToEqualizer_fac
    {V W : Geometric k} (f g : Morphism V W) :
    reducedEqualizerToEqualizer f g ≫ equalizerInclusion f g =
      (reducedEqualizer f g).inclusion.hom := by
  letI : IsClosedImmersion (equalizerInclusion f g) :=
    equalizerInclusion_isClosedImmersion f g
  exact IsClosedImmersion.lift_fac _ _ _

/-- The inclusion of the reduced equalizer equalizes the two original morphisms. -/
theorem reducedEqualizer_condition {V W : Geometric k} (f g : Morphism V W) :
    (reducedEqualizer f g).inclusion.hom ≫ f.hom =
      (reducedEqualizer f g).inclusion.hom ≫ g.hom := by
  have hcondition : equalizerInclusion f g ≫ f.hom =
      equalizerInclusion f g ≫ g.hom := by
    exact congrArg Over.Hom.left (equalizer.condition f.toOver g.toOver)
  rw [← reducedEqualizerToEqualizer_fac f g,
    Category.assoc, Category.assoc, hcondition]

/-- Rational points of the reduced equalizer are precisely the points where the maps agree. -/
theorem point_mem_reducedEqualizer_iff {V W : Geometric k}
    (f g : Morphism V W) (x : Point V) :
    f x = g x ↔
      ∃! y : Point (reducedEqualizer f g).toGeometric,
        (reducedEqualizer f g).inclusion y = x := by
  change f x = g x ↔
    ∃! y : Point (reducedClosedSubvariety V (equalizerSupport f g)).toGeometric,
      (reducedClosedSubvariety V (equalizerSupport f g)).inclusion y = x
  constructor
  · intro h
    have hhom : x.1 ≫ f.hom = x.1 ≫ g.hom :=
      congrArg (fun p : Point W => p.1) h
    let xOver : Over.mk (𝟙 (Spec (.of k))) ⟶ Over.mk V.structureMap :=
      Over.homMk x.1 x.2
    have hOver : xOver ≫ f.toOver = xOver ≫ g.toOver := by
      apply Over.OverMorphism.ext
      exact hhom
    let yOver := equalizer.lift xOver hOver
    have hy := congrArg Over.Hom.left (equalizer.lift_ι xOver hOver)
    change yOver.left ≫ equalizerInclusion f g = x.1 at hy
    have hmem : x.1 (IsLocalRing.closedPoint k) ∈
        Set.range (equalizerInclusion f g) := by
      rw [← hy]
      exact ⟨yOver.left (IsLocalRing.closedPoint k), rfl⟩
    apply (point_mem_reducedClosedSubvariety_iff V (equalizerSupport f g) x).mp
    change x.1 (IsLocalRing.closedPoint k) ∈ Set.range (equalizerInclusion f g)
    exact hmem
  · intro hx
    apply Subtype.ext
    have hcondition := reducedEqualizer_condition f g
    change
      (reducedClosedSubvariety V (equalizerSupport f g)).inclusion.hom ≫ f.hom =
        (reducedClosedSubvariety V (equalizerSupport f g)).inclusion.hom ≫ g.hom
      at hcondition
    have hxhom : x.1 ≫ f.hom = x.1 ≫ g.hom := by
      obtain ⟨y, hy, -⟩ := hx
      have hyhom := congrArg (fun p : Point V => p.1) hy
      rw [← hyhom]
      simpa only [Category.assoc] using congrArg (fun q => y.1 ≫ q) hcondition
    exact hxhom

/-- A morphism which equalizes `f` and `g` has range in their equalizer support. -/
theorem range_subset_equalizerSupport_of_comp_eq
    {U V W : Geometric k} (f g : Morphism V W) (h : Morphism U V)
    (hh : Morphism.comp h f = Morphism.comp h g) :
    Set.range h.hom ⊆ equalizerSupport f g := by
  have hhom := congrArg Morphism.hom hh
  change h.hom ≫ f.hom = h.hom ≫ g.hom at hhom
  have hOver : h.toOver ≫ f.toOver = h.toOver ≫ g.toOver := by
    apply Over.OverMorphism.ext
    exact hhom
  let q := equalizer.lift h.toOver hOver
  have hq := congrArg Over.Hom.left (equalizer.lift_ι h.toOver hOver)
  change q.left ≫ equalizerInclusion f g = h.hom at hq
  rintro x ⟨y, hy⟩
  change x ∈ Set.range (equalizerInclusion f g)
  refine ⟨q.left y, ?_⟩
  exact (congrArg (fun m : _ ⟶ V.toScheme => m y) hq).trans hy

/-- Restrict a morphism which equalizes `f` and `g` to their reduced equalizer. -/
def restrictToReducedEqualizer
    {U V W : Geometric k} (f g : Morphism V W) (h : Morphism U V)
    (hh : Morphism.comp h f = Morphism.comp h g) :
    Morphism U (reducedEqualizer f g).toGeometric :=
  restrictToReducedClosedSubvariety (equalizerSupport f g) h
    (range_subset_equalizerSupport_of_comp_eq f g h hh)

/-- The specialized equalizer restriction factors the original morphism. -/
@[simp]
theorem restrictToReducedEqualizer_inclusion
    {U V W : Geometric k} (f g : Morphism V W) (h : Morphism U V)
    (hh : Morphism.comp h f = Morphism.comp h g) :
    Morphism.comp (restrictToReducedEqualizer f g h hh)
      (reducedEqualizer f g).inclusion = h := by
  exact restrictToReducedClosedSubvariety_inclusion _ _ _

/-- The specialized equalizer restriction is unique. -/
theorem restrictToReducedEqualizer_unique
    {U V W : Geometric k} (f g : Morphism V W) (h : Morphism U V)
    (hh : Morphism.comp h f = Morphism.comp h g)
    (q : Morphism U (reducedEqualizer f g).toGeometric)
    (hq : Morphism.comp q (reducedEqualizer f g).inclusion = h) :
    q = restrictToReducedEqualizer f g h hh := by
  exact restrictToReducedClosedSubvariety_unique _ _ _ q hq

/-- A reduced equalizer in a complete variety is complete. -/
theorem reducedEqualizer_isComplete {V W : Geometric k}
    (f g : Morphism V W) (hV : IsComplete V) :
    IsComplete (reducedEqualizer f g).toGeometric :=
  reducedClosedSubvariety_isComplete _ hV

/-! ## Arbitrary intersections and common equalizers -/

/-- The reduced closed subvariety supported on an arbitrary intersection. -/
def reducedIntersection {ι : Type*} (V : Geometric k)
    (Z : ι → Closeds V.toScheme) : ClosedSubvariety V :=
  reducedClosedSubvariety V (⨅ i, Z i)

/-- The reduced intersection has exactly the set-theoretic intersection as its support. -/
@[simp]
theorem reducedIntersection_range {ι : Type*} (V : Geometric k)
    (Z : ι → Closeds V.toScheme) :
    Set.range (reducedIntersection V Z).inclusion.hom =
      ⋂ i, (Z i : Set V.toScheme) := by
  change Set.range (reducedClosedSubvariety V (⨅ i, Z i)).inclusion.hom = _
  rw [reducedClosedSubvariety_range]
  ext x
  simp

/-- Rational points of an arbitrary reduced intersection satisfy every support condition. -/
theorem point_mem_reducedIntersection_iff {ι : Type*} (V : Geometric k)
    (Z : ι → Closeds V.toScheme) (x : Point V) :
    (∀ i, x.1 (IsLocalRing.closedPoint k) ∈ Z i) ↔
      ∃! y : Point (reducedIntersection V Z).toGeometric,
        (reducedIntersection V Z).inclusion y = x := by
  change (∀ i, x.1 (IsLocalRing.closedPoint k) ∈ Z i) ↔
    ∃! y : Point (reducedClosedSubvariety V (⨅ i, Z i)).toGeometric,
      (reducedClosedSubvariety V (⨅ i, Z i)).inclusion y = x
  constructor
  · intro h
    apply (point_mem_reducedClosedSubvariety_iff V (⨅ i, Z i) x).mp
    exact Closeds.mem_iInf.mpr h
  · intro h
    have hmem := (point_mem_reducedClosedSubvariety_iff V (⨅ i, Z i) x).mpr h
    exact Closeds.mem_iInf.mp hmem

/-- Restrict a morphism whose range lies in every member of a family to the reduced
intersection. -/
def restrictToReducedIntersection
    {ι : Type*} {U : Geometric k} (V : Geometric k)
    (Z : ι → Closeds V.toScheme) (h : Morphism U V)
    (hh : ∀ i, Set.range h.hom ⊆ Z i) :
    Morphism U (reducedIntersection V Z).toGeometric :=
  restrictToReducedClosedSubvariety (⨅ i, Z i) h fun _ hx =>
    Closeds.mem_iInf.mpr fun i => hh i hx

/-- The specialized intersection restriction factors the original morphism. -/
@[simp]
theorem restrictToReducedIntersection_inclusion
    {ι : Type*} {U : Geometric k} (V : Geometric k)
    (Z : ι → Closeds V.toScheme) (h : Morphism U V)
    (hh : ∀ i, Set.range h.hom ⊆ Z i) :
    Morphism.comp (restrictToReducedIntersection V Z h hh)
      (reducedIntersection V Z).inclusion = h := by
  exact restrictToReducedClosedSubvariety_inclusion _ _ _

/-- The specialized intersection restriction is unique. -/
theorem restrictToReducedIntersection_unique
    {ι : Type*} {U : Geometric k} (V : Geometric k)
    (Z : ι → Closeds V.toScheme) (h : Morphism U V)
    (hh : ∀ i, Set.range h.hom ⊆ Z i)
    (q : Morphism U (reducedIntersection V Z).toGeometric)
    (hq : Morphism.comp q (reducedIntersection V Z).inclusion = h) :
    q = restrictToReducedIntersection V Z h hh := by
  exact restrictToReducedClosedSubvariety_unique _ _ _ q hq

/-- An arbitrary reduced intersection in a complete variety is complete. -/
theorem reducedIntersection_isComplete {ι : Type*} {V : Geometric k}
    (Z : ι → Closeds V.toScheme) (hV : IsComplete V) :
    IsComplete (reducedIntersection V Z).toGeometric :=
  reducedClosedSubvariety_isComplete _ hV

/-- The reduced common equalizer of two indexed families of geometric morphisms. -/
def reducedCommonEqualizer {ι : Type*} {V W : Geometric k}
    (f g : ι → Morphism V W) : ClosedSubvariety V :=
  reducedIntersection V fun i => equalizerSupport (f i) (g i)

/-- Rational points of the reduced common equalizer are exactly the simultaneous equalizer
points.  Taking one family to be action maps and the other to be the identity yields a common
fixed locus. -/
theorem point_mem_reducedCommonEqualizer_iff
    {ι : Type*} {V W : Geometric k} (f g : ι → Morphism V W) (x : Point V) :
    (∀ i, f i x = g i x) ↔
      ∃! y : Point (reducedCommonEqualizer f g).toGeometric,
        (reducedCommonEqualizer f g).inclusion y = x := by
  change (∀ i, f i x = g i x) ↔
    ∃! y : Point
        (reducedIntersection V fun i => equalizerSupport (f i) (g i)).toGeometric,
      (reducedIntersection V fun i => equalizerSupport (f i) (g i)).inclusion y = x
  rw [← point_mem_reducedIntersection_iff]
  constructor
  · intro h i
    exact (point_mem_reducedClosedSubvariety_iff V
      (equalizerSupport (f i) (g i)) x).mpr
        ((point_mem_reducedEqualizer_iff (f i) (g i) x).mp (h i))
  · intro h i
    exact (point_mem_reducedEqualizer_iff (f i) (g i) x).mpr
      ((point_mem_reducedClosedSubvariety_iff V
        (equalizerSupport (f i) (g i)) x).mp (h i))

/-- A reduced common equalizer in a complete variety is complete. -/
theorem reducedCommonEqualizer_isComplete
    {ι : Type*} {V W : Geometric k} (f g : ι → Morphism V W)
    (hV : IsComplete V) : IsComplete (reducedCommonEqualizer f g).toGeometric :=
  reducedIntersection_isComplete _ hV

/-- The reduced common fixed locus of an indexed family of endomorphisms. -/
def reducedFixedLocus {ι : Type*} {V : Geometric k}
    (f : ι → Morphism V V) : ClosedSubvariety V :=
  reducedCommonEqualizer f fun _ => Morphism.id V

/-- Rational points of the reduced fixed locus are exactly the common fixed points. -/
theorem point_mem_reducedFixedLocus_iff
    {ι : Type*} {V : Geometric k} (f : ι → Morphism V V) (x : Point V) :
    (∀ i, f i x = x) ↔
      ∃! y : Point (reducedFixedLocus f).toGeometric,
        (reducedFixedLocus f).inclusion y = x := by
  change (∀ i, f i x = Morphism.id V x) ↔ _
  exact point_mem_reducedCommonEqualizer_iff f (fun _ => Morphism.id V) x

/-- A reduced common fixed locus in a complete variety is complete. -/
theorem reducedFixedLocus_isComplete
    {ι : Type*} {V : Geometric k} (f : ι → Morphism V V)
    (hV : IsComplete V) : IsComplete (reducedFixedLocus f).toGeometric :=
  reducedCommonEqualizer_isComplete _ _ hV

end Theory.AlgebraicGroup.Variety.Geometric
