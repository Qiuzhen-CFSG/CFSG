module

public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.Endpoint
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification.Basic
public import Theory.Representation.G2Natural
public import Theory.AtlasPort.Algebra.SplitOctonion.NormGeometry

/-!
# Natural and Weyl realizations of the binary G₂ hexagon

The Weyl model is the trace-zero octonion hyperplane. Its natural quotient
is the quotient by the scalar identity line. Two singular trace-zero
vectors with the same quotient image are equal: their difference is a
scalar identity, and comparing their norms forces that scalar to vanish.
Thus both maps preserve and reflect inclusions between singular subspaces.

We construct the actual point and line subspaces, prove their orders and
incidence correspondence, and check equivariance for the full octonion
automorphism group. In the six-dimensional quotient every nonzero vector
comes from a singular point. An actual group equivalence then realizes the
geometry by subgroups of the literal source quotient, furnishing every
field of `QuotientGeometry` without a cycle or girth premise.

These are the model and transport steps of Aschbacher–Smith 14.7.55(7),
combined manuscript (1 March 2004), printed pp.1066–1067. Identification of
the source module and marking of V, V₂ and the local actors remain separate.
The actual octonion coordinates and action use the existing attributed
ATLAS ports; see LICENSES/ATLAS.txt. No additional ATLAS source is copied.
-/

@[expose] public noncomputable section

namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry
open Atlas.G2 Atlas.SplitOctonion Atlas.G2.Natural
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon

private theorem norm_scalar_add {F : Type*} [Field F] (r : F) (y : Carrier F) :
    Atlas.SplitOctonion.norm (r • unit + y) =
      r ^ 2 + r * trace y + Atlas.SplitOctonion.norm y := by
  simp only [Atlas.SplitOctonion.norm, unit, Pi.add_apply, Pi.smul_apply, smul_eq_mul, trace]
  simp
  ring

/-- Singular vectors have distinct images in the natural quotient. -/
theorem natural_injective_on_singular {F : Type*} [Field F] [CharP F 2]
    (x y : TraceZero F) (hx : Atlas.SplitOctonion.norm x.val = 0) (hy : Atlas.SplitOctonion.norm y.val = 0)
    (he : mk F x = mk F y) : x = y := by
  obtain ⟨r,hr⟩ := (mk_eq_mk_iff F x y).mp he
  have hx' : x.val = r • unit + y.val := eq_add_of_sub_eq hr.symm
  have ht : trace y.val = 0 := y.property
  rw [hx', norm_scalar_add, hy, ht, mul_zero, add_zero, add_zero] at hx
  have hr0 : r = 0 := eq_zero_of_pow_eq_zero hx
  apply Subtype.ext
  simpa only [hr0, zero_smul, zero_add] using hx'

/-- Restrict an octonion subspace to the trace-zero hyperplane. -/
def traceRestriction (P : Submodule (ZMod 2) (Carrier (ZMod 2))) :
    Submodule (ZMod 2) (TraceZero (ZMod 2)) := P.comap (TraceZero (ZMod 2)).subtype

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- A map from the Weyl module that separates singular vectors. The natural
quotient and the Weyl identity will both be constructed instances. -/
structure SingularMap (W : Type*) [AddCommGroup W] [Module (ZMod 2) W] where
  linear : TraceZero (ZMod 2) →ₗ[ZMod 2] W
  separates : ∀ x y, Atlas.SplitOctonion.norm x.val = 0 → Atlas.SplitOctonion.norm y.val = 0 → linear x = linear y → x = y

/-- Actual inclusion of a singular subspace in either model. -/
def SingularMap.image (f : SingularMap W)
    (P : Submodule (ZMod 2) (Carrier (ZMod 2))) : Submodule (ZMod 2) W :=
  (traceRestriction P).map f.linear

/-- Every vector has zero trace and zero octonion norm. -/
def TotallySingular (P : Submodule (ZMod 2) (Carrier (ZMod 2))) : Prop :=
  ∀ x ∈ P, trace x = 0 ∧ Atlas.SplitOctonion.norm x = 0

private theorem point_singular (p : SingularPoints (ZMod 2)) :
    TotallySingular p.val.submodule := by
  intro x hx
  rw [Projectivization.submodule_eq] at hx
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hx
  constructor
  · change traceLinearMap (ZMod 2) (a • p.val.rep) = 0
    rw [map_smul]
    change a * trace p.val.rep = 0
    rw [p.property.1, mul_zero]
  · rw [Atlas.SplitOctonion.norm_smul, p.property.2, mul_zero]

private theorem line_singular (L : ZeroProductLine (ZMod 2)) :
    TotallySingular L.val := CosetIdentification.line_singular L

private theorem image_le_iff (f : SingularMap W)
    {P R : Submodule (ZMod 2) (Carrier (ZMod 2))}
    (hP : TotallySingular P) (hR : TotallySingular R) :
    f.image P ≤ f.image R ↔ P ≤ R := by
  constructor
  · intro h x hx
    have hx' : (⟨x,(hP x hx).1⟩ : TraceZero (ZMod 2)) ∈ traceRestriction P := hx
    obtain ⟨y,hy,he⟩ := h (Submodule.mem_map_of_mem hx')
    have hxy := f.separates y ⟨x,(hP x hx).1⟩ (hR y.val hy).2 (hP x hx).2 he
    have heq : y.val = x := congrArg Subtype.val hxy
    change y.val ∈ R at hy
    rwa [← heq]
  · intro h
    exact Submodule.map_mono (Submodule.comap_mono h)

private def intoImage (f : SingularMap W)
    (P : Submodule (ZMod 2) (Carrier (ZMod 2))) (hP : TotallySingular P)
    (x : P) : f.image P :=
  ⟨f.linear ⟨x.val, (hP x.val x.property).1⟩,
    ⟨⟨x.val, (hP x.val x.property).1⟩, x.property, rfl⟩⟩

private theorem intoImage_injective (f : SingularMap W)
    (P : Submodule (ZMod 2) (Carrier (ZMod 2))) (hP : TotallySingular P) :
    Function.Injective (intoImage f P hP) := by
  intro x y h
  have he := congrArg (fun v : f.image P => v.val) h
  change f.linear ⟨x.val, (hP x.val x.property).1⟩ =
    f.linear ⟨y.val, (hP y.val y.property).1⟩ at he
  have hxy := f.separates ⟨x.val, (hP x.val x.property).1⟩
    ⟨y.val, (hP y.val y.property).1⟩ (hP x.val x.property).2
    (hP y.val y.property).2 he
  exact Subtype.ext (congrArg (fun z : TraceZero (ZMod 2) => z.val) hxy)

private def imageEquiv (f : SingularMap W)
    (P : Submodule (ZMod 2) (Carrier (ZMod 2))) (hP : TotallySingular P) :
    P ≃ f.image P :=
  Equiv.ofBijective (intoImage f P hP) ⟨intoImage_injective f P hP, by
    rintro ⟨y,hy⟩
    obtain ⟨x,hx,rfl⟩ := hy
    exact ⟨⟨x.val,hx⟩,rfl⟩⟩

/-- The singular point in the actual target module. -/
def SingularMap.point (f : SingularMap W) (p : SingularPoints (ZMod 2)) :
    Submodule (ZMod 2) W := f.image p.val.submodule

/-- The doubly singular line in the actual target module. -/
def SingularMap.line (f : SingularMap W) (L : ZeroProductLine (ZMod 2)) :
    Submodule (ZMod 2) W := f.image L.val

theorem SingularMap.point_injective (f : SingularMap W) : Function.Injective f.point := by
  intro p q h
  apply Subtype.ext
  apply Projectivization.submodule_injective
  exact le_antisymm ((image_le_iff f (point_singular p) (point_singular q)).mp h.le)
    ((image_le_iff f (point_singular q) (point_singular p)).mp h.ge)

theorem SingularMap.line_injective (f : SingularMap W) : Function.Injective f.line := by
  intro L M h
  apply Subtype.ext
  exact le_antisymm ((image_le_iff f (line_singular L) (line_singular M)).mp h.le)
    ((image_le_iff f (line_singular M) (line_singular L)).mp h.ge)

theorem SingularMap.incidence (f : SingularMap W)
    (p : SingularPoints (ZMod 2)) (L : ZeroProductLine (ZMod 2)) :
    pointOnLine p L ↔ f.point p ≤ f.line L :=
  (image_le_iff f (point_singular p) (line_singular L)).symm

theorem SingularMap.point_card (f : SingularMap W) (p : SingularPoints (ZMod 2)) :
    Nat.card (f.point p) = 2 := by
  change Nat.card (f.image p.val.submodule) = 2
  rw [← Nat.card_congr (imageEquiv f _ (point_singular p)),
    Module.natCard_eq_pow_finrank (K := ZMod 2), p.val.finrank_submodule]
  simp

theorem SingularMap.line_card (f : SingularMap W) (L : ZeroProductLine (ZMod 2)) :
    Nat.card (f.line L) = 4 := by
  change Nat.card (f.image L.val) = 4
  rw [← Nat.card_congr (imageEquiv f _ (line_singular L)),
    Module.natCard_eq_pow_finrank (K := ZMod 2), L.property.1]
  simp

/-- Incidence realization in the multiplicative notation used for the source
quotient groups. -/
def SingularMap.geometry (f : SingularMap W) : QuotientGeometry (Multiplicative W) where
  point := ⟨fun p => (f.point p).toAddSubgroup.toSubgroup, by
    intro p q h
    apply f.point_injective
    apply Submodule.toAddSubgroup_injective
    exact AddSubgroup.toSubgroup.injective h⟩
  line := ⟨fun L => (f.line L).toAddSubgroup.toSubgroup, by
    intro L M h
    apply f.line_injective
    apply Submodule.toAddSubgroup_injective
    exact AddSubgroup.toSubgroup.injective h⟩
  point_card := f.point_card
  line_card := f.line_card
  incidence := f.incidence

/-- The identity map gives the seven-dimensional model. -/
def weylMap : SingularMap (TraceZero (ZMod 2)) where
  linear := LinearMap.id
  separates := fun _ _ _ _ h => h

/-- The genuine scalar quotient gives the six-dimensional model. -/
def naturalMap : SingularMap (Space (ZMod 2)) where
  linear := mk (ZMod 2)
  separates := natural_injective_on_singular

/-- The actual linear action is intertwined with the trace-zero octonion action. -/
def SingularMap.Equivariant (f : SingularMap W)
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) W) : Prop :=
  ∀ g x, ρ g (f.linear x) = f.linear (traceZeroAction (ZMod 2) g x)

private theorem image_equivariant (f : SingularMap W)
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) W) (hf : f.Equivariant ρ)
    (g : Model (ZMod 2)) (P : Submodule (ZMod 2) (Carrier (ZMod 2)))
    (hP : TotallySingular P) :
    f.image (P.map g.val.toLinearMap) = (f.image P).map (ρ g) := by
  ext v
  constructor
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨y,hy,he⟩ := hx
    let y' : TraceZero (ZMod 2) := ⟨y, (hP y hy).1⟩
    refine ⟨f.linear y', ⟨y',hy,rfl⟩, ?_⟩
    rw [hf]
    congr 1
    exact Subtype.ext he
  · rintro ⟨y,⟨x,hx,rfl⟩,rfl⟩
    refine ⟨traceZeroAction (ZMod 2) g x, ?_, (hf g x).symm⟩
    exact ⟨x.val,hx,rfl⟩

private theorem point_submodule_smul (g : Model (ZMod 2))
    (p : SingularPoints (ZMod 2)) :
    (g • p).val.submodule = p.val.submodule.map g.val.toLinearMap := by
  conv_lhs => rw [← singularPointMk_rep (ZMod 2) p, singularPointMk_smul]
  change (Projectivization.mk (ZMod 2) (g.val p.val.rep) _).submodule = _
  rw [Projectivization.submodule_mk, Projectivization.submodule_eq,
    Submodule.map_span, Set.image_singleton]
  rfl

/-- The point correspondence respects the full actual G₂ action. -/
theorem SingularMap.point_equivariant (f : SingularMap W)
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) W) (hf : f.Equivariant ρ)
    (g : Model (ZMod 2)) (p : SingularPoints (ZMod 2)) :
    f.point (g • p) = (f.point p).map (ρ g) := by
  unfold SingularMap.point
  rw [point_submodule_smul]
  exact image_equivariant f ρ hf g _ (point_singular p)

/-- The line correspondence respects the full actual G₂ action. -/
theorem SingularMap.line_equivariant (f : SingularMap W)
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) W) (hf : f.Equivariant ρ)
    (g : Model (ZMod 2)) (L : ZeroProductLine (ZMod 2)) :
    f.line (g • L) = (f.line L).map (ρ g) := by
  unfold SingularMap.line
  rw [line_smul_val]
  exact image_equivariant f ρ hf g _ (line_singular L)

theorem weylMap_equivariant : weylMap.Equivariant (traceZeroAction (ZMod 2)) :=
  fun _ _ => rfl

theorem naturalMap_equivariant : naturalMap.Equivariant (action (ZMod 2)) :=
  action_mk (ZMod 2)

private theorem traceRestriction_span (x : TraceZero (ZMod 2)) :
    traceRestriction ((ZMod 2) ∙ x.val) = (ZMod 2) ∙ x := by
  ext y
  change y.val ∈ (ZMod 2) ∙ x.val ↔ y ∈ (ZMod 2) ∙ x
  simp only [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a,Subtype.ext ha⟩
  · rintro ⟨a,ha⟩
    exact ⟨a,congrArg Subtype.val ha⟩

/-- The correspondence sends a singular vector to its actual image span. -/
theorem SingularMap.point_mk (f : SingularMap W) (x : TraceZero (ZMod 2))
    (hx : x.val ≠ 0) (hn : Atlas.SplitOctonion.norm x.val = 0) :
    f.point (singularPointMk (ZMod 2) x.val hx x.property hn) =
      (ZMod 2) ∙ f.linear x := by
  change f.image (Projectivization.mk (ZMod 2) x.val hx).submodule = _
  rw [Projectivization.submodule_mk]
  unfold SingularMap.image
  rw [traceRestriction_span, Submodule.map_span, Set.image_singleton]

/-- Every natural-module vector has a singular octonion lift. Over F₂ adding
its norm times the scalar identity corrects the norm without changing the class. -/
theorem natural_singular_lift (v : Space (ZMod 2)) :
    ∃ x : TraceZero (ZMod 2), Atlas.SplitOctonion.norm x.val = 0 ∧ mk (ZMod 2) x = v := by
  obtain ⟨y,rfl⟩ := mk_surjective (ZMod 2) v
  let r := Atlas.SplitOctonion.norm y.val
  refine ⟨r • identity (ZMod 2) + y, ?_, ?_⟩
  · change Atlas.SplitOctonion.norm (r • unit + y.val) = 0
    have ht : trace y.val = 0 := y.property
    rw [norm_scalar_add, ht, mul_zero, add_zero]
    change r ^ 2 + r = 0
    exact (by decide : ∀ a : ZMod 2, a ^ 2 + a = 0) r
  · rw [map_add, map_smul, mk_identity, smul_zero, zero_add]

/-- All nonzero vectors of the six-dimensional model are represented by
singular points; the correspondence is not merely a partial embedding. -/
theorem natural_point_of_nonzero (v : Space (ZMod 2)) (hv : v ≠ 0) :
    ∃ p : SingularPoints (ZMod 2), naturalMap.point p = (ZMod 2) ∙ v := by
  obtain ⟨x,hn,hx⟩ := natural_singular_lift v
  have hx0 : x.val ≠ 0 := by
    intro he
    have : x = 0 := Subtype.ext he
    rw [this, map_zero] at hx
    exact hv hx.symm
  refine ⟨singularPointMk (ZMod 2) x.val hx0 x.property hn, ?_⟩
  rw [naturalMap.point_mk x hx0 hn]
  change (ZMod 2) ∙ mk (ZMod 2) x = _
  rw [hx]

/-- Every nonzero singular Weyl vector likewise gives its actual point span. -/
theorem weyl_point_of_singular (x : TraceZero (ZMod 2)) (hx : x.val ≠ 0)
    (hn : Atlas.SplitOctonion.norm x.val = 0) :
    ∃ p : SingularPoints (ZMod 2), weylMap.point p = (ZMod 2) ∙ x :=
  ⟨singularPointMk (ZMod 2) x.val hx x.property hn, weylMap.point_mk x hx hn⟩

variable {Q R : Type*} [Group Q] [Group R]

/-- Transfer by an actual group equivalence; all incidence relations and orders
are preserved, with no geometric premise. -/
def transportGeometry (geom : QuotientGeometry Q) (e : Q ≃* R) : QuotientGeometry R where
  point := ⟨fun p => (geom.point p).map e.toMonoidHom, by
    intro p q h
    apply geom.point.injective
    exact Subgroup.map_injective e.injective h⟩
  line := ⟨fun L => (geom.line L).map e.toMonoidHom, by
    intro L M h
    apply geom.line.injective
    exact Subgroup.map_injective e.injective h⟩
  point_card := fun p => (Subgroup.card_map_of_injective e.injective).trans (geom.point_card p)
  line_card := fun L => (Subgroup.card_map_of_injective e.injective).trans (geom.line_card L)
  incidence := fun p L => (geom.incidence p L).trans
    (Subgroup.map_le_map_iff_of_injective e.injective).symm

/-- Clause 14.7.55(7), realized in the literal natural-module quotient. -/
def naturalQuotientGeometry (N : Subgroup Q) [N.Normal]
    (e : Multiplicative (Space (ZMod 2)) ≃* Q ⧸ N) : QuotientGeometry (Q ⧸ N) :=
  transportGeometry naturalMap.geometry e

/-- Clause 14.7.55(7), realized in the literal Weyl-module quotient. -/
def weylQuotientGeometry (N : Subgroup Q) [N.Normal]
    (e : Multiplicative (TraceZero (ZMod 2)) ≃* Q ⧸ N) : QuotientGeometry (Q ⧸ N) :=
  transportGeometry weylMap.geometry e

end CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry
