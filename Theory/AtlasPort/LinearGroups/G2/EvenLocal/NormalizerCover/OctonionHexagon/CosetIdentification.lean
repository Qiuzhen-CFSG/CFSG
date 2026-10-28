module

public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification.Stabilizer

/-!
# Identifying the actual G₂ coset and octonion geometries

The short parabolic is the full stabilizer of the standard zero-product plane,
so its cosets identify with the intrinsic lines. The existing long-coset map
identifies the other vertex type with singular projective points. Flag
transitivity proves that geometric incidence is exactly a common coset
representative; combining the two maps gives an equivariant graph isomorphism.

The map preserves the specified long-point identification and sends the short
vertex represented by `g` to `g • standardLine`. These statements use the
actual octonion automorphism group and hold over every field, in particular
under the finite characteristic-two hypotheses of the intended consumer.

Source context: the split G₂ geometry used for Aschbacher--Smith, Theorem
0.1.2(1), printed pp.3--4, repeated on pp.481--482. The coordinate model and
normalizations are those of the licensed ATLAS port. Metric and apartment
properties are separate inputs to the parent hexagon assembly.
-/

public section

namespace Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
open LieParabolicSetup CosetIdentification
variable {F : Type*} [Field F]

/-- Short parabolic cosets are the actual two-dimensional zero-product subspaces. -/
noncomputable def shortCosetEquivZeroProductLine :
    (Model F ⧸ parabolic₁) ≃ ZeroProductLine F :=
  (Subgroup.quotientEquivOfEq shortParabolic_eq_lineStabilizer).trans
    (Equiv.ofBijective (MulAction.ofQuotientStabilizer (Model F) (standardLine (F := F)))
      ⟨MulAction.injective_ofQuotientStabilizer (Model F) (standardLine (F := F)), by
        intro L
        obtain ⟨g,hg⟩ := exists_line_translate L
        exact ⟨(g : Model F ⧸ MulAction.stabilizer (Model F) (standardLine (F := F))),hg⟩⟩)

@[simp] theorem shortCosetEquivZeroProductLine_coe (g : Model F) :
    shortCosetEquivZeroProductLine (g : Model F ⧸ parabolic₁) =
      g • (standardLine (F := F)) := by rfl

theorem shortCosetEquivZeroProductLine_smul (g : Model F) (v : Model F ⧸ parabolic₁) :
    shortCosetEquivZeroProductLine (g • v) = g • shortCosetEquivZeroProductLine v := by
  induction v using Quotient.inductionOn' with
  | h k => exact mul_smul g k (standardLine (F := F))

/-- Intrinsic incidence is exactly the existence of a common left-coset representative. -/
theorem pointOnLine_coset_iff (u : Model F ⧸ parabolic₁) (v : Model F ⧸ parabolic₂) :
    pointOnLine (longCosetEquivSingularPoints v) (shortCosetEquivZeroProductLine u) ↔
      ∃ g : Model F, (g : Model F ⧸ parabolic₁) = u ∧ (g : Model F ⧸ parabolic₂) = v := by
  constructor
  · intro h
    obtain ⟨g,hL,hp⟩ := exists_flag_translate _ _ h
    refine ⟨g,shortCosetEquivZeroProductLine.injective ?_,
      longCosetEquivSingularPoints.injective ?_⟩
    · exact hL
    · exact hp
  · rintro ⟨g,rfl,rfl⟩
    exact (pointOnLine_smul_iff g firstPoint standardLine).mpr firstPoint_on_standardLine

/-- The equivariant identification of both vertex types in the two geometries. -/
noncomputable def cosetVertexEquivGeometry : Vertex F ≃ GeometryVertex F :=
  Equiv.sumCongr shortCosetEquivZeroProductLine longCosetEquivSingularPoints

/-- The actual root-parabolic coset graph is the intrinsic octonion incidence graph. -/
noncomputable def cosetGeometryIso : incidenceGraph (F := F) ≃g geometryGraph (F := F) where
  toEquiv := cosetVertexEquivGeometry
  map_rel_iff' := by
    intro x y
    constructor
    · intro h
      cases x with
      | inl u =>
        cases y with
        | inl v => exact False.elim h
        | inr v =>
          obtain ⟨g,hu,hv⟩ := (pointOnLine_coset_iff u v).mp h
          exact Or.inl ⟨g,congrArg Sum.inl hu.symm,congrArg Sum.inr hv.symm⟩
      | inr u =>
        cases y with
        | inl v =>
          obtain ⟨g,hv,hu⟩ := (pointOnLine_coset_iff v u).mp h
          exact Or.inr ⟨g,congrArg Sum.inr hu.symm,congrArg Sum.inl hv.symm⟩
        | inr v => exact False.elim h
    · rintro (⟨g,rfl,rfl⟩ | ⟨g,rfl,rfl⟩)
      all_goals exact (pointOnLine_smul_iff g firstPoint standardLine).mpr firstPoint_on_standardLine

@[simp] theorem cosetGeometryIso_short (v : Model F ⧸ parabolic₁) :
    cosetGeometryIso (Sum.inl v) = Sum.inl (shortCosetEquivZeroProductLine v) := by rfl

@[simp] theorem cosetGeometryIso_long (v : Model F ⧸ parabolic₂) :
    cosetGeometryIso (Sum.inr v) = Sum.inr (longCosetEquivSingularPoints v) := by rfl

@[simp] theorem cosetGeometryIso_shortVertex (g : Model F) :
    cosetGeometryIso (shortVertex g) = Sum.inl (g • (standardLine (F := F))) := by rfl

theorem cosetGeometryIso_smul (g : Model F) (v : Vertex F) :
    cosetGeometryIso (g • v) = g • cosetGeometryIso v := by
  cases v with
  | inl u => exact congrArg Sum.inl (shortCosetEquivZeroProductLine_smul g u)
  | inr u => exact congrArg Sum.inr (longCosetEquivSingularPoints_smul g u)

/-- The graph identification with its action and both specified markings. -/
theorem exists_equivariant_cosetGeometryIso :
    ∃ e : incidenceGraph (F := F) ≃g geometryGraph (F := F),
      (∀ (g : Model F) (v : Vertex F), e (g • v) = g • e v) ∧
      (∀ v : Model F ⧸ parabolic₂,
        e (Sum.inr v) = Sum.inr (longCosetEquivSingularPoints v)) ∧
      (∀ g : Model F, e (shortVertex g) = Sum.inl (g • (standardLine (F := F)))) :=
  ⟨cosetGeometryIso,cosetGeometryIso_smul,cosetGeometryIso_long,cosetGeometryIso_shortVertex⟩

end Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
