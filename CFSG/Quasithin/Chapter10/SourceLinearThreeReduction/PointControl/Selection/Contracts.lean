module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.Centralizer
public import Theory.Representation.SL2.BinarySmallModels
public import Theory.Representation.BinaryConjugationSection

/-!
# Source geometry still needed for the chosen non-A₅ module

These contracts separate the actual module choice from its two moving-
Thompson point geometries. Both natural-module predicates specify the
original quotient map and conjugation coordinates on [V,L]/C_[V,L](L).
They are not group-family labels. The centralizing-Thompson branch needs
no module recognition.

The rank-one branch asks for Baumann fixed orbits. The binary-three branch
asks for the half-Sylow or the omega-center residual geometry on the
literal saturated point. The final selection assembly must prove all
three contracts; none is asserted here as a source theorem.
Source: Aschbacher--Smith, 3.2.6, 10.1.1--2 and 10.2.8--9,
printed pp.581,741--742,749--750.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Stellmacher
namespace CFSG.Quasithin.Chapter10.PointControl.Selection
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The literal natural rank-one quotient of the original moved factor. -/
def RankOneNatural (D : FundamentalSetup KnownSimple.IsKnownSimple T L) : Prop :=
  ∃ (n : ℕ) (hn : 1 < n),
    letI : NeZero n := ⟨by omega⟩
    letI : Algebra (ZMod 2) (GaloisField 2 n) := ZMod.algebra _ 2
    ∃ e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
      Nonempty (BinaryConjugationSection L ⁅D.fullModule,L⁆
        (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
        (SL2.BinarySmall.natural.comp
          (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))

/-- The literal binary-three natural quotient, allowing its fixed kernel. -/
def BinaryThreeNatural (D : FundamentalSetup KnownSimple.IsKnownSimple T L) : Prop :=
  ∃ e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
    Nonempty (BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
      ((specialLinearNatural 3).comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))

/-- The minimal source choice, retaining precisely the moving-Thompson
rows of 10.1.1 and the actual crossed centralization. -/
def ModuleChoiceAt (T : Sylow 2 G) : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ L : Subgroup G, L ∈ Chapter1.LStar G (T : Subgroup G) →
    ChapterA.Section04.IsFaithfulSignalizerType L → IsQuasisimple (L ⧸ pCore 2 L) →
    ¬ (T : Subgroup G) ≤ normalizer (L : Set G) →
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) →
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L, D.IsMinimalFullModule ∧
      ∃ t ∈ (T : Subgroup G), t ∉ normalizer (L : Set G) ∧
        (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) ∧
        (elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G) ∨
          (D.fullModule = D.moduleSubgroup ∧ (RankOneNatural D ∨ BinaryThreeNatural D)))

/-- Source rank-one geometry, before applying saturation or half-Sylow
uniqueness to obtain the desired point-control conclusions. -/
structure RankOnePointGeometry
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (t : G) : Prop where
  fixed_layer : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≤
    centralizer (((T : Subgroup G) ⊓ normalizer (L : Set G)) : Set G)
  baumann_normalizer : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal
  fixed_orbits : ∀ v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom,
    v ≠ 1 → v ∉ centralizer (localOrbit T L : Set G) →
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (D.maximalLocal ⊓ centralizer ({v} : Set G)) →
    ∃ m ∈ D.maximalLocal, (ChapterB.baumann (T : Subgroup G)).map
      (MulAut.conj m).toMonoidHom ≤ centralizer ({v} : Set G)

/-- The two binary-three source point geometries. The residual in the
second row is computed inside L₀, not postulated for C_G(Ω₁Z(C_T(v))). -/
def BinaryThreePointCase
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (v : G) : Prop :=
  (((T : Subgroup G) ⊓ centralizer ({v} : Set G) =
      (T : Subgroup G) ⊓ normalizer (L : Set G)) ∧
    normalizer (((T : Subgroup G) ⊓ normalizer (L : Set G)) : Set G) ≤ D.maximalLocal) ∨
  (3 ∣ Nat.card (L ⧸ pCore 2 L) ∧
    localOrbit T L ≤ centralizer (omegaCenterIn (T : Subgroup G) : Set G) ∧
    cubicPerfectCore (localOrbit T L ⊓ centralizer
      (omegaCenterIn ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) : Set G)) = L)

/-- The actual fixed-layer and saturated-point data in the binary-three row. -/
structure BinaryThreePointGeometry
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (t : G) : Prop where
  fixed_layer : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≤
    centralizer (((T : Subgroup G) ⊓ normalizer (L : Set G)) : Set G)
  points : ∀ v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom,
    v ≠ 1 → v ∉ centralizer (localOrbit T L : Set G) →
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (D.maximalLocal ⊓ centralizer ({v} : Set G)) → BinaryThreePointCase D v

/-- Rank-one source geometry can be proved independently of module choice. -/
def RankOneGeometryAt (T : Sylow 2 G) : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
    D.IsMinimalFullModule → D.fullModule = D.moduleSubgroup →
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) → RankOneNatural D →
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G) →
    ∀ t ∈ (T : Subgroup G), t ∉ normalizer (L : Set G) →
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) →
      HalfSylowUnique D → RankOnePointGeometry D t

/-- Binary-three source geometry can be proved independently of module choice.
Half-Sylow uniqueness is the permitted conditional input of SelectionAt. -/
def BinaryThreeGeometryAt (T : Sylow 2 G) : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
    D.IsMinimalFullModule → D.fullModule = D.moduleSubgroup →
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) → BinaryThreeNatural D →
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G) →
    ∀ t ∈ (T : Subgroup G), t ∉ normalizer (L : Set G) →
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) →
      HalfSylowUnique D → BinaryThreePointGeometry D t

end CFSG.Quasithin.Chapter10.PointControl.Selection
