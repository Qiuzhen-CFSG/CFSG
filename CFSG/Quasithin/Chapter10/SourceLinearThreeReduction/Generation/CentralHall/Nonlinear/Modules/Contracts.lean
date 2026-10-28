module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Inputs
public import CFSG.Quasithin.Chapter10.SourceA5ModuleQuadraticBound
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Orbits

/-!
# Earlier source obligations for the nonlinear module analysis

The seed analysis in D.3.5--9, D.3.21 and 3.2.6, together with the nonnormal
part of 7.0.1, must give a separated seed on the original minimal setup.
The second, independent obligation is the small-module recognition on its
literal moved subgroup. It may use subgroup minimality above the centralizer,
the genuine four-model component catalogue, and both original cubic bounds.
In particular the odd PSL₂ and J₁ alternatives still have to be excluded.

These are specifications of missing source proofs. Neither is an instance
or an assertion that the corresponding source theorem has been proved.
`Modules.Source` supplies their conditional assembly and retains both premises.
Source: Aschbacher--Smith, pp.195--207,581,695--737,741--742.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The earlier separated-seed conclusions, before passing to the moved subgroup.
Both possible orientations of the original homogeneous seed are allowed. -/
structure SeparatedSeed (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (t : G) : Prop where
  full_eq_local : D.fullModule = D.moduleSubgroup
  stable : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ normalizer (D.seed : Set G)
  separated : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
    D.seed ≤ centralizer (L : Set G)

/-- Subgroup minimality for the literal moved central quotient. This does not
assert an isomorphism to a model or that the central kernel is trivial. -/
def MovedMinimal (D : FundamentalSetup KnownSimple.IsKnownSimple T L) : Prop :=
  ∀ J : Subgroup G, J ≤ ⁅D.fullModule,L⁆ → L ≤ normalizer (J : Set G) →
    J = ⁅D.fullModule,L⁆ ∨ J ≤ centralizer (L : Set G)

/-- The needed original-seed implication of 3.2.6 and the nonnormal part of
7.0.1. The supplied cubic bounds have separate completed source proofs. -/
def SeedAnalysisAt (T : Sylow 2 G) : Prop :=
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (H : Subgroup G) (B : Subgroup H) (_c : Context D H B),
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
    SourceLocalModuleCubicBound D → SourceFullModuleCubicBound D →
      ∃ t ∈ (T : Subgroup G), t ∉ normalizer (L : Set G) ∧ SeparatedSeed D t

/-- The independent B.4.2/B.4.5 recognition and central-kernel analysis.
It must construct the actual three rows, including whole-module coordinates
in the orthogonal and Suzuki cases. No recognition certificate is supplied. -/
def MovedRecognitionAt (T : Sylow 2 G) : Prop :=
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (H : Subgroup G) (B : Subgroup H) (_c : Context D H B),
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
    Chapter1.Section02.NonnormalCComponentModel (L ⧸ pCore 2 L) →
    SourceLocalModuleCubicBound D → SourceFullModuleCubicBound D →
    ModuleGeometry D → MovedMinimal D → ModuleRow D

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
