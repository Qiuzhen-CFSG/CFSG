module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Contracts
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking.FactorKernel

/-!
# Earlier source inputs for the large-offender fixed-space argument

The context is exactly the hypotheses of `Recognition.GeometryAt`. The packets below
separate earlier intersection/residual facts from the component-action facts. They do not assume offender normalization or uniform
fixed spaces. In particular orbit rigidity is stated without assuming that
three divides the component order: the Suzuki row must be retained.

The action input retains the literal central quotient kernel and asks only
for a nonfixed vector fixed by an involution stabilizing the moved factor.
The displacement, supplement, kernel and fixed-vector arguments are proved in
this directory. Only the earlier intersection/residual producer remains open.
Source: Aschbacher--Smith 10.1.1--3, 10.2.10 and 10.2.12, pp.741--754.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition.FixedSpaces
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The original assumptions, without any offender-geometry conclusion. -/
structure Context (D : FundamentalSetup KnownSimple.IsKnownSimple T L) : Prop where
  many : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard
  minimal : D.IsMinimalFullModule
  nonnormal : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)
  notA5 : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
  pointCentralizers : ∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 →
    centralizer ({v} : Set G) ≤ D.maximalLocal
  crossed : ∀ t ∈ (T : Subgroup G), t ∉ normalizer (L : Set G) →
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)
  size : 8 < (centralizer (L : Set G)).relIndex ⁅D.fullModule,L⁆

/-- Earlier 10.2.10(1) and the conjugate-overgroup consequence of 10.1.3. -/
structure IntersectionInputs (D : FundamentalSetup KnownSimple.IsKnownSimple T L) : Prop where
  outside : ∀ x ∉ D.maximalLocal,
    ⁅D.fullModule,L⁆ ⊓ (⁅D.fullModule,L⁆).map (MulAut.conj x).toMonoidHom = ⊥
  orbitRigid : ∀ x : G,
    localOrbit T L ≤ D.maximalLocal.map (MulAut.conj x).toMonoidHom → x ∈ D.maximalLocal

/-- The precise component-action facts used in the proof through (*).
No moduleA bound, module classification or natural marking is assumed. -/
structure ActionInputs (D : FundamentalSetup KnownSimple.IsKnownSimple T L) : Prop where
  simple : IsSimpleGroup (L ⧸ pCore 2 L)
  even : 2 ∣ Nat.card (L ⧸ pCore 2 L)
  kernel : commutatorPreimage L ⁅D.fullModule,L⁆
    (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G)) = L.pCoreIn 2
  nonfixed : ∀ b ∈ D.maximalLocal,
    b ∈ normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) → b ^ 2 = 1 →
    ¬ ⁅D.fullModule,L⁆ ⊓ centralizer ({b} : Set G) ≤ centralizer (L : Set G)

/-- The centralizing-Thompson branch is already proved by fusion and the kernel argument.
Its definition contains only earlier module facts, not offender geometry. -/
def FusionCase (D : FundamentalSetup KnownSimple.IsKnownSimple T L) : Prop :=
  Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G)

/-- Produce the earlier intersections only outside the already proved fusion
branch. In particular a Suzuki row may be discharged by `FusionCase`. -/
def IntersectionsAt (T : Sylow 2 G) : Prop :=
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
    Context D → FusionCase D ∨ IntersectionInputs D

/-- The nonfixed involution-fixed vector contract in
the remaining branch. Simplicity, parity and the component kernel are proved
in `Quotient` and `Kernel`. `FixedVectors.source_actionsAt` proves this contract
without any further module-model premise. -/
def ActionsAt (T : Sylow 2 G) : Prop :=
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
    Context D → ¬ FusionCase D →
    ∀ b ∈ D.maximalLocal,
      b ∈ normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) → b ^ 2 = 1 →
      ¬ ⁅D.fullModule,L⁆ ⊓ centralizer ({b} : Set G) ≤ centralizer (L : Set G)

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition.FixedSpaces
