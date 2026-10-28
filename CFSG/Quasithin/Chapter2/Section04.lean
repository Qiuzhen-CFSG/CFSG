module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FieldActorSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.OvergroupSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CatalogueSetupSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterNormalizerSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.OvercomponentSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.ModelSource.Recognition
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.OvergroupCoreSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.ElementarySource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.TorusAlternativesSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterTorusSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.HallSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.SylowSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.AbsorptionSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FixedSource

public import CFSG.Quasithin.Chapter2.Section04.Source

public import Theory.PGroupCore
public import Mathlib.GroupTheory.Sylow
public import CFSG.Quasithin.Chapter2.Section04.CoreNormalizers
public import CFSG.Quasithin.Chapter2.Section04.BlockResidual
public import CFSG.Quasithin.Chapter2.Section04.ConjugateEscape
public import CFSG.Quasithin.Chapter2.Section04.Statement
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.JointHallSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.SourceCoordinates

/-!
# The case where `Γₑ₀` is nonempty: core normalizers

This file records the elementary finite-group transport used at the start of
Aschbacher--Smith, §2.4, and reexports the source core-normalizer and maximality
arguments of Lemmas 2.4.3–4. It also constructs the selected minimal
parabolic and its literal block closure and proves all of 2.4.5(1),(2),(4),
including the core factorization and maximum elementary conclusion. Every C.5
block marking is constructed from the original hypotheses. The nonsolvable
2.4.6 branch uses the complete A/C/C.1.29 source proofs; the cubic residual
and its direct-product core retain the actual subgroup factors. The single
linear-block branch also constructs the original nontrivial cyclic Hall
torus in the literal Borel intersection M∩L. The linear-shadow descendants prove the local fixed-point, splitting,
rank and transfer implications; SmallBlocks discharges the three excluded
small models; DoubleA3 proves the corrected terminal quotient count from
the actual earlier centralizer and fusion geometry. Full source shadow
classification and its earlier-input discharge remain separate.
In the source, `Q = O₂(H)` and a Sylow 2-subgroup
`S` of `H` are fixed.  The arguments in Lemmas 2.4.3--2.4.4 repeatedly use
the general facts that a normal `p`-subgroup is contained in every Sylow
`p`-subgroup and that a normal subgroup is normalized by the whole group.
The statements here are parameterized by `p` so they can also be reused by
the later local arguments.
-/

@[expose] public section

open Subgroup

namespace CFSG.Quasithin.Chapter2

/-- The `p`-core is contained in every Sylow `p`-subgroup.

This is the precise Sylow fact used for `Q = O₂(H)` in source Lemma 2.4.3.
-/
public theorem pCore_le_sylow
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (S : Sylow p G) :
    pCore p G ≤ (S : Subgroup G) := by
  exact pCore_isPGroup.le_sylow_of_normal S

/-- A normal `p`-subgroup lies in every Sylow `p`-subgroup.

The normality hypothesis is an explicit argument rather than a typeclass so
that this lemma applies directly to a named local subgroup such as `O₂(H)`.
-/
public theorem normal_pSubgroup_le_sylow
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    {Q : Subgroup G} (hQ : Q.Normal) (hQp : IsPGroup p Q)
    (S : Sylow p G) : Q ≤ (S : Subgroup G) := by
  have hQcore : Q ≤ pCore p G := le_sSup ⟨hQ, hQp⟩
  exact hQcore.trans (pCore_le_sylow S)

/-- The `p`-core is the whole group exactly when the whole group is a
`p`-group.  This is useful for pruning the degenerate `O₂(H) = H` branch in
the source's minimal-counterexample arguments. -/
public theorem pCore_eq_top_iff_isPGroup
    {G : Type*} [Group G]
    {p : ℕ} [Fact p.Prime] :
    pCore p G = (⊤ : Subgroup G) ↔ IsPGroup p (⊤ : Subgroup G) := by
  constructor
  · intro h
    rw [← h]
    exact pCore_isPGroup
  · intro h
    apply top_unique
    exact le_sSup ⟨inferInstance, h⟩

/-- A normal subgroup is normalized by the ambient group.

This is the normalizer interface used when passing from `H` to
`G_Q = N_G(Q)` in source Lemma 2.4.3.
-/
public theorem le_normalizer_of_normal
    {G : Type*} [Group G] {Q : Subgroup G} (hQ : Q.Normal) :
    (⊤ : Subgroup G) ≤ Subgroup.normalizer (Q : Set G) := by
  rw [Subgroup.normalizer_eq_top_iff.mpr hQ]

/-- In particular every Sylow subgroup normalizes a normal `p`-subgroup. -/
public theorem sylow_le_normalizer_of_normal
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    {Q : Subgroup G} (hQ : Q.Normal) (S : Sylow p G) :
    (S : Subgroup G) ≤ Subgroup.normalizer (Q : Set G) := by
  rw [Subgroup.normalizer_eq_top_iff.mpr hQ]
  exact le_top

/-- A Sylow subgroup remains Sylow after restricting to an overgroup. -/
public def sylow_subtype_of_le
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    {N : Subgroup G} (S : Sylow p G) (hS : (S : Subgroup G) ≤ N) :
    Sylow p N :=
  S.subtype hS

/-- If `Q` is normal, the Sylow subgroup containing its `p`-core is a Sylow
subgroup of the corresponding normalizer.  This is the abstract form of the
`S ∈ Sylow (G_Q)` assertion in source Lemma 2.4.3(1). -/
public def pCore_sylow_in_normalizer
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (Q : Subgroup G) (hQ : Q.Normal) (S : Sylow p G) :
    Sylow p (Subgroup.normalizer (Q : Set G)) := by
  exact sylow_subtype_of_le S (sylow_le_normalizer_of_normal hQ S)

end CFSG.Quasithin.Chapter2
