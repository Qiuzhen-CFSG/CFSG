module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Critical
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.CriticalPairs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.CommonFacts
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Tree
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Realization
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.LocalStructure
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.NormalizerTransfer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Factorization

/-!
# Actual local geometry for the binary MS93 setup

The constructor realizes `LocalSource` and `Geometry` from a genuine input
with nontrivial commutator core. It uses the native characteristic replacement,
the two actual parabolic preimages, and the infinite free holomorph amalgam.
The quotient marking and the original component and core are compared through
the specified embeddings. No odd-index radical condition is asserted for the
replacement. `CommonFacts` remains the separate basic-reduction obligation.
The normalization and factorization lemmas 2.1(vi)--(vii) and 2.2(iv)--(vi)
are exported here with their literal source premises: positive critical
distance, the edge-centralizer identity for 2.2, and universal escape for
2.2(v). Deriving those premises from a nonabelian core belongs to the later
basic reduction; they are not assumed by this constructor.

Source: Meierfrankenfeld--Stellmacher (1993), Sections 2--4.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93

open Subgroup Stellmacher.PushingUp.AmalgamGraph

variable {M : Type*} [Group M] [Finite M] (R : Subgroup M)

/-- Assemble the proved local geometry once acyclicity of the actual free
amalgam graph has been supplied. The extra hypothesis is kept explicit. -/
theorem geometry_of_isTree (hp : IsPGroup 2 R) (hne : R ≠ ⊥)
    (hP : MSCharacteristicCondition R) (htree : (cosetGraph R).IsTree) : Geometry R where
  tree := htree
  exists_critical := criticalRadius_exists_at R hp hne hP
  even := fun a ha => criticalDistance_even R a ha _
  distance_constant := fun a ha => criticalDistance_eq_base R a ha _ _
  centralizes := Z_centralizes_Q R
  omega_bound := fun a ha => Z_le_X_of_positive R a ha _
  Z_normal := Z_normal R
  V_local := fun a ha => V_le_stabilizer_of_two_lt R hp hne hP a ha _


/-- The actual free-amalgam geometry, with the tree theorem discharged. -/
theorem geometry (hp : IsPGroup 2 R) (hne : R ≠ ⊥)
    (hP : MSCharacteristicCondition R) : Geometry R :=
  geometry_of_isTree R hp hne hP (cosetGraph_isTree R)

universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L T : Subgroup J}

/-- A realized replacement, retaining the compatible original quotient.
This contains the setup geometry, not the later common reduction. -/
structure InputSetup (h : Input κ L T) where
  reduction : CharacteristicReduction L T
  source : LocalSource (L.subgroupOf reduction.overgroup) reduction.radical
  projection_eq : source.projection = reduction.projection h
  radical_ne_bot : reduction.radical ≠ ⊥
  geometry : Geometry reduction.radical

/-- Construct the actual reduced source setup from the original input.
Nontriviality suffices here; the later source reduction uses nonabelianness. -/
noncomputable def from_Input (h : Input κ L T) (hD : commutatorCore L ≠ ⊥) :
    InputSetup h :=
  let d := characteristicReduction h
  { reduction := d
    source := d.localSource h
    projection_eq := d.localSource_projection h
    radical_ne_bot := d.radical_ne_bot h hD
    geometry := geometry d.radical (d.radical_two_group h)
      (d.radical_ne_bot h hD) (d.msCharacteristic h) }

/-- In particular the nonabelian-core input has an actual source setup. -/
theorem exists_setup (h : Input κ L T) (hD : ¬ IsMulCommutative (commutatorCore L)) :
    Nonempty (InputSetup h) := by
  refine ⟨from_Input h ?_⟩
  intro he
  apply hD
  rw [he]
  infer_instance

namespace InputSetup
variable {h : Input κ L T} (s : InputSetup h)

/-- Source Q at the distinguished vertex pulls back to the replacement core. -/
theorem Q_pullback :
    (Q s.reduction.radical (alpha s.reduction.radical)).comap (embedM s.reduction.radical) =
      pCore 2 s.reduction.overgroup :=
  Q_alpha_comap _ s.source.two_group s.source.core_le

/-- Source T at the distinguished holomorph vertex is the actual embedded edge group. -/
theorem T_embedded : Q s.reduction.radical (beta s.reduction.radical) =
    s.reduction.radical.map (embedM s.reduction.radical) := Q_beta _

/-- The source local residual is the original component through both inclusions. -/
theorem Ltilde_embedded : Ltilde s.reduction.radical (alpha s.reduction.radical) =
    (L.subgroupOf s.reduction.overgroup).map (embedM s.reduction.radical) := by
  rw [Ltilde_alpha, s.source.residual]

/-- Pulling back through embedM and then including in J recovers exactly D. -/
theorem core_pullback :
    ((core s.reduction.radical (alpha s.reduction.radical)).comap
      (embedM s.reduction.radical)).map s.reduction.overgroup.subtype = commutatorCore L := by
  rw [core_alpha _ s.source.two_group s.source.core_le s.source.residual,
    comap_map_eq_self_of_injective (embedM_injective _)]
  exact s.reduction.commutatorCore_eq h

/-- An actual isomorphism between the amalgam commutator core and the original D. -/
noncomputable def coreEquiv :
    core s.reduction.radical (alpha s.reduction.radical) ≃* commutatorCore L :=
  (MulEquiv.subgroupCongr
    (core_alpha _ s.source.two_group s.source.core_le s.source.residual)).trans
    (((⁅pCore 2 s.reduction.overgroup, L.subgroupOf s.reduction.overgroup⁆).equivMapOfInjective
      (embedM s.reduction.radical) (embedM_injective _)).symm.trans
      (((⁅pCore 2 s.reduction.overgroup, L.subgroupOf s.reduction.overgroup⁆).equivMapOfInjective
        s.reduction.overgroup.subtype s.reduction.overgroup.subtype_injective).trans
          (MulEquiv.subgroupCongr (s.reduction.commutatorCore_eq h))))

/-- The setup's projection has exactly the replacement core as kernel. -/
theorem projection_kernel : s.source.projection.ker = pCore 2 s.reduction.overgroup :=
  s.source.projection_kernel

/-- Compatibility with the specified original component quotient is retained. -/
theorem projection_component (l : L) :
    s.source.projection ⟨l, (show L ≤ s.reduction.overgroup from le_sup_left) l.property⟩ =
      h.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l) := by
  rw [s.projection_eq]
  exact h.coreProjection_component l

end InputSetup

end CFSG.Quasithin.ChapterC.BinaryMS.MS93
