module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIdentificationSetup
public import Theory.SpecificGroups.Lyons.Atlas111LocalPresentationSetup
public import Theory.AtlasPort.LinearGroups.G2.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Presentation route to identifying the Lyons local subgroup

The first local generator is a conjugate of the nonidentity ambient generator,
so any homomorphism onto the specified matrix pair is nontrivial. For a simple
source this proves faithfulness. The universal property of the explicit
22-relator presentation therefore reduces identification to two independent
certificates: its equivalence with the octonion G₂(5), and its relations on the
111-dimensional pair. Simplicity is a further explicit input, supplied by the
independent G₂ theory. No unconditional identification is asserted here.

Source of the local words: R. A. Wilson et al., ATLAS of Finite Group
Representations, https://brauer.maths.qmul.ac.uk/Atlas/v3/subgroup/LyG1-max1W1 .
See `Atlas111OrderSource/` and `G2Five/AtlasPresentationSource/` for original data.
-/

namespace Lyons.OrderCertificate

public instance identificationFivePrime : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Noncommutativity of the ambient generators implies this one is nonidentity. -/
public theorem generatorA_ne_one : generatorA ≠ 1 := by
  intro h
  apply generators_not_commute
  rw [h, one_mul, mul_one]

/-- The first local generator is a conjugate of the nonidentity ambient generator. -/
public theorem localA_ne_one : localA ≠ 1 := by
  intro h
  apply generatorA_ne_one
  rw [localA, max1Program_fst] at h
  have hh := mul_inv_eq_one.mp h
  exact mul_left_cancel (hh.trans (mul_one _).symm)

/-- Nontriviality persists on removing the ambient-group subtype. -/
public theorem localMatrixA_ne_one : (max1Program atlasA atlasB).1 ≠ 1 := by
  intro h
  apply localA_ne_one
  apply ambientUnitsHom_injective
  change ambientUnitsHom (max1Program generatorA generatorB).1 = ambientUnitsHom 1
  have hm := congrArg Prod.fst (max1Program_map ambientUnitsHom generatorA generatorB)
  exact hm.trans (h.trans (map_one ambientUnitsHom).symm)

/-- A simple group with the specified generating images is the concrete local group. -/
public noncomputable def localSubgroupEquivOfSimpleImage
    {G : Type*} [Group G] [IsSimpleGroup G]
    (f : G →* AtlasMatrixˣ) (u v : G)
    (hgen : Subgroup.closure ({u, v} : Set G) = ⊤)
    (hu : f u = (max1Program atlasA atlasB).1)
    (hv : f v = (max1Program atlasA atlasB).2) : localSubgroup ≃* G := by
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    rcases f.normal_ker.eq_bot_or_eq_top with hbot | htop
    · exact hbot
    · have htrivial : f = 1 := MonoidHom.ker_eq_top_iff.mp htop
      exact False.elim (localMatrixA_ne_one (hu.symm.trans (by simp [htrivial])))
  exact localSubgroupEquivOfMatrixRange f hf
    (range_eq_localMatrixSubgroup f u v hgen hu hv)

/-- Assemble the identification from a proved presentation and its matrix relations. -/
public noncomputable def localSubgroupG2EquivOfPresentation
    [IsSimpleGroup (Atlas.G2.Model (ZMod 5))]
    (e : G2Five.AtlasPresentation.Model ≃* Atlas.G2.Model (ZMod 5))
    (hrel : LocalPresentationRelations) : localSubgroup ≃* Atlas.G2.Model (ZMod 5) := by
  letI : IsSimpleGroup G2Five.AtlasPresentation.Model := e.isSimpleGroup
  exact (localSubgroupEquivOfSimpleImage
    (G2Five.AtlasPresentation.hom localMatrixAssignment hrel)
    (G2Five.AtlasPresentation.generator false) (G2Five.AtlasPresentation.generator true)
    G2Five.AtlasPresentation.closure_generators
    (G2Five.AtlasPresentation.hom_generator _ _ false)
    (G2Five.AtlasPresentation.hom_generator _ _ true)).trans e

end Lyons.OrderCertificate
