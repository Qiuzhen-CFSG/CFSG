module

public import Stellmacher.SectionEight.GeneratedContext
public import Stellmacher.SectionEight.EightTwoDistanceOneElementaryCores
public import Stellmacher.SectionEight.EightTwoDistanceOneCoreStructure
public import Stellmacher.SectionEight.EightTwoDistanceOneInvolutions
public import Stellmacher.SectionEight.EightTwoPropagation
public import Theory.GroupTheory.ElementaryCoreSymmetricFour

/-!
# Whole-stabilizer classification at critical distance one

In the noncentral first-step case of Stellmacher (8.2), critical distance
one implies that every vertex stabilizer is S4 or C2 times S4. The local
version uses the ambient-retaining Section Eight context, and the legacy
version preserves the original SectionEightContext interface through its
definitionally graph-preserving adapter. Critical distance one is an
explicit hypothesis, not a conclusion of this module.

The elementary-core theorem first makes both distinguished two-cores
elementary abelian. The structural theorem decomposes each actual core
as a normal order-four subgroup times its stabilizer's center, with
trivial intersection, center order at most two, and actual core quotient
S3. Characteristic two gives self-centralization. Criticality supplies
an involution outside each core, retaining the splitting input needed
to exclude the nonsplit extension admitted by weaker local data. The
elementary-core classifier therefore identifies both whole stabilizers;
critical-edge propagation transports these models to all vertices.

Source: Stellmacher (8.2), final paragraph, Journal of Algebra 190 (1997),
printed p.38, `refs/latex/stellmacher-n-group.tex`. The imported structural
proofs work directly on the distinguished edge rather than assuming a
transfer from the source's backward edge. No faithful center-action
quotient is silently substituted for the actual core quotient.
-/

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven

universe u

public theorem eight_two_models_of_distance_one_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlength : ctx.criticalPath.length = 1) :
    ∀ d : ctx.Γ.Vertex,
      IsModel (GAt ctx.Γ d) S4 ∨ IsModel (GAt ctx.Γ d) (C2 × S4) := by
  have helementary := eight_two_distance_one_elementary_cores_local ctx hcenter hlength
  have hstructure := eight_two_distance_one_core_structure_local ctx hcenter hlength helementary
  have hcharacteristic := SevenSix.edge_characteristic_data
    ctx.sectionSeven ctx.Γ ctx.criticalPath
  have hedge (d : ctx.Γ.Vertex)
      (hd : d = ctx.criticalPath.a ∨ d = ctx.criticalPath.firstStep) :
      IsModel (GAt ctx.Γ d) S4 ∨ IsModel (GAt ctx.Γ d) (C2 × S4) := by
    let _ := helementary d hd
    obtain ⟨U, hnormal, hQ, hUZ, hUcard, hZcard, hquot⟩ := hstructure d hd
    let _ := hnormal
    have hcent : Subgroup.centralizer (pCore 2 (GAt ctx.Γ d) : Set (GAt ctx.Γ d)) ≤
        pCore 2 (GAt ctx.Γ d) := by
      rcases hd with rfl | rfl
      · exact hcharacteristic.1
      · exact hcharacteristic.2
    exact elementary_core_symmetric_four_or_c2_product
      (pCore 2 (GAt ctx.Γ d)) U hcent hQ hUZ hUcard hZcard hquot
      (eight_two_distance_one_edge_involutions_local ctx hlength d hd)
  exact eight_two_models_of_critical_edge_local ctx
    (hedge _ (Or.inl rfl)) (hedge _ (Or.inr rfl))

public theorem eight_two_models_of_distance_one
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlength : ctx.criticalPath.length = 1) :
    ∀ d : ctx.Γ.Vertex,
      IsModel (GAt ctx.Γ d) S4 ∨ IsModel (GAt ctx.Γ d) (C2 × S4) :=
  eight_two_models_of_distance_one_local ctx.toLocalContext hcenter hlength

end Stellmacher.SectionEight
