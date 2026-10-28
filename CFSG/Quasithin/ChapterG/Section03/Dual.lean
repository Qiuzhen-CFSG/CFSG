module

public import CFSG.Quasithin.ChapterG.Section03.TwoCore
public import Theory.Representation.BinaryTransvectionGroups.Duality

/-!
# The dual G.3 source-use theorem

A nonzero binary form denotes its hyperplane kernel; the lower-layer duality
lemmas prove both uniqueness of this description and equivariance of the axes.
`AxisHypotheses` uses the original acting group and the images of its actual
axis radicals in its intrinsic two-core quotient. The contragredient group
isomorphism carries these images to the center-root quotient images, preserving
rank. It also carries the intrinsic two-core to that of the dual action image.
We can therefore apply the proved center version and obtain every decomposition,
full-action, elementary-kernel and local-rank conclusion on the dual module.

The extra trivial-two-core premise remains explicit on the original faithful
acting group. No irreducibility or semisimplicity is assumed, and the conclusion
is not the unrestricted printed G.3.1. Consumers own discharge of this premise.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004, G.3.1,
printed pp.337--338; dual applications G.10.4 and 12.2.20.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterG.Section03
open BinaryTransvectionGroups
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The image of the original axis group in the original group's intrinsic quotient. -/
def axisRootQuotientImage (G : Subgroup (BinaryLinear.GL V)) (f : DualSpace V) :
    Subgroup (G ⧸ pCore 2 G) :=
  ((axisRootGroup G f).subgroupOf G).map (QuotientGroup.mk' (pCore 2 G))

/-- The induced isomorphism between the actual two-core quotients. -/
noncomputable def dualCoreQuotientEquiv (G : Subgroup (BinaryLinear.GL V)) :
    (G ⧸ pCore 2 G) ≃* (dualGroup G ⧸ pCore 2 (dualGroup G)) :=
  QuotientGroup.congr _ _ (dualGroupEquiv G) (dualGroup_pCore G 2)

theorem axisRoot_subgroupOf_map (G : Subgroup (BinaryLinear.GL V)) (f : DualSpace V) :
    ((axisRootGroup G f).subgroupOf G).map (dualGroupEquiv G).toMonoidHom =
      (rootGroup (dualGroup G) f).subgroupOf (dualGroup G) := by
  ext t
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (contragredient_mem_axisRoot_iff G f g.val).mpr hg
  · intro ht
    obtain ⟨g, rfl⟩ := (dualGroupEquiv G).surjective t
    exact ⟨g, (contragredient_mem_axisRoot_iff G f g.val).mp ht, rfl⟩

/-- Quotient-rank transport uses the isomorphism induced by the same action. -/
theorem axisRootQuotientImage_map (G : Subgroup (BinaryLinear.GL V)) (f : DualSpace V) :
    (axisRootQuotientImage G f).map (dualCoreQuotientEquiv G).toMonoidHom =
      rootQuotientImage (dualGroup G) f := by
  have he : (dualCoreQuotientEquiv G).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G)) =
      (QuotientGroup.mk' (pCore 2 (dualGroup G))).comp (dualGroupEquiv G).toMonoidHom := by
    ext g
    rfl
  rw [axisRootQuotientImage, Subgroup.map_map, he, ← Subgroup.map_map,
    axisRoot_subgroupOf_map]
  rfl

theorem axisRootQuotientImage_rank (G : Subgroup (BinaryLinear.GL V)) [Finite G]
    (f : DualSpace V) :
    Group.rank (axisRootQuotientImage G f) = Group.rank (rootQuotientImage (dualGroup G) f) := by
  let e := (axisRootQuotientImage G f).equivMapOfInjective
    (dualCoreQuotientEquiv G).toMonoidHom (dualCoreQuotientEquiv G).injective
  exact (Group.rank_congr e).trans (Subgroup.rank_congr (axisRootQuotientImage_map G f))

/-- Genuine axis inputs, indexed by the unique nonzero binary forms defining
those hyperplanes. The orbit uses the original acting group; the rank uses
its original axis groups and intrinsic two-core quotient. -/
structure AxisHypotheses (G : Subgroup (BinaryLinear.GL V)) [Finite G]
    (Γ : Set (DualSpace V)) : Prop where
  nonzero : ∀ f ∈ Γ, f ≠ 0
  orbit : ∃ f : DualSpace V, Γ = {l | ∃ g : G, contragredient g.val f = l}
  rank_gt_one : ∀ f ∈ Γ, 1 < Group.rank (axisRootQuotientImage G f)

/-- The original axis hypotheses imply the center hypotheses for the actual
contragredient image, with no extra recognition premise. -/
theorem AxisHypotheses.dual {G : Subgroup (BinaryLinear.GL V)} [Finite G]
    {Γ : Set (DualSpace V)} (h : AxisHypotheses G Γ) : Hypotheses (dualGroup G) Γ := by
  refine ⟨h.nonzero, ?_, ?_⟩
  · obtain ⟨f, hf⟩ := h.orbit
    refine ⟨f, ?_⟩
    rw [hf]
    ext l
    constructor
    · rintro ⟨g, rfl⟩
      exact MulAction.mem_orbit_iff.mpr ⟨dualGroupEquiv G g, rfl⟩
    · intro hl
      obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hl
      obtain ⟨g, rfl⟩ := (dualGroupEquiv G).surjective g
      exact ⟨g, rfl⟩
  · intro f hf
    rw [← axisRootQuotientImage_rank]
    exact h.rank_gt_one f hf

/-- The dual source-use theorem: all decomposition and rank conclusions on the
actual dual module, with the extra two-core premise imposed on the original
faithful acting group. The kernel, core, radical and quotient-rank transports
have all been proved above. -/
theorem dual_source_conclusions_of_twoCore_eq_bot
    {G : Subgroup (BinaryLinear.GL V)} [Finite G] {Γ : Set (DualSpace V)}
    (h : AxisHypotheses G Γ) (hcore : pCore 2 G = ⊥) :
    FullAction (dualGroup G) Γ ∧ Decomposition (dualGroup G) Γ ∧
      LocalStructure (dualGroup G) Γ :=
  source_conclusions_of_twoCore_eq_bot h.dual (dualGroup_twoCore_eq_bot hcore)

end CFSG.Quasithin.ChapterG.Section03
