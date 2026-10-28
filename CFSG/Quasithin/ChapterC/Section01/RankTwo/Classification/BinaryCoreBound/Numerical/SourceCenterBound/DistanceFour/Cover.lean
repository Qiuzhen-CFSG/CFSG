module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.Numerical.SourceCenterBound.DistanceFour.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Kernel.Fixed.Displacement.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.FixedKernel.DoubleCopy.CoverRigidity.Models

/-!
# The actual core quotient as a cover of two natural modules

Restrict the constructed starred quotient to the core and descend it through
the constructed quotient by U_alpha. Both actions use the literal source
projection. Precomposing by the inverse of graph composed with the supplied
marking turns the two dual summands into the precise natural representation
used by the cover theorem.

The proved invariant-preimage equality makes the covering kernel fixed,
and core commutator generation makes the cover full. The universal-cover
bound then gives dimension at most eight for core/U_alpha.

Source: Meierfrankenfeld--Stellmacher (1993), (1.4)--(1.5), p.842, and
(4.6.12), pp.910--912; the cover bound uses the binary natural first
cohomology calculation already formalized in CoverRigidity.Models.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterC.BinaryMS.Numerical.SourceCenterBound.DistanceFour

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender Representation.OneCohomology Module
open MS93 MS93.DistanceFour
open scoped IsMulCommutative commutatorElement

private theorem restriction_surjective {A T : Type*} [Group A] [Group T]
    {star central coreSubgroup : Subgroup A} (hCS : coreSubgroup ≤ star) (f : star →* T)
    (hf : Function.Surjective f) (hker : f.ker = central.subgroupOf star)
    (hSC : star = central ⊔ coreSubgroup) :
    Function.Surjective (f.comp (inclusion hCS)) := by
  apply MonoidHom.range_eq_top.mp
  have hZS : central ≤ star := by rw [hSC]; exact le_sup_left
  have hgen : central.subgroupOf star ⊔ coreSubgroup.subgroupOf star = ⊤ := by
    rw [← subgroupOf_sup hZS hCS, ← hSC, subgroupOf_self]
  have h := congrArg (Subgroup.map f) hgen
  rw [Subgroup.map_sup, ← hker, Subgroup.map_ker_self,
    bot_sup_eq, map_top_of_surjective _ hf] at h
  rw [MonoidHom.range_comp, inclusion_range]
  exact h

universe u
variable {M : Type u} [Group M] [Finite M] {L R : Subgroup M}
  (source : LocalSource L R) {geometry : Geometry R}
  (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)

local notation "C" => core R (alpha R)
local notation "S" => VStar R geometry (alpha R) (beta R)
local notation "Z" => Z R (alpha R)
local notation "U" => U R (alpha R)

variable (q : LargeBranch.StarDoubleQuotient source common)
  (hSC : VStar R geometry (alpha R) (beta R) =
    CFSG.Quasithin.ChapterC.BinaryMS.MS93.Z R (alpha R) ⊔ core R (alpha R))
  (d : SmallBranch.QuotientAction source)

/-- Restriction of the actual starred quotient to the actual core. -/
noncomputable def coreProjection : C →* Multiplicative (Linear.W × Linear.W) :=
  q.quotient.comp (inclusion
    (SmallBranch.core_le_star source geometry common radius (alpha R) (beta R)
      rfl (base_adjacent R)))

theorem coreProjection_kernel :
    (coreProjection source common radius q).ker = (Z).subgroupOf C := by
  ext x
  change inclusion _ x ∈ q.quotient.ker ↔ _
  rw [q.kernel]
  rfl

include hSC in
theorem coreProjection_onto : Function.Surjective (coreProjection source common radius q) := by
  change Function.Surjective (q.quotient.comp (inclusion
    (SmallBranch.core_le_star source geometry common radius (alpha R) (beta R)
      rfl (base_adjacent R))))
  exact @restriction_surjective (FreeAmalgam R)
    (Multiplicative (Linear.W × Linear.W)) inferInstance inferInstance S Z C
    (SmallBranch.core_le_star source geometry common radius (alpha R) (beta R)
      rfl (base_adjacent R)) q.quotient q.onto q.kernel hSC

theorem coreProjection_action (m : M) (x y : C)
    (hy : (y : FreeAmalgam R) = embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹) :
    (coreProjection source common radius q y).toAdd =
      (Linear.dual (common.natural.marking (source.projection m))
        (coreProjection source common radius q x).toAdd.1,
       Linear.dual (common.natural.marking (source.projection m))
        (coreProjection source common radius q x).toAdd.2) :=
  q.action m _ _ hy

theorem quotient_kernel_le :
    d.projection.ker ≤ (coreProjection source common radius q).ker := by
  rw [d.kernel, coreProjection_kernel]
  exact comap_mono (MS93.DistanceEight.U_le_Z R (alpha R))

/-- The unique descended map through the already constructed core/U quotient. -/
noncomputable def descendedHom : Multiplicative d.Space →* Multiplicative (Linear.W × Linear.W) :=
  d.projection.liftOfSurjective d.onto
    ⟨coreProjection source common radius q, quotient_kernel_le source common radius q d⟩

theorem descendedHom_apply (x : C) :
    descendedHom source common radius q d (d.projection x) =
      coreProjection source common radius q x :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

noncomputable def descendedAddHom : d.Space →+ (Linear.W × Linear.W) where
  toFun v := (descendedHom source common radius q d (Multiplicative.ofAdd v)).toAdd
  map_zero' := congrArg Multiplicative.toAdd (map_one (descendedHom source common radius q d))
  map_add' x y := congrArg Multiplicative.toAdd
    (map_mul (descendedHom source common radius q d)
      (Multiplicative.ofAdd x) (Multiplicative.ofAdd y))

noncomputable def descendedLinear : d.Space →ₗ[ZMod 2] (Linear.W × Linear.W) :=
  { descendedAddHom source common radius q d with
    map_smul' := ZMod.map_smul (descendedAddHom source common radius q d) }

theorem descendedLinear_apply (x : C) :
    descendedLinear source common radius q d (d.projection x).toAdd =
      (coreProjection source common radius q x).toAdd :=
  congrArg Multiplicative.toAdd (descendedHom_apply source common radius q d x)

include hSC in
theorem descendedLinear_onto : Function.Surjective (descendedLinear source common radius q d) := by
  intro v
  obtain ⟨x, hx⟩ := coreProjection_onto source common radius q hSC (Multiplicative.ofAdd v)
  exact ⟨(d.projection x).toAdd, (descendedLinear_apply source common radius q d x).trans
    (congrArg Multiplicative.toAdd hx)⟩

theorem descendedLinear_action (g : SL) (v : d.Space) :
    descendedLinear source common radius q d (d.representation g v) =
      (Linear.dual (common.natural.marking g) (descendedLinear source common radius q d v).1,
       Linear.dual (common.natural.marking g) (descendedLinear source common radius q d v).2) := by
  obtain ⟨m, rfl⟩ := source.projection_surjective g
  obtain ⟨x, hx⟩ := d.onto (Multiplicative.ofAdd v)
  have hv : (d.projection x).toAdd = v := congrArg Multiplicative.toAdd hx
  rw [← hv, ← d.action m x (coreAction (R := R) m x) rfl, descendedLinear_apply,
    descendedLinear_apply]
  exact coreProjection_action source common radius q m x (coreAction (R := R) m x) rfl

/-- The literal graph automorphism composed with the supplied source marking. -/
noncomputable def markingTwist : SL ≃* SL :=
  common.natural.marking.trans BinaryLinearThree.AutomorphismAction.graph

noncomputable def twistedRepresentation : Representation (ZMod 2) SL d.Space :=
  d.representation.comp (markingTwist source common).symm.toMonoidHom

/-- The descended map becomes natural on both coordinates under this exact twist. -/
noncomputable def pairNaturalMap :
    (twistedRepresentation source common d).IntertwiningMap
      (AbelianCore.DoubleCopy.CoverModels.base.prod AbelianCore.DoubleCopy.CoverModels.base) where
  toLinearMap := descendedLinear source common radius q d
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    change descendedLinear source common radius q d
      (d.representation ((markingTwist source common).symm g) v) =
      (g.val.mulVec (descendedLinear source common radius q d v).1,
       g.val.mulVec (descendedLinear source common radius q d v).2)
    rw [descendedLinear_action]
    have he : BinaryLinearThree.AutomorphismAction.graph
        (common.natural.marking ((markingTwist source common).symm g)) = g :=
      (markingTwist source common).apply_symm_apply g
    have hw (w : Linear.W) :
        Linear.dual (common.natural.marking ((markingTwist source common).symm g)) w =
          g.val.mulVec w := by
      change (BinaryLinearThree.AutomorphismAction.graph
        (common.natural.marking ((markingTwist source common).symm g))).val.mulVec w = _
      rw [he]
    exact Prod.ext (hw _) (hw _)

/-- The final map uses the exact function-space convention of the cover theorem. -/
noncomputable def coverMap :
    (twistedRepresentation source common d).IntertwiningMap AbelianCore.DoubleCopy.natural :=
  AbelianCore.DoubleCopy.CoverModels.pairEquiv.symm.toIntertwiningMap.comp
    (pairNaturalMap source common radius q d)

include hSC in
theorem coverMap_isCover : IsCover (coverMap source common radius q d) := by
  refine ⟨?_, ?_, ?_⟩
  · exact AbelianCore.DoubleCopy.CoverModels.pairEquiv.symm.surjective.comp
      (descendedLinear_onto source common radius q hSC d)
  · intro v hv
    have hz : descendedLinear source common radius q d v = 0 := by
      apply AbelianCore.DoubleCopy.CoverModels.pairEquiv.symm.injective
      exact hv.trans (map_zero _).symm
    obtain ⟨x, hx⟩ := d.onto (Multiplicative.ofAdd v)
    have hq : coreProjection source common radius q x = 1 := by
      apply Multiplicative.toAdd.injective
      rw [← descendedLinear_apply, hx]
      exact hz
    have hxZ : (x : FreeAmalgam R) ∈ Z := by
      change x ∈ (Z).subgroupOf C
      rw [← coreProjection_kernel source common radius q]
      exact hq
    have hfix : x ∈ ((fixedSpace d.representation ⊤).toAddSubgroup.toSubgroup).comap
        d.projection := by
      rw [LargeBranch.RankOne.Fixed.Displacement.invariant_preimage_eq
        source common d radius]
      exact hxZ
    have hvfix : v ∈ fixedSpace d.representation ⊤ := by
      change (d.projection x).toAdd ∈ fixedSpace d.representation ⊤ at hfix
      have hv : (d.projection x).toAdd = v := congrArg Multiplicative.toAdd hx
      exact hv ▸ hfix
    intro g
    exact hvfix ⟨(markingTwist source common).symm g, mem_top _⟩
  · have hle : subspaceCommutator d.representation ⊤ ⊤ ≤
        Coinvariants.ker (twistedRepresentation source common d) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨g, _, v, _, rfl⟩
      have h := Coinvariants.sub_mem_ker
        (ρ := twistedRepresentation source common d) (markingTwist source common g) v
      change d.representation ((markingTwist source common).symm
        (markingTwist source common g)) v - v ∈
          Coinvariants.ker (twistedRepresentation source common d) at h
      rwa [(markingTwist source common).symm_apply_apply] at h
    rw [d.full] at hle
    exact top_unique hle

include q hSC radius in
theorem quotient_dimension_le_eight : Module.finrank (ZMod 2) d.Space ≤ 8 := by
  let _ : Module.Finite (ZMod 2) d.Space := Module.Finite.of_finite
  let p := coverMap source common radius q d
  have hp := coverMap_isCover source common radius q hSC d
  have hk := AbelianCore.DoubleCopy.CoverModels.cover_kernel_finrank_le_two p hp
  have hd := p.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hp.1, finrank_top,
    AbelianCore.DoubleCopy.CoverModels.finrank_natural] at hd
  omega

end CFSG.Quasithin.ChapterC.BinaryMS.Numerical.SourceCenterBound.DistanceFour
