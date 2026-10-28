module

public import CFSG.Quasithin.ChapterC.Section01.DoubledNaturalControl.SourceReduction.MSConstruction
public import Theory.Representation.PSL3Two.SmallModules

/-!
# Geometric interfaces and the marked reduction output

The offender reduction must produce `OffenderData`, or the literal
characteristic obstruction in K. Its plane marking is conjugation in the
specified SL₃(2), acting on the specified natural module; it does not use
graph duality. Independently, the plane action must supply `BaumannFamily`,
including all of B.2.18(a)--(d), the codimension sum, and J(R) containment.

`ReductionData` records the exact output consumed by doubled-natural core
control. `reduction_of_geometry` constructs it from these two geometric
outputs. The unconditional `SourceData.reduce` in the parent module discharges
these inputs using `Offenders` and `BaumannFamily`.

Source: Aschbacher--Smith, C.1.37, printed pp.141--143, especially the
three-conjugate argument on p.143, and B.2.18, printed pp.80--81.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterC.DoubledNaturalControl.SourceReduction
open Subgroup Theory.GroupTheory Stellmacher
universe u
variable {K : Type u} [Group K] [Finite K]
  {κ : GroupClass.{u}} {L P U : Subgroup K} [L.Normal] [U.Normal]
  {T : Sylow 2 K} (d : SourceData κ L P U T)

/-- Output of the maximum-elementary comparison. The plane radical consists
of the literal shears fixing v₂=0 in the original natural coordinates. -/
structure OffenderData : Prop where
  thompson_image : (elementaryAbelianMaxJ (R P)).map d.ρK = (R P).map d.ρK
  plane_radical : ∃ g : SL,
    (R P).map d.ρK = BinaryLinearThree.R.map (MulAut.conj g).toMonoidHom

/-- Output of the three-conjugate construction, including every quantitative
Baumann premise, not only a generating-family tag. -/
structure BaumannFamily (d : SourceData κ L P U T) where
  X : Fin 3 → Subgroup K
  hypotheses : ChapterB.BaumannArgument.HypothesesAD U (R P) X
  thompson_le : elementaryAbelianMaxJ (R P) ≤ ⨆ i, X i

/-- The marked MS reduction output. None of these fields are added to the
source input. The two local maps are always inclusions into the literal J. -/
structure ReductionData where
  group_normal : (J L P).Normal
  ms : BinaryMS.Input κ (LJ L P) (BJ L P)
  core_eq_comap : pCore 2 (J L P) = (pCore 2 K).comap (J L P).subtype
  projection_surjective : Function.Surjective d.ρJ
  projection_kernel : d.ρJ.ker = pCore 2 (J L P)
  quotient_compatible : ∀ l : LJ L P,
    ms.quotientEquiv (QuotientGroup.mk' (pCore 2 (LJ L P)) l) =
      d.eL (QuotientGroup.mk' (pCore 2 L) (SourceData.eLJ l))
  component_projection : ∀ l : LJ L P,
    ms.quotientEquiv (QuotientGroup.mk' (pCore 2 (LJ L P)) l) = d.ρJ (l : J L P)
  source_module_le : U ≤ J L P
  module_map : (UJ L P U).map (J L P).subtype = U
  module_normal : (UJ L P U).Normal
  module_elementary : IsElementaryAbelian 2 (UJ L P U)
  module_le_core : UJ L P U ≤ pCore 2 (J L P)
  module_commutator : ⁅UJ L P U, LJ L P⁆ = UJ L P U
  module_fixed : UJ L P U ⊓ centralizer (LJ L P : Set (J L P)) = ⊥
  module_card : Nat.card (UJ L P U) = 64
  module_centralizes_core : UJ L P U ≤ centralizer (pCore 2 (J L P) : Set (J L P))
  module_action : letI := module_normal
    ∀ j u, Multiplicative.toAdd (d.eDouble (MulAut.conjNormal j u)) =
      fun i => Matrix.mulVec (d.ρJ j).val (Multiplicative.toAdd (d.eDouble u) i)
  parabolic_proper : HJ L P < ⊤
  parabolic_odd : Odd (HJ L P).index
  parabolic_radical : (pCore 2 (HJ L P)).map (HJ L P).subtype = BJ L P

namespace SourceData

omit [Finite K] in
/-- J(R) ≤ B ≤ R turns the Thompson-image equality into the Baumann-image
equality used by the local radical computation. -/
theorem baumann_image (h : OffenderData d) : (B P).map d.ρK = (R P).map d.ρK := by
  apply le_antisymm (map_mono inf_le_left)
  rw [← h.thompson_image]
  apply map_mono
  refine le_inf (sSup_le fun _ hA => hA.1) ?_
  intro j hj
  apply mem_centralizer_iff.mpr
  intro z hz
  obtain ⟨zJ, hzJ, rfl⟩ := hz
  obtain ⟨zC, _, rfl⟩ := hzJ
  exact congrArg Subtype.val ((mem_center_iff.mp zC.property) ⟨j, hj⟩).symm

/-- Conditional assembly of the exact output. The unconditional reduction
supplies both geometric inputs using their separate proved producers. -/
noncomputable def reduction_of_geometry (hno : ¬ CharacteristicObstruction P)
    (ho : OffenderData d) (hf : BaumannFamily d) : ReductionData d where
  group_normal := d.group_normal
  ms := d.msInput hno (d.baumann_image ho) hf.X hf.hypotheses hf.thompson_le
  core_eq_comap := d.core_eq_comap
  projection_surjective := d.projection_surjective
  projection_kernel := d.projection_kernel
  quotient_compatible := d.componentEquiv_apply
  component_projection := d.component_projection
  source_module_le := d.source_module_le
  module_map := d.module_map
  module_normal := inferInstance
  module_elementary := d.module_elementary
  module_le_core := d.module_le_core
  module_commutator := d.module_commutator
  module_fixed := d.module_fixed
  module_card := d.module_card
  module_centralizes_core := d.module_centralizes_core
  module_action := d.module_action
  parabolic_proper := d.parabolic_proper
  parabolic_odd := d.parabolic_odd
  parabolic_radical := d.parabolic_radical (d.baumann_image ho)
    (d.core_le_baumann_of_family hf.X hf.hypotheses hf.thompson_le)

end SourceData
end CFSG.Quasithin.ChapterC.DoubledNaturalControl.SourceReduction
