module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.CentralKernel
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.ExtensionControl
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.AbelianSpans.Offender.SelfDualFF.Commutator

/-!
# The actual commutator module and its central attachments

For an arbitrary faithful binary action of the matrix group SL₃(2), the
commutator module is stable, faithful, and commutator-generated. An offender
on the original module remains an offender on this submodule. Its fixed
space is identified with the literal intersection of the ambient fixed and
commutator spaces, without assuming that either central attachment splits.

The stability and perfect-actor argument are reused from `SelfDualFF.Commutator`.
These are the intrinsic reductions for Aschbacher–Smith B.4.8 and B.5.1,
printed pp.91–103, used in MS93 (3.2), printed p.863.
-/

@[expose] public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.CentralAttachments
open AbelianCore.QuotientRecognition
open DistanceFour.Early.Containment.SpanOffender.SelfDualFF

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The literal commutator subrepresentation D = [V,SL₃(2)]. -/
noncomputable abbrev moving (ρ : Representation (ZMod 2) SL V) : Subrepresentation ρ :=
  commutatorSubrepresentation ρ

/-- The actual sum C_V(SL₃(2)) + [V,SL₃(2)]. -/
noncomputable abbrev centralSum (ρ : Representation (ZMod 2) SL V) : Submodule (ZMod 2) V :=
  fixedSpace ρ ⊤ ⊔ (moving ρ).toSubmodule

/-- Natural copies with a single automorphism marking and actual coordinates. -/
structure Copies (ρ : Representation (ZMod 2) SL V) (m : ℕ) where
  marking : SL ≃* SL
  equiv : V ≃ₗ[ZMod 2] (Fin m → Fin 3 → ZMod 2)
  equivariant : ∀ (g : SL) (v : V) (i : Fin m),
    equiv (ρ g v) i = specialLinearNatural 3 (marking g) (equiv v i)

variable (ρ : Representation (ZMod 2) SL V)

/-- The submodule convention agrees with the span of action differences. -/
theorem moving_eq : (moving ρ).toSubmodule = subspaceCommutator ρ ⊤ ⊤ :=
  (fullCommutator_eq ρ).symm

/-- The restricted action on D is fully moving, by perfectness of SL₃(2). -/
theorem moving_full : subspaceCommutator (moving ρ).toRepresentation ⊤ ⊤ = ⊤ := by
  let : Group.IsPerfect SL := Atlas.sl_perfect (F := ZMod 2) 3 (by decide)
  exact commutator_full ρ

private theorem moving_not_fixed (hρ : Function.Injective ρ) :
    ¬ (moving ρ).toSubmodule ≤ fixedSpace ρ ⊤ := by
  let : Group.IsPerfect SL := Atlas.sl_perfect (F := ZMod 2) 3 (by decide)
  let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  intro hc
  have hall := le_fixedSpace_of_commutator_le_fixedSpace ρ ⊤ ⊤
    (le_subspaceStabilizer ρ ⊤ (by simp)) ((moving_eq ρ) ▸ hc)
  obtain ⟨g, hg⟩ := exists_ne (1 : SL)
  apply hg
  apply hρ
  apply LinearMap.ext
  intro v
  have h := hall (show v ∈ (⊤ : Submodule (ZMod 2) V) from Submodule.mem_top)
    ⟨g, Subgroup.mem_top g⟩
  change ρ g v = v at h
  simpa only [map_one, Module.End.one_apply] using h

/-- A faithful SL₃(2)-action is still faithful on its actual commutator module. -/
theorem moving_faithful (hρ : Function.Injective ρ) :
    Function.Injective (moving ρ).toRepresentation := by
  let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  let σ := (moving ρ).toRepresentation
  rcases (inferInstance : σ.ker.Normal).eq_bot_or_eq_top with hb | ht
  · exact σ.ker_eq_bot_iff.mp hb
  · have he : σ = 1 := MonoidHom.ker_eq_top_iff.mp ht
    apply False.elim
    apply moving_not_fixed ρ hρ
    intro v hv g
    have h : σ g ⟨v, hv⟩ = ⟨v, hv⟩ := by rw [he]; rfl
    exact congrArg Subtype.val h

/-- Fixed vectors in D are exactly the ambient intersection C ∩ D. -/
noncomputable def fixedMovingEquiv :
    fixedSpace (moving ρ).toRepresentation ⊤ ≃ₗ[ZMod 2]
      (fixedSpace ρ ⊤ ⊓ (moving ρ).toSubmodule : Submodule (ZMod 2) V) where
  toFun v := ⟨v.val.val, ⟨fun g => congrArg Subtype.val (v.property g), v.val.property⟩⟩
  invFun v := ⟨⟨v.val, v.property.2⟩, fun g => Subtype.ext (v.property.1 g)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Vanishing fixed space in D is literal disjointness of C and D. -/
theorem disjoint_iff_fixedMoving_eq_bot :
    Disjoint (fixedSpace ρ ⊤) (moving ρ).toSubmodule ↔
      fixedSpace (moving ρ).toRepresentation ⊤ = ⊥ := by
  rw [disjoint_iff]
  constructor
  · intro h
    apply le_bot_iff.mp
    intro v hv
    have hm : (v : V) ∈ fixedSpace ρ ⊤ ⊓ (moving ρ).toSubmodule :=
      ⟨fun g => congrArg Subtype.val (hv g), v.property⟩
    rw [h] at hm
    exact Subtype.ext hm
  · intro h
    apply le_bot_iff.mp
    intro v hv
    have hm : (⟨v, hv.2⟩ : (moving ρ).toSubmodule) ∈
        fixedSpace (moving ρ).toRepresentation ⊤ :=
      fun g => Subtype.ext (hv.1 g)
    rw [h] at hm
    exact congrArg Subtype.val hm

variable [FiniteDimensional (ZMod 2) V]

/-- Restricting an offender to D preserves its fixed-codimension budget. -/
theorem moving_isFFModule (hFF : IsFFModule ρ) : IsFFModule (moving ρ).toRepresentation := by
  obtain ⟨A, hA, hbudget⟩ := hFF
  exact ⟨A, hA, (fixedCodim_subrepresentation_le ρ (moving ρ) A).trans hbudget⟩

/-- The actual commutator module has dimension at most six. -/
theorem moving_finrank_le_six (hFF : IsFFModule ρ) :
    Module.finrank (ZMod 2) (moving ρ).toSubmodule ≤ 6 :=
  ExtensionControl.finrank_le_six _ (moving_full ρ) (moving_isFFModule ρ hFF)

/-- The established fully moving classification applies to the actual D. -/
theorem moving_quotient (hρ : Function.Injective ρ) (hFF : IsFFModule ρ) :
    ∃ m : ℕ, (m = 1 ∨ m = 2) ∧ Nonempty (ModuleQuotient (moving ρ).toRepresentation m) :=
  ExtensionControl.exists_moduleQuotient _ (moving_faithful ρ hρ)
    (moving_full ρ) (moving_isFFModule ρ hFF)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.CentralAttachments
