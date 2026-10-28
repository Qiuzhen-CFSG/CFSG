module

public import Theory.Representation.G2BinaryNondegeneratePlane.ExtraspecialCubic
public import Theory.Representation.BinaryCoprimeDegree.CubicDisplacement
public import Theory.AtlasPort.LinearGroups.G2.BinaryDerivedSimplicity

/-!
# Cubic displacement on every nontrivial binary G₂(2)′ module

The marked cubic is noncentral in the explicit extraspecial subgroup of order
27. Restricting a faithful representation gives fixed codimension at least
three. Simplicity of the actual derived octonion group makes every nontrivial
representation faithful, so irreducibility is not an additional hypothesis.

Source: Aschbacher–Smith 13.3.12, printed p.890, the unitary chief-factor step.
-/

public section

open Subgroup Module
namespace Atlas.G2.Natural.BinaryNondegeneratePlane
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

theorem cubic_fixedCodim_ge_three_of_faithful
    (σ : Representation (ZMod 2) (commutator (Model K)) V)
    (hσ : Function.Injective σ) :
    3≤Representation.BinaryOffender.fixedCodim σ (zpowers derivedCubic) := by
  let : IsExtraspecial 3 cubicExtraspecial := cubicExtraspecial_isExtraspecial
  let x : cubicExtraspecial := ⟨derivedCubic,subset_closure (by simp)⟩
  have h := Representation.BinaryCoprimeDegree.noncentral_fixedCodim_ge_three
    (σ.comp cubicExtraspecial.subtype) (hσ.comp cubicExtraspecial.subtype_injective)
    card_cubicExtraspecial (x:=x) cubic_noncentral
  rw [Representation.BinaryOffender.fixedCodim_zpowers_eq_displacement_rank] at h ⊢
  exact h

theorem cubic_fixedCodim_ge_three_of_nontrivial
    (σ : Representation (ZMod 2) (commutator (Model K)) V) (hσ : σ≠1) :
    3≤Representation.BinaryOffender.fixedCodim σ (zpowers derivedCubic) := by
  let : IsSimpleGroup (commutator (Model K)) := Atlas.G2.isSimple_commutator_binary
  apply cubic_fixedCodim_ge_three_of_faithful σ
  apply σ.ker_eq_bot_iff.mp
  exact (inferInstance : σ.ker.Normal).eq_bot_or_eq_top.resolve_right
    (fun h => hσ (MonoidHom.ker_eq_top_iff.mp h))
end Atlas.G2.Natural.BinaryNondegeneratePlane

