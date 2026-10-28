module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Preparation
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Components.Placement
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Geometry

/-!+# The marked small actions needed in the component branch of 14.7.67

The decomposition contract records an actual direct complement to the moved
space and an equivariant identification of that space. Its A₅ alternative is
the orthogonal deleted permutation module; its L₃(2) alternative uses one
group identification on at most two copies of the natural module. The kernel
of each marked quotient is the actor's literal two-core. These definitions
contain no assertion about centralizer residuals and do not prove that the
source action has such a decomposition.

The source adapters use the already constructed representation of Y/O₂(Y)
on E, restricted to the original component, and the original element z
generating V₁. They identify its vector stabilizer with the actual ambient
point centralizer and supply the Sylow fixed-point condition. Thus the
remaining model calculation has a specified consumer on the original action.

The decomposition is still to be constructed from genuine 1.2.10, all the
needed 14.3.4 clauses, and the corrected universal B.5.1 contract. Component
exclusion and solvability remain with the Thompson.Components assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.67(4), printed p.1070, PDF p.1087.
-/

@[expose] public section
noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Theory.GroupTheory

namespace ResidualNormalizer.Components
open ChapterB.QuasisimpleSource Representation.BinaryOffender
universe u v w x
variable {A : Type u} [Group A] {E : Type v} [AddCommGroup E] [Module (ZMod 2) E]

/-- A marking of the actual two-core quotient and the actual module together. -/
structure QuotientActionMarking (ρ : Representation (ZMod 2) A E)
    {M : Type w} [Group M] {N : Type x} [AddCommGroup N] [Module (ZMod 2) N]
    (σ : Representation (ZMod 2) M N) where
  quotient : A →* M
  onto : Function.Surjective quotient
  kernel : quotient.ker = pCore 2 A
  coordinates : E ≃ₗ[ZMod 2] N
  intertwines : ∀ a v, coordinates (ρ a v) = σ (quotient a) (coordinates v)

/-- These are module identifications, with a single group marking on all summands. -/
inductive SmallMovedAction (ρ : Representation (ZMod 2) A E) : Prop
  | alternatingFive (marking : QuotientActionMarking ρ (alternatingNatural 5))
  | linearThree (r : ℕ) (positive : 0 < r) (bound : r ≤ 2)
      (marking : QuotientActionMarking ρ (repeated (linearNatural BinaryField.two 3) r))

/-- The splitting and marked action that the source B.5.1 application must construct.
The stronger source complement C_E(BR₁) must also be retained at that application. -/
structure SmallModuleDecomposition (ρ : Representation (ZMod 2) A E) where
  movedSpace : Subrepresentation ρ
  moved_eq : movedSpace.toSubmodule = subspaceCommutator ρ ⊤ ⊤
  splitting : IsCompl movedSpace.toSubmodule ρ.invariants
  action : SmallMovedAction movedSpace.toRepresentation

/-- The stabilizer of one vector in the original acting group. -/
def pointStabilizer (ρ : Representation (ZMod 2) A E) (v : E) : Subgroup A where
  carrier := {a | ρ a v = v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change ρ a v = v at ha
    change ρ b v = v at hb
    change ρ (a * b) v = v
    simp only [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    change ρ a v = v at ha
    change ρ a⁻¹ v = v
    have he := congrArg (ρ a⁻¹) ha
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using he.symm

end ResidualNormalizer.Components

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

namespace Data
open ResidualNormalizer ResidualNormalizer.Components
variable (d : Data T L V F W)

/-- Restrict the literal Y/O₂(Y) action to an ambient subgroup of Y. -/
def residualComponentRepresentation
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hBY : B ≤ Y L F) :
    letI := (d.residualSpan_reduced hSylow).elementary
    Representation (ZMod 2) B (Additive ((E F).subgroupOf (Y L F))) := by
  letI := (d.residualSpan_reduced hSylow).elementary
  exact (d.residualRepresentation hSylow).comp
    ((QuotientGroup.mk' (pCore 2 (Y L F))).comp (inclusion hBY))

/-- The original generator z of V₁, as a vector of the original E. -/
def residualPointVector : Additive ((E F).subgroupOf (Y L F)) := by
  have hz : d.z ∈ E F := point_le_E (by rw [d.point]; exact mem_zpowers d.z)
  exact Additive.ofMul ⟨⟨d.z, d.residualSpan_le_D.trans le_sup_left hz⟩, hz⟩

theorem residualPointVector_ne_zero : d.residualPointVector ≠ 0 := by
  intro he
  exact d.z_ne_one (congrArg (fun v : Additive ((E F).subgroupOf (Y L F)) =>
    ((v.toMul : Y L F) : G)) he)

/-- The source action uses ambient conjugation on the same generator z. -/
theorem residualComponentRepresentation_point_apply
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hBY : B ≤ Y L F) (b : B) :
    letI := (d.residualSpan_reduced hSylow).elementary
    (((d.residualComponentRepresentation hSylow hBY b d.residualPointVector).toMul :
      Y L F) : G) = (b : G) * d.z * (b : G)⁻¹ :=
  d.residualRepresentation_apply hSylow (inclusion hBY b) d.residualPointVector

/-- The vector stabilizer is the original point centralizer, restricted to B. -/
theorem residualComponentPointStabilizer_eq
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hBY : B ≤ Y L F) :
    letI := (d.residualSpan_reduced hSylow).elementary
    pointStabilizer (d.residualComponentRepresentation hSylow hBY) d.residualPointVector =
      (centralizer (F.Vi 1 : Set G)).subgroupOf B := by
  let := (d.residualSpan_reduced hSylow).elementary
  ext b
  change d.residualComponentRepresentation hSylow hBY b d.residualPointVector =
    d.residualPointVector ↔ (b : G) ∈ centralizer (F.Vi 1 : Set G)
  rw [d.point, zpowers_eq_closure, centralizer_closure, mem_centralizer_singleton_iff]
  have he := d.residualComponentRepresentation_point_apply hSylow hBY b
  constructor
  · intro hf
    have hv := congrArg (fun v : Additive ((E F).subgroupOf (Y L F)) =>
      ((v.toMul : Y L F) : G)) hf
    exact mul_inv_eq_iff_eq_mul.mp (he.symm.trans hv)
  · intro hc
    apply Subtype.ext
    apply Subtype.ext
    exact he.trans (mul_inv_eq_iff_eq_mul.mpr hc)

/-- Mapping the vector stabilizer into G gives the literal C_B(V₁). -/
theorem residualComponentPointStabilizer_map
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hBY : B ≤ Y L F) :
    letI := (d.residualSpan_reduced hSylow).elementary
    (pointStabilizer (d.residualComponentRepresentation hSylow hBY) d.residualPointVector).map
      B.subtype = B ⊓ centralizer (F.Vi 1 : Set G) := by
  let := (d.residualSpan_reduced hSylow).elementary
  rw [d.residualComponentPointStabilizer_eq hSylow hBY, subgroupOf_map_subtype, inf_comm]

/-- The original point is fixed by a Sylow subgroup of the component. -/
theorem residual_component_point_fixed_by_sylow
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F)) :
    letI := (d.residualSpan_reduced hSylow).elementary
    ∃ P : Sylow 2 B, (P : Subgroup B) ≤
      pointStabilizer (d.residualComponentRepresentation hSylow (hB.1.trans J_le_Y))
        d.residualPointVector := by
  let := (d.residualSpan_reduced hSylow).elementary
  obtain ⟨P, hP⟩ := residual_component_sylow hB hSylow
  refine ⟨P, ?_⟩
  rw [d.residualComponentPointStabilizer_eq hSylow (hB.1.trans J_le_Y), hP]
  intro b hb
  exact d.H_centralizes_point (residual_R_le_H hb)

/-- The literal vector stabilizer has trivial two-residual; the marked small actions must contradict this. -/
theorem residual_component_point_stabilizer_residual_eq_bot
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F)) :
    letI := (d.residualSpan_reduced hSylow).elementary
    pResidual 2 (pointStabilizer
      (d.residualComponentRepresentation hSylow (hB.1.trans J_le_Y)) d.residualPointVector) = ⊥ := by
  let := (d.residualSpan_reduced hSylow).elementary
  have hp : IsPGroup 2 (pointStabilizer
      (d.residualComponentRepresentation hSylow (hB.1.trans J_le_Y)) d.residualPointVector) := by
    rw [d.residualComponentPointStabilizer_eq hSylow (hB.1.trans J_le_Y)]
    intro b
    have hb : (b.val : G) ∈ (T : Subgroup G) :=
      d.residual_component_point_centralizer_le_sylow hB ⟨b.val.property, b.property⟩
    obtain ⟨n, hn⟩ := T.isPGroup' ⟨b.val, hb⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    change (b.val : G) ^ 2 ^ n = 1
    exact congrArg (fun t : T => (t : G)) hn
  apply bot_unique
  exact sInf_le ⟨inferInstance,
    hp.of_surjective (QuotientGroup.mk' ⊥) (QuotientGroup.mk'_surjective ⊥)⟩


end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
