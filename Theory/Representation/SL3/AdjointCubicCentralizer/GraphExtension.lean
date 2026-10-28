module
public import Theory.Representation.SL3.AdjointCubicCentralizer.GraphExtension.Graph
public import Theory.SpecificGroups.PSL3.ExtensionBorel.Linear

/-!
# The adjoint extension under a specified PSL₃ graph actor

Transport conjugation by the given automorphism of PSL₃ through the literal
pglEquivInnerDiagonal. Its arbitrary inner-diagonal correction is absorbed
in the given representation; graph-field compatibility then forces equality
with projectiveAdjoint under the original marking. No involution condition
on the binary lift and no restriction on the field automorphism is needed.

Source motivation: Aschbacher–Smith B.4.14, printed p.98, and the nonblock
argument for original 4.3.2, pp.618–619. These are representation consequences
of explicit action hypotheses; constructing the source Frattini marking and
discharging its action-kernel descent are separate source obligations.
-/

open Matrix Representation
open scoped MatrixGroups
open Matrix.PSL3.OuterSolvable Matrix.PSL3.ExtensionBorel
namespace Representation.SL3.AdjointCubicCentralizer.GraphExtension
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (F : Type*) [Field F]

def conjugatePGL (a : MulAut PSL(3,F))
    (ha : a ∈ Subgroup.normalizer (innerDiagonal F)) :
    MulAut (ProjGenLinGroup (Fin 3) F) :=
  ((pglEquivInnerDiagonal F).trans ((innerDiagonal F).normalizerMonoidHom ⟨a,ha⟩)).trans
    (pglEquivInnerDiagonal F).symm

theorem conjugatePGL_spec (a : MulAut PSL(3,F))
    (ha : a ∈ Subgroup.normalizer (innerDiagonal F)) (p : ProjGenLinGroup (Fin 3) F) :
    (pglEquivInnerDiagonal F (conjugatePGL F a ha p)).val =
      a * (pglEquivInnerDiagonal F p).val * a⁻¹ := by
  change ((pglEquivInnerDiagonal F) ((pglEquivInnerDiagonal F).symm _)).val = _
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem graphActor_normalizes (a : MulAut PSL(3,F))
    (m : GL (Fin 3) F) (σ : F ≃+* F)
    (ha : a = linearConj F m * graph F * fieldAction F σ) :
    a ∈ Subgroup.normalizer (innerDiagonal F) := by
  rw [ha]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _
    ((innerDiagonal F).le_normalizer ⟨m,rfl⟩) graph_mem_normalizer_innerDiagonal)
    (fieldAction_mem_normalizer_innerDiagonal σ)

theorem conjugatePGL_graph_mk (a : MulAut PSL(3,F))
    (hn : a ∈ Subgroup.normalizer (innerDiagonal F))
    (m : GL (Fin 3) F) (σ : F ≃+* F)
    (ha : a = linearConj F m * graph F * fieldAction F σ) (g : GL (Fin 3) F) :
    conjugatePGL F a hn (ProjGenLinGroup.mk g) =
      ProjGenLinGroup.mk (m * graphFieldGL F σ g * m⁻¹) := by
  apply (pglEquivInnerDiagonal F).injective
  apply Subtype.ext
  rw [conjugatePGL_spec,pglEquiv_mk,pglEquiv_mk,ha]
  calc
    _ = linearConj F m *
        (graph F * (fieldAction F σ * linearConj F g * (fieldAction F σ)⁻¹) *
          (graph F)⁻¹) * (linearConj F m)⁻¹ := by group
    _ = _ := by
      rw [field_linearConj,mul_inv_cancel_right,graph_linearConj,mul_inv_cancel_right]
      simp only [graphFieldGL,MonoidHom.comp_apply,map_mul,map_inv]

variable [Finite F] [CharP F 2]
attribute [local instance] ZMod.algebra

theorem ordinary_of_graphActor (hF : Nat.card F = 4)
    (R : Representation (ZMod 2) (ProjGenLinGroup (Fin 3) F) (TraceZero F))
    (hR : R.comp ProjectiveSpecialLinearGroup.toPGL =
      restrictScalars (k := ZMod 2) (projectiveSpecialAdjoint F))
    (a : MulAut PSL(3,F)) (hn : a ∈ Subgroup.normalizer (innerDiagonal F))
    (m : GL (Fin 3) F) (σ : F ≃+* F)
    (ha : a = linearConj F m * graph F * fieldAction F σ)
    (u : TraceZero F ≃ₗ[ZMod 2] TraceZero F)
    (hu : ∀ p v, u (R p v) = R (conjugatePGL F a hn p) (u v)) :
    R = restrictScalars (k := ZMod 2) (projectiveAdjoint F) := by
  let S : Representation (ZMod 2) (GL (Fin 3) F) (TraceZero F) := R.comp ProjGenLinGroup.mk
  have hs (s : SL(3,F)) : S (SpecialLinearGroup.toGL s) =
      binaryAdjoint F (SpecialLinearGroup.toGL s) :=
    DFunLike.congr_fun hR (QuotientGroup.mk s)
  let um : TraceZero F ≃ₗ[ZMod 2] TraceZero F :=
    LinearEquiv.ofBijective (S m⁻¹) (S.apply_bijective m⁻¹)
  have he : S = binaryAdjoint F := ordinary_of_graphField F hF S hs σ (u.trans um) (by
    intro g v
    change S m⁻¹ (u (R (ProjGenLinGroup.mk g) v)) =
      S (graphFieldGL F σ g) (S m⁻¹ (u v))
    rw [hu,conjugatePGL_graph_mk F a hn m σ ha]
    change S m⁻¹ (S (m * graphFieldGL F σ g * m⁻¹) (u v)) = _
    simp only [map_mul,Module.End.mul_apply]
    rw [S.inv_self_apply])
  apply MonoidHom.ext
  intro p
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (GL (Fin 3) F)) p
  exact DFunLike.congr_fun he g

end
end Representation.SL3.AdjointCubicCentralizer.GraphExtension
