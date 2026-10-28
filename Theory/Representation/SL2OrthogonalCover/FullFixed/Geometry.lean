module
public import Theory.Representation.SL2OrthogonalCover.Universal
public import Theory.Representation.SL2NaturalOffenders.Semilinear
public import Theory.Representation.CentralCoverOriginalAction.Quadratic
public import Theory.Representation.NormalPSubgroupKernel
import Mathlib.Tactic.FinCases

/-!
# Singular representatives in the universal natural SL₂ cover

The orthogonal form r²+xy has exactly one singular representative above each
natural vector. Every binary normalizing actor preserves these representatives:
the scalar commutant identifies its semilinear quotient action, and the zero-polar
quadratic difference vanishes by commutator generation.

Source: Aschbacher–Smith I.2.3(1a),(2), printed p.413.
-/

@[expose] public section
noncomputable section
namespace Representation.SL2OrthogonalCover.FullFixed
open Matrix Representation.OneCohomology Representation.OneCohomology.CentralCoverOriginalAction
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

def pairing : LinearMap.BilinForm F (Plane F) where
  toFun v :=
    { toFun w := v 0 * w 1 + v 1 * w 0
      map_add' w x := by simp only [Pi.add_apply]; ring
      map_smul' c w := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  map_add' v w := by
    apply LinearMap.ext; intro x
    change (v 0 + w 0) * x 1 + (v 1 + w 1) * x 0 = _
    change (v 0 + w 0) * x 1 + (v 1 + w 1) * x 0 = (v 0 * x 1 + v 1 * x 0) + (w 0 * x 1 + w 1 * x 0)
    ring
  map_smul' c v := by
    apply LinearMap.ext; intro w
    change c * v 0 * w 1 + c * v 1 * w 0 = c * (v 0 * w 1 + v 1 * w 0)
    ring

omit [Finite F] [CharP F 2] [Algebra (ZMod 2) F] in
theorem pairing_nondegenerate : (pairing (F := F)).Nondegenerate := by
  constructor
  · intro v hv
    have h0 := hv ![0,1]
    have h1 := hv ![1,0]
    ext i
    fin_cases i
    · simpa [pairing] using h0
    · simpa [pairing] using h1
  · intro v hv
    have h0 := hv ![0,1]
    have h1 := hv ![1,0]
    ext i
    fin_cases i
    · simpa [pairing] using h0
    · simpa [pairing] using h1

omit [Finite F] [Algebra (ZMod 2) F] in
theorem pairing_invariant (g : SL F) (v w : Plane F) :
    pairing (natural g v) (natural g w) = pairing v w := by
  change (natural g v) 0 * (natural g w) 1 +
    (natural g v) 1 * (natural g w) 0 = _
  simp only [natural, specialLinearNatural_apply, mulVec, dotProduct, Fin.sum_univ_two]
  have hd := det_relation g
  calc
    _ = (g.val 0 0 * g.val 1 0) * (v 0 * w 0 + v 0 * w 0) +
        (g.val 0 1 * g.val 1 1) * (v 1 * w 1 + v 1 * w 1) +
        (g.val 0 0 * g.val 1 1 + g.val 0 1 * g.val 1 0) *
          (v 0 * w 1 + v 1 * w 0) := by ring
    _ = _ := by rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, hd]; simp [pairing]

omit [Algebra (ZMod 2) F] in
theorem singular_unique (u v : Space F)
    (hp : projection u = projection v) (hu : form u = 0) (hv : form v = 0) : u = v := by
  have h1 : u 1 = v 1 := congrFun hp 0
  have h2 : u 2 = v 2 := congrFun hp 1
  have h0 : u 0 = v 0 := by
    apply CharTwo.sq_injective
    rw [form_apply] at hu hv
    rw [h1, h2] at hu
    exact add_right_cancel (hu.trans hv.symm)
  ext i
  fin_cases i <;> assumption

omit [Algebra (ZMod 2) F] in
theorem exists_singular (v : Plane F) :
    ∃ u : Space F, projection u = v ∧ form u = 0 := by
  refine ⟨![root (v 0 * v 1), v 0, v 1], ?_, ?_⟩
  · ext i; fin_cases i <;> rfl
  · rw [form_apply]
    change root (v 0 * v 1) ^ 2 + v 0 * v 1 = 0
    rw [sq_root, CharTwo.add_self_eq_zero]

theorem normalizer_preserves_singular (hF : 2 < Nat.card F)
    (a : MulAut (SL F)) (e : Plane F ≃ₗ[ZMod 2] Plane F)
    (E : Space F ≃ₗ[ZMod 2] Space F)
    (he : ∀ l v, e (natural l v) = natural (a l) (e v))
    (hE : ∀ l u, E (action l u) = action (a l) (E u))
    (hover : ∀ u, projection (E u) = e (projection u)) :
    ∀ u, form (E u) = 0 ↔ form u = 0 := by
  apply lift_preserves_singular (natural (F := F)) (action (F := F)) (projection (F := F)) (binaryProjection_isCover hF)
    (fun f hf => SL2NaturalOffenders.centralizer_scalar f hf)
    pairing pairing_nondegenerate pairing_invariant form form_invariant
    (fun u v => polar_apply u v) a e E he hE hover
end Representation.SL2OrthogonalCover.FullFixed
