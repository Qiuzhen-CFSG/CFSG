module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.NaturalSum.Action
public import Theory.Representation.BinaryConjugationSection.InvariantPreimage

/-!
# The marked seed generates the literal closure quotient

The seed is the image of V₃ in G₁/V₁. Its inclusion in the closure quotient
is binary linear and respects the original K action. Pulling an invariant
subspace back through the original quotient proves that its H₁ orbit spans
the whole closure quotient. The natural marking is a preceding flag input;
it includes a genuine identification of K/O₂(K) and an intertwining map.

Source: Aschbacher--Smith 11.5.5(3), printed p.780.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

theorem V₃_le_G₁ : E.V₃ ≤ E.G₁ := by
  let := D.elementary
  exact (D.centralQuotientPreimage_le E.threeSpace).trans
    ((Subgroup.le_centralizer (H := V)).trans ((Subgroup.centralizer_le E.V₁_le).trans
      (Subgroup.centralizer_le_normalizer _)))

/-- The binary space on the original seed image. -/
instance seedElementary : IsElementaryAbelian 2 (E.tilde E.V₃) := by
  let : IsElementaryAbelian 2 E.V₃ := D.centralQuotientPreimage_elementary E.threeSpace
  let := IsElementaryAbelian.subgroupOf (p := 2) E.V₃_le_G₁
  exact IsElementaryAbelian.map (QuotientGroup.mk' (E.V₁.subgroupOf E.G₁))

namespace ClosureFlag
variable {E} (f : E.ClosureFlag)

/-- The literal K action on Ṽ₃ in the branch K=L₁. -/
def seedAction (hK : E.K = E.L₁) : Representation (ZMod 2) E.K
    (Additive (E.tilde E.V₃)) where
  toFun k := (E.tildeConjugation E.V₃ E.K E.K_le_G₁
    (hK ▸ le_sup_left.trans f.local_normalizes_seed) k).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro v
    change Additive.ofMul (E.tildeConjugation E.V₃ E.K E.K_le_G₁
      (hK ▸ le_sup_left.trans f.local_normalizes_seed) 1 v.toMul) = v
    rw [map_one]
    rfl
  map_mul' a b := by
    apply LinearMap.ext
    intro v
    change Additive.ofMul (E.tildeConjugation E.V₃ E.K E.K_le_G₁
      (hK ▸ le_sup_left.trans f.local_normalizes_seed) (a * b) v.toMul) = _
    rw [map_mul]
    rfl

/-- The preceding natural-action marking, with its actual quotient map.
There is no marking of the closure or a sum among these inputs. -/
structure NaturalSeed (hK : E.K = E.L₁) where
  groupEquiv : (E.K ⧸ pCore 2 E.K) ≃*
    Matrix.SpecialLinearGroup (Fin 2) E.input.field.Carrier
  linearEquiv : Additive (E.tilde E.V₃) ≃ₗ[ZMod 2] (Fin 2 → E.input.field.Carrier)
  intertwines : ∀ k v, linearEquiv (f.seedAction hK k v) =
    linearNatural E.input.field 2 (groupEquiv (QuotientGroup.mk' (pCore 2 E.K) k))
      (linearEquiv v)

variable (H₁ : Subgroup G) (hH : H₁ ≤ E.G₁)
    (hLH : E.L₁ ⊔ (T : Subgroup G) ≤ H₁)

/-- Inclusion of the genuine seed quotient into the genuine closure quotient. -/
def seedEmbedding : Additive (E.tilde E.V₃) →ₗ[ZMod 2]
    f.Space H₁ hH hLH :=
  (inclusion (map_mono (comap_mono (le_conjugateSpanBy E.V₃ H₁)))).toAdditive.toZModLinearMap 2

theorem seedEmbedding_injective : Function.Injective (f.seedEmbedding H₁ hH hLH) := by
  intro x y h
  apply Additive.toMul.injective
  apply Subtype.ext
  exact congrArg (fun z : f.Space H₁ hH hLH =>
    (z.toMul : E.Tilde)) h

theorem seedEmbedding_intertwines (hK : E.K = E.L₁) (k : E.K)
    (v : Additive (E.tilde E.V₃)) :
    f.seedEmbedding H₁ hH hLH (f.seedAction hK k v) =
      f.restrictedAction H₁ hH hLH hK k (f.seedEmbedding H₁ hH hLH v) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  rfl

/-- The original closure and point, with the literal quotient coordinates. -/
def quotientSection : BinaryConjugationSection H₁ (E.localClosure H₁) E.V₁ (f.action H₁ hH hLH) where
  section_le := closure_le H₁ hLH
  kernel_le := f.point_le_seed.trans (le_conjugateSpanBy _ _)
  normalized := le_normalizer_conjugateSpanBy _ _
  coordinates := {
    toFun u := Multiplicative.ofAdd (Additive.ofMul
      (E.tildeProjection (E.localClosure H₁) ((closure_le H₁ hLH).trans hH) u))
    map_one' := by
      change E.tildeProjection (E.localClosure H₁) ((closure_le H₁ hLH).trans hH) 1 = 1
      exact map_one _
    map_mul' u v := by
      change E.tildeProjection (E.localClosure H₁) ((closure_le H₁ hLH).trans hH) (u * v) = _
      exact map_mul _ u v }
  onto := E.tildeProjection_surjective _ ((closure_le H₁ hLH).trans hH)
  kernel_eq := E.tildeProjection_kernel _ ((closure_le H₁ hLH).trans hH)
  equivariant h u := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change QuotientGroup.mk' (E.V₁.subgroupOf E.G₁)
      ((⟨h, hH h.property⟩ : E.G₁) * ⟨u, hH (closure_le H₁ hLH u.property)⟩ *
        ⟨h, hH h.property⟩⁻¹) = _
    simp only [map_mul, map_inv]
    rfl

/-- The H₁ span assertion is derived from the original subgroup closure. -/
theorem seed_generates (P : Subrepresentation (f.action H₁ hH hLH))
    (hP : (f.seedEmbedding H₁ hH hLH).range ≤ P.toSubmodule) : P = ⊤ := by
  let d := f.quotientSection H₁ hH hLH
  have hseed : E.V₃ ≤ d.invariantPreimage P := by
    intro v hv
    apply (d.mem_invariantPreimage P v).mpr
    refine ⟨le_conjugateSpanBy E.V₃ H₁ hv, ?_⟩
    apply hP
    exact ⟨Additive.ofMul (E.tildeProjection E.V₃ E.V₃_le_G₁ ⟨v, hv⟩), rfl⟩
  have hgen : E.localClosure H₁ ≤ d.invariantPreimage P :=
    conjugateSpanBy_le hseed (d.invariantPreimage_normalized P)
  apply top_unique
  intro v _
  obtain ⟨u, hu⟩ := d.onto (Multiplicative.ofAdd v)
  obtain ⟨_, hp⟩ := (d.mem_invariantPreimage P u).mp (hgen u.property)
  change v ∈ P.toSubmodule
  simpa only [hu, toAdd_ofAdd] using hp

/-- Convert the genuine seed marking to an injective map of the standard
natural module into the closure quotient. -/
def markedSeedMap {hK : E.K = E.L₁} (m : f.NaturalSeed hK) :
    (Fin 2 → E.input.field.Carrier) →ₗ[ZMod 2] f.Space H₁ hH hLH :=
  (f.seedEmbedding H₁ hH hLH).comp m.linearEquiv.symm.toLinearMap

theorem markedSeedMap_injective {hK : E.K = E.L₁} (m : f.NaturalSeed hK) :
    Function.Injective (f.markedSeedMap H₁ hH hLH m) :=
  (f.seedEmbedding_injective H₁ hH hLH).comp m.linearEquiv.symm.injective

theorem markedSeedMap_intertwines {hK : E.K = E.L₁} (m : f.NaturalSeed hK)
    (k : E.K) (v : Fin 2 → E.input.field.Carrier) :
    f.markedSeedMap H₁ hH hLH m
        (linearNatural E.input.field 2 (m.groupEquiv (QuotientGroup.mk' (pCore 2 E.K) k)) v) =
      f.restrictedAction H₁ hH hLH hK k (f.markedSeedMap H₁ hH hLH m v) := by
  have he := m.intertwines k (m.linearEquiv.symm v)
  rw [m.linearEquiv.apply_symm_apply] at he
  have he' := congrArg m.linearEquiv.symm he
  rw [m.linearEquiv.symm_apply_apply] at he'
  change f.seedEmbedding H₁ hH hLH (m.linearEquiv.symm _) = _
  rw [← he', f.seedEmbedding_intertwines]
  rfl

theorem markedSeedMap_generates {hK : E.K = E.L₁} (m : f.NaturalSeed hK)
    (P : Subrepresentation (f.action H₁ hH hLH))
    (hP : (f.markedSeedMap H₁ hH hLH m).range ≤ P.toSubmodule) : P = ⊤ := by
  apply f.seed_generates H₁ hH hLH P
  rintro v ⟨x, rfl⟩
  apply hP
  refine ⟨m.linearEquiv x, ?_⟩
  change f.seedEmbedding H₁ hH hLH (m.linearEquiv.symm (m.linearEquiv x)) = _
  rw [m.linearEquiv.symm_apply_apply]

/-- Conjugation on K is defined using its relative normality in G₁. -/
def actorConjugation : H₁ →* MulAut E.K :=
  E.K.normalizerMonoidHom.comp (inclusion (hH.trans E.G₁_normalizes_K))

theorem actorConjugation_inclusion (hK : E.K = E.L₁) (h : H₁) (k : E.K) :
    inclusion (K_le H₁ hLH hK) (actorConjugation H₁ hH h k) =
      h * inclusion (K_le H₁ hLH hK) k * h⁻¹ := by
  apply Subtype.ext
  rfl

/-- The two-core quotient action is compatible with the original H₁ action.
The induced automorphism is on the literal K/O₂(K). -/
theorem quotientAction_conjugation (hK : E.K = E.L₁) (h : H₁)
    (k : E.K ⧸ pCore 2 E.K) (v : f.Space H₁ hH hLH) :
    f.action H₁ hH hLH h (f.quotientAction H₁ hH hLH hK k v) =
      f.quotientAction H₁ hH hLH hK
        (Subgroup.quotientAut (pCore 2 E.K) (actorConjugation H₁ hH h) k)
        (f.action H₁ hH hLH h v) := by
  induction k using Quotient.inductionOn with
  | h k =>
    change f.action H₁ hH hLH h
      (f.quotientAction H₁ hH hLH hK (QuotientGroup.mk' (pCore 2 E.K) k) v) =
      f.quotientAction H₁ hH hLH hK
        (Subgroup.quotientAut (pCore 2 E.K) (actorConjugation H₁ hH h)
          (QuotientGroup.mk' (pCore 2 E.K) k)) _
    rw [Subgroup.quotientAut_apply_mk]
    change f.action H₁ hH hLH h
      (f.action H₁ hH hLH (inclusion (K_le H₁ hLH hK) k) v) =
      f.action H₁ hH hLH
        (inclusion (K_le H₁ hLH hK) (actorConjugation H₁ hH h k))
        (f.action H₁ hH hLH h v)
    rw [actorConjugation_inclusion H₁ hH hLH hK]
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]

end ClosureFlag
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
