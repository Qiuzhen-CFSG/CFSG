module
public import Theory.Representation.ScalarMultiplicity
public import Theory.Representation.BinaryDoubledNaturalCentralizer
public import Theory.Representation.BinaryParabolicNatural.RepeatedOffender
public import Theory.Representation.BinaryOffender.QuadraticRatioTransport

/-!
# Multiplicity actions for repeated binary natural modules

A linear action commuting with repeated copies of the full binary natural
module acts through a single matrix on the multiplicity space. The scalar
commutant theorem constructs that matrix without requiring preservation of
individual natural copies. Transposing the original coordinates identifies
the commuting action with d copies of its multiplicity action.

The full action kernel and quadraticity are preserved, and every subgroup's
fixed codimension is exactly d times its multiplicity fixed codimension.
The original local quotient in Section12.9 uses this to compare its F.9 actor
with the minimal-parabolic chief-factor bound.

Source: Aschbacher--Smith, 12.8.5(1) and the multiplicity argument in the
proof of 12.9.5, printed pp.850,861. The scalar calculation is reused from
BinaryDoubledNaturalCentralizer; no chief-factor bound is assumed here.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.BinaryNaturalMultiplicity
open BinaryLinear.OuterCyclic
variable {C : Type*} [Group C] {d r : ℕ}

/-- Construct the actual multiplicity matrix of every commuting actor. -/
theorem exists_multiplicity
    (hd : 2 ≤ d)
    (τ : Representation (ZMod 2) C (Fin r → Fin d → ZMod 2))
    (hc : ∀ c (g : LinearGroup d) x,
      τ c (fun i => g (x i)) = fun i => g (τ c x i)) :
    ∃ μ : Representation (ZMod 2) C (Fin r → ZMod 2),
      ∀ c x i j, τ c x i j = μ c (fun k => x k j) i := by
  let : NeZero d := ⟨by omega⟩
  let σ := BinaryParabolicNatural.natural (Fin d → ZMod 2)
  have hs (f : (Fin d → ZMod 2) →ₗ[ZMod 2] (Fin d → ZMod 2))
      (hf : ∀ g v, f (σ g v) = σ g (f v)) :
      ∃ a : ZMod 2, ∀ v, f v = a • v := by
    apply BinaryDoubledNatural.natural_centralizer_scalar hd f.toAddMonoidHom
    intro g v
    have h := hf (slEquivLinear d g) v
    change f ((slEquivLinear d g) v) = (slEquivLinear d g) (f v) at h
    change f (g.val.mulVec v) = g.val.mulVec (f v)
    simpa only [slEquivLinear_apply] using h
  obtain ⟨μ,hμ⟩ := ScalarMultiplicity.exists_multiplicity σ hs τ hc
  refine ⟨μ,?_⟩
  intro c x i j
  have hx : x = ∑ j : Fin d, fun i => x i j • (Pi.single j 1 : Fin d → ZMod 2) := by
    ext i j
    simp [Finset.sum_apply, Pi.single_apply, mul_ite]
  calc
    τ c x i j = (∑ l : Fin d, τ c (fun k => x k l • (Pi.single l 1 : Fin d → ZMod 2))) i j := by
      rw [←map_sum,←hx]
    _ = μ c (fun k => x k j) i := by
      simp only [hμ,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
      simp [Pi.single_apply, mul_ite]

/-- The original coordinates, transposed, identify a commuting action with
exactly d identical copies of its multiplicity representation. -/
theorem exists_coordinates
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {D : Type*} [Group D] (hd : 2 ≤ d)
    (α : D →* LinearGroup d) (hα : Function.Surjective α)
    (σ : Representation (ZMod 2) D V)
    (τ : Representation (ZMod 2) C V)
    (hc : ∀ c g v, τ c (σ g v) = σ g (τ c v))
    (e : V ≃ₗ[ZMod 2] (Fin r → Fin d → ZMod 2))
    (he : ∀ g v i, e (σ g v) i = α g (e v i)) :
    ∃ μ : Representation (ZMod 2) C (Fin r → ZMod 2),
      ∀ c v j i, e (τ c v) i j = μ c (fun k => e v k j) i := by
  let ν : Representation (ZMod 2) C (Fin r → Fin d → ZMod 2) :=
    e.conjRingEquiv.toMonoidHom.comp τ
  have hn : ∀ c (g : LinearGroup d) x,
      ν c (fun i => g (x i)) = fun i => g (ν c x i) := by
    intro c g x
    obtain ⟨a,rfl⟩ := hα g
    obtain ⟨v,rfl⟩ := e.surjective x
    have hev : e (σ a v) = fun i => α a (e v i) := funext (he a v)
    change e (τ c (e.symm (fun i => α a (e v i)))) = _
    rw [←hev,e.symm_apply_apply,hc]
    funext i
    rw [he]
    change α a (e (τ c v) i) = α a (e (τ c (e.symm (e v))) i)
    rw [e.symm_apply_apply]
  obtain ⟨μ,hμ⟩ := exists_multiplicity hd ν hn
  refine ⟨μ,?_⟩
  intro c v j i
  have hh := hμ c (e v) i j
  change e (τ c (e.symm (e v))) i j = _ at hh
  simpa only [e.symm_apply_apply] using hh

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (τ : Representation (ZMod 2) C V)
    (e : V ≃ₗ[ZMod 2] (Fin r → Fin d → ZMod 2))
    (μ : Representation (ZMod 2) C (Fin r → ZMod 2))
    (he : ∀ c v j i, e (τ c v) i j = μ c (fun k => e v k j) i)

private def transposeCoordinates : V ≃ₗ[ZMod 2] (Fin d → Fin r → ZMod 2) :=
  e.trans {
    toFun := Function.swap
    invFun := Function.swap
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

include he

private theorem transpose_equivariant (c : C) (v : V) :
    transposeCoordinates e (τ c v) =
      BinaryParabolicNatural.copies (Fin d) μ c (transposeCoordinates e v) := by
  ext j i
  exact he c v j i

/-- The multiplicity representation retains the entire original kernel. -/
theorem ker_eq (hd : 0 < d) : μ.ker = τ.ker := by
  ext c
  constructor
  · intro hc
    apply LinearMap.ext
    intro v
    apply e.injective
    ext i j
    change e (τ c v) i j = e v i j
    rw [he,hc]
    rfl
  · intro hc
    let j : Fin d := ⟨0,hd⟩
    apply LinearMap.ext
    intro v
    let x := e.symm (fun i => Pi.single j (v i))
    have hx : (fun k => e x k j) = v := by ext k; simp [x]
    ext i
    have hh := he c x j i
    rw [hc] at hh
    change e x i j = μ c (fun k => e x k j) i at hh
    rw [hx] at hh
    exact hh.symm.trans (congrFun hx i)

/-- Faithfulness is preserved without choosing an invariant natural summand. -/
theorem faithful (hf : Function.Injective τ) : Function.Injective μ := by
  intro a b hab
  apply hf
  apply LinearMap.ext
  intro v
  apply e.injective
  ext i j
  rw [he,he,hab]

/-- Every natural coordinate contributes the same fixed codimension. -/
theorem fixedCodim_eq (A : Subgroup C) : fixedCodim τ A = d * fixedCodim μ A := by
  have hh := fixedCodim_map_equivariant τ (BinaryParabolicNatural.copies (Fin d) μ)
    (MonoidHom.id C) (transposeCoordinates e) (transpose_equivariant τ e μ he) A
  simpa only [Subgroup.map_id,BinaryParabolicNatural.fixedCodim_copies,Fintype.card_fin] using hh

/-- Quadraticity descends to the same actor on the multiplicity space. -/
theorem quadratic (hd : 0 < d) {A : Subgroup C} (hA : IsQuadratic τ A) :
    IsQuadratic μ A := by
  have hh := quadratic_map_equivariant τ (BinaryParabolicNatural.copies (Fin d) μ)
    (MonoidHom.id C) (transposeCoordinates e) (transpose_equivariant τ e μ he) hA
  rw [Subgroup.map_id] at hh
  intro a ha b hb v
  exact congrFun (hh a ha b hb (fun _ : Fin d => v)) ⟨0,hd⟩

end Representation.BinaryNaturalMultiplicity
