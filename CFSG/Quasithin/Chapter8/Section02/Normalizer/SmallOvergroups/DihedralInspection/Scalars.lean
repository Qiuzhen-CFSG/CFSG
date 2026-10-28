module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.DihedralInspection.Actions
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.Action
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.FieldTheory.Finiteness

/-!
# Scalar refinement of the actual dihedral quotient action

An additive automorphism commuting with one ring generator is linear over
the generated field. This constructs the linear K-action from a scalar
marking of the original X-action on P/U; the kernel remains the original
commutator kernel. Perfectness forces determinant one. The literal orders
of P/U give multiplicity dimension two or three over a field of order 16.

The field and its marked scalar action are explicit inputs here. Constructing
that field from the genuine irreducible X-constituent is a separate obligation,
as is the compatible small-overgroup inspection. The simultaneous action on U
is retained, and no action of T on X or P/U is postulated.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
Proposition 8.2.8(1), printed p.719 (PDF p.736). The corrected scalar convention
for the incoming tensor description is documented in Normalizer.TensorDimension.
-/

public section
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups
open Subgroup
open scoped commutatorElement

private theorem map_smul_of_generator {F W : Type*} [Field F]
    [AddCommGroup W] [Module F W] (ζ : F)
    (hgen : Subring.closure ({ζ} : Set F) = ⊤)
    (f : W ≃+ W) (hf : ∀ v, f (ζ • v) = ζ • f v) :
    ∀ (a : F) (v : W), f (a • v) = a • f v := by
  intro a
  have ha : a ∈ Subring.closure ({ζ} : Set F) := hgen ▸ Subring.mem_top a
  induction ha using Subring.closure_induction with
  | mem x hx => simpa only [Set.mem_singleton_iff.mp hx] using hf
  | zero => simp
  | one => simp
  | add a b _ _ ha hb => intro v; simp only [add_smul, map_add, ha, hb]
  | neg a _ ha => intro v; simp only [neg_smul, map_neg, ha]
  | mul a b _ _ ha hb => intro v; simp only [mul_smul, ha, hb]

variable {F A H : Type*} [Field F] [CommGroup A] [Group H]
  [Module F (Additive A)]

/-- Refine an existing action without changing any of its underlying permutations. -/
noncomputable def scalarRefinement (α : H →* MulAut A) (ζ : F)
    (hgen : Subring.closure ({ζ} : Set F) = ⊤)
    (hcomm : ∀ k v, (α k).toAdditive (ζ • v) = ζ • (α k).toAdditive v) :
    H →* (Additive A ≃ₗ[F] Additive A) where
  toFun k := {
    (α k).toAdditive with
    map_smul' := map_smul_of_generator ζ hgen (α k).toAdditive (hcomm k) }
  map_one' := by
    ext v
    change Additive.ofMul (α 1 v.toMul) = v
    rw [map_one]
    rfl
  map_mul' k l := by
    ext v
    change Additive.ofMul (α (k * l) v.toMul) = _
    rw [map_mul]
    rfl

/-- Scalar refinement preserves the exact action kernel. -/
theorem scalarRefinement_ker (α : H →* MulAut A) (ζ : F)
    (hgen : Subring.closure ({ζ} : Set F) = ⊤)
    (hcomm : ∀ k v, (α k).toAdditive (ζ • v) = ζ • (α k).toAdditive v) :
    (scalarRefinement α ζ hgen hcomm).ker = α.ker := by
  ext k
  constructor
  · intro h
    apply MulEquiv.ext
    intro a
    exact congrArg Additive.toMul (LinearEquiv.congr_fun h (Additive.ofMul a))
  · intro h
    apply LinearEquiv.ext
    intro a
    exact congrArg Additive.ofMul (MulEquiv.congr_fun h a.toMul)

/-- Every refined action of a perfect group has determinant one. -/
theorem scalarRefinement_det (α : H →* MulAut A) (ζ : F)
    (hgen : Subring.closure ({ζ} : Set F) = ⊤)
    (hcomm : ∀ k v, (α k).toAdditive (ζ • v) = ζ • (α k).toAdditive v)
    [Group.IsPerfect H] (k : H) :
    (scalarRefinement α ζ hgen hcomm k).det = 1 := by
  let χ := (LinearEquiv.det : (Additive A ≃ₗ[F] Additive A) →* Fˣ).comp
    (scalarRefinement α ζ hgen hcomm)
  exact Abelianization.commutator_subset_ker χ Group.IsPerfect.mem_commutator

/-- The two source orders of P/U give dimensions two and three over F₁₆. -/
theorem multiplicity_finrank [Finite F] [Finite A] (hF : Nat.card F = 16)
    (hA : Nat.card A = 2 ^ 8 ∨ Nat.card A = 2 ^ 12) :
    Module.finrank F (Additive A) = 2 ∨ Module.finrank F (Additive A) = 3 := by
  have hc : Nat.card A = 16 ^ Module.finrank F (Additive A) := by
    calc
      Nat.card A = Nat.card (Additive A) := Nat.card_congr Additive.ofMul
      _ = 16 ^ Module.finrank F (Additive A) := by
        rw [Module.natCard_eq_pow_finrank (K := F), hF]
  rcases hA with hA | hA
  · left
    have h : 16 ^ Module.finrank F (Additive A) = 16 ^ 2 := by omega
    exact (Nat.pow_right_injective (by decide : 1 < 16)) h
  · right
    have h : 16 ^ Module.finrank F (Additive A) = 16 ^ 3 := by omega
    exact (Nat.pow_right_injective (by decide : 1 < 16)) h


section ActualQuotient
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
    (K I U : Subgroup G) [Group.IsPerfect K]
    [(U.subgroupOf (I.pCoreIn 2)).Normal]
    [IsMulCommutative (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2))]
    [Module F (Additive (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)))]
    (e : (I ⧸ pCore 2 I) ≃* DihedralGroup 5)
    (hQI : K.pCoreIn 2 ≤ normalizer (I : Set G))
    (hKI : ⁅K, I⁆ ≤ K.pCoreIn 2) (hKU : K ≤ normalizer (U : Set G))
    (hUP : U ≤ I.pCoreIn 2)
    (hfull : I.pCoreIn 2 = ⁅I.pCoreIn 2, (pResidual 2 I).map I.subtype⁆ ⊔ U)
    (hIC : I ≤ centralizer (U : Set G))
    (hPP : ⁅I.pCoreIn 2, I.pCoreIn 2⁆ ≤ U)
    (ζ : F) (hgen : Subring.closure ({ζ} : Set F) = ⊤)
    (x : (pResidual 2 I).map I.subtype)
    (hscalar : ∀ v, Additive.ofMul (pairResidualQuotientAction I U hIC x v) =
      ζ • Additive.ofMul v)

open scoped IsMulCommutative

include e hIC hPP x hscalar in
private theorem component_smul (k : K)
    (v : Additive (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2))) :
    (componentCoreQuotientAction K I U hQI hKI hKU hUP hfull k).toAdditive (ζ • v) =
      ζ • (componentCoreQuotientAction K I U hQI hKI hKU hUP hfull k).toAdditive v := by
  have hc := componentCoreQuotientAction_commute K I U e hQI hKI hKU hUP hfull
    hIC hPP k x
  have hh := congrArg Additive.ofMul (MulEquiv.congr_fun hc.eq v.toMul)
  change Additive.ofMul (componentCoreQuotientAction K I U hQI hKI hKU hUP hfull k
      (pairResidualQuotientAction I U hIC x v.toMul)) =
    Additive.ofMul (pairResidualQuotientAction I U hIC x
      (componentCoreQuotientAction K I U hQI hKI hKU hUP hfull k v.toMul)) at hh
  rw [hscalar] at hh
  have he : ζ • v = Additive.ofMul (pairResidualQuotientAction I U hIC x v.toMul) := by
    simpa only [ofMul_toMul] using (hscalar v.toMul).symm
  rw [he]
  exact hh

/-- The multiplicity action is the scalar refinement of the literal component
conjugation action. Its field-generator marking must be constructed from the
source X-constituent; it is not an assumed linearity or kernel conclusion. -/
noncomputable def componentMultiplicityAction :
    K →* (Additive (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)) ≃ₗ[F]
      Additive (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2))) :=
  scalarRefinement (componentCoreQuotientAction K I U hQI hKI hKU hUP hfull)
    ζ hgen (component_smul K I U e hQI hKI hKU hUP hfull hIC hPP ζ x hscalar)

/-- Scalar refinement agrees with conjugation on every element of the literal quotient. -/
theorem componentMultiplicityAction_apply (k : K)
    (v : I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)) :
    componentMultiplicityAction K I U e hQI hKI hKU hUP hfull hIC hPP
      ζ hgen x hscalar k (Additive.ofMul v) =
      Additive.ofMul (componentCoreQuotientAction K I U hQI hKI hKU hUP hfull k v) := by rfl

/-- The F-linear action retains the exact original commutator kernel. -/
theorem mem_componentMultiplicityAction_ker (k : K) :
    k ∈ (componentMultiplicityAction K I U e hQI hKI hKU hUP hfull hIC hPP
      ζ hgen x hscalar).ker ↔
      ∀ p : I.pCoreIn 2, ⁅(k : G), (p : G)⁆ ∈ U := by
  rw [componentMultiplicityAction, scalarRefinement_ker]
  exact mem_componentCoreQuotientAction_ker K I U hQI hKI hKU hUP hfull k

/-- The constructed F-linear action has determinant one, including the code row. -/
theorem componentMultiplicityAction_det (k : K) :
    (componentMultiplicityAction K I U e hQI hKI hKU hUP hfull hIC hPP
      ζ hgen x hscalar k).det = 1 :=
  scalarRefinement_det _ _ _ _ k

/-- Retain the original action on U alongside the constructed multiplicity action.
This is the pair of compatible actions needed by the remaining inspection. -/
@[expose] noncomputable def componentSimultaneousAction :
    K →* MulAut U × (Additive (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)) ≃ₗ[F]
      Additive (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2))) :=
  (U.normalizerMonoidHom.comp (inclusion hKU)).prod
    (componentMultiplicityAction K I U e hQI hKI hKU hUP hfull hIC hPP
      ζ hgen x hscalar)

/-- The first image of the simultaneous action is the literal source image on U. -/
theorem componentSimultaneousAction_first_range :
    ((MonoidHom.fst _ _).comp (componentSimultaneousAction K I U e hQI hKI hKU hUP
      hfull hIC hPP ζ hgen x hscalar)).range = actionImage K U := by
  change (U.normalizerMonoidHom.comp (inclusion hKU)).range = _
  rw [MonoidHom.range_comp, inclusion_range]
  rfl

/-- Restriction to the source R = N_L(U)^∞ retains its literal action image on U. -/
theorem componentSimultaneousAction_localResidual_first_range (L : Subgroup G)
    (hRK : localResidual L U ≤ K) :
    ((MonoidHom.fst _ _).comp ((componentSimultaneousAction K I U e hQI hKI hKU hUP
      hfull hIC hPP ζ hgen x hscalar).comp (inclusion hRK))).range =
      actionImage (localResidual L U) U := by
  change (U.normalizerMonoidHom.comp (inclusion (hRK.trans hKU))).range = _
  rw [MonoidHom.range_comp, inclusion_range]
  rfl

/-- The action kernel is central modulo O₂(K) whenever the marked tensor action
is nontrivial; quasisimplicity is that of the actual two-core quotient. -/
theorem componentMultiplicityAction_kernel_commutator
    [Theory.GroupTheory.IsQuasisimple (K ⧸ pCore 2 K)]
    (hnontriv : ∃ (k : K) (v : I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)),
      componentCoreQuotientAction K I U hQI hKI hKU hUP hfull k v ≠ v) :
    ⁅(componentMultiplicityAction K I U e hQI hKI hKU hUP hfull hIC hPP
      ζ hgen x hscalar).ker, ⊤⁆ ≤ pCore 2 K := by
  apply normal_kernel_commutator_le_twoCore
  rw [componentMultiplicityAction, scalarRefinement_ker]
  intro he
  obtain ⟨k, v, hv⟩ := hnontriv
  exact hv (MulEquiv.congr_fun (show
    k ∈ (componentCoreQuotientAction K I U hQI hKI hKU hUP hfull).ker from
      he ▸ mem_top k) v)

end ActualQuotient
end CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups
