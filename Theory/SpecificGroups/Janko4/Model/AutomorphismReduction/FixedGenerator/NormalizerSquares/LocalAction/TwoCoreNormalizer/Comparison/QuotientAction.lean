module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.Reduction
public import Theory.ElementaryAbelian.ExtraspecialSuitableLift
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Coordinates for the literal J₄ two-core quotient action

Write C for the centralizer of the literal first matrix generator inside
`matrixGroup`, and Q for O₂(C). A `Coordinates` value is a multiplicative
isomorphism from the actual Q/Z(Q) onto the additive binary twelve-space.
It constructs `matrixAction : Aut(Q) → GL₁₂(2)` without any recognition
assumption. The application formula uses column vectors and left matrix
multiplication; it fixes the convention for subsequent matrix certificates.

If |Z(Q)| = 2, these coordinates make Q extraspecial. Extraspecial commutator
duality then proves that the kernel is exactly Inn(Q): an automorphism
invisible on Q/Z(Q) fixes the order-two center and its displacement can be
cancelled by an inner automorphism. The abstract argument is kept separate
from the specialization to avoid unfolding the nested matrix subgroup during
elaboration. No quaternion central-product hypothesis is used.

`ActionGenerators` asks for two actual elements generating C modulo Q and
coordinates in which their conjugation actions are the two fixed ATLAS
matrices. These pointwise identities imply the exact matrix image. Neither
such generators and coordinates nor the order of Z(Q) are constructed here.
They are independent concrete obligations for the comparison theorem.

Source motivation: GLS3, Table 5.3i, printed p.270,
`refs/KGroup/GLS3/Chapter5(sec3-).tex`. Its 2A centralizer has shape
Q₈⁶ # (3M₂₂ · 2), and acts irreducibly on the Frattini quotient of its
two-core. The table alone does not identify that action with the literal
`3M22d2G1-f2r12B0` matrices in `TwoCoreLinearModel`.
-/

public section

open scoped IsMulCommutative commutatorElement Matrix

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreComparison

/-- Quotient by the actual center of the literal two-core. -/
abbrev CentralQuotient := involutionTwoCore ⧸ Subgroup.center involutionTwoCore

/-- Binary coordinate column vectors. -/
abbrev Vector := Fin 12 → ZMod 2

/-- Coordinates preserve the quotient group law, interpreted as vector addition. -/
abbrev Coordinates := CentralQuotient ≃* Multiplicative Vector

private def binaryAutLinear :
    MulAut (Multiplicative Vector) ≃* (Vector ≃ₗ[ZMod 2] Vector) where
  toFun a := { AddEquiv.toMultiplicative.symm a with
    map_smul' := ZMod.map_smul (AddEquiv.toMultiplicative.symm a) }
  invFun a := AddEquiv.toMultiplicative a.toAddEquiv
  left_inv a := by ext; rfl
  right_inv a := by ext; rfl
  map_mul' a b := by ext; rfl

/-- Binary group automorphisms as invertible matrices in the standard basis. -/
def binaryAutMatrix : MulAut (Multiplicative Vector) ≃* TwoCoreLinearModel.Matrix12ˣ :=
  binaryAutLinear.trans
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Vector).symm.trans
      Matrix.GeneralLinearGroup.toLin.symm)

theorem binaryAutMatrix_mulVec (a : MulAut (Multiplicative Vector)) (v : Vector) :
    (binaryAutMatrix a : TwoCoreLinearModel.Matrix12) *ᵥ v =
      (a (Multiplicative.ofAdd v)).toAdd := by
  exact LinearMap.toMatrix'_mulVec (binaryAutLinear a).toLinearMap v

/-- The action of every automorphism of Q on its central quotient in given coordinates. -/
def matrixAction (e : Coordinates) :
    MulAut involutionTwoCore →* TwoCoreLinearModel.Matrix12ˣ :=
  ((MulAut.congr e).trans binaryAutMatrix).toMonoidHom.comp
    (Subgroup.quotientAut (Subgroup.center involutionTwoCore))

theorem matrixAction_mulVec (e : Coordinates) (a : MulAut involutionTwoCore) (q : involutionTwoCore) :
    (matrixAction e a : TwoCoreLinearModel.Matrix12) *ᵥ
        (e (QuotientGroup.mk' (Subgroup.center involutionTwoCore) q)).toAdd =
      (e (QuotientGroup.mk' (Subgroup.center involutionTwoCore) (a q))).toAdd := by
  change (binaryAutMatrix ((MulAut.congr e)
    (Subgroup.quotientAut (Subgroup.center involutionTwoCore) a)) :
      TwoCoreLinearModel.Matrix12) *ᵥ _ = _
  rw [binaryAutMatrix_mulVec]
  change (e ((Subgroup.quotientAut (Subgroup.center involutionTwoCore) a)
    (e.symm (e (QuotientGroup.mk' (Subgroup.center involutionTwoCore) q))))).toAdd = _
  rw [e.symm_apply_apply]
  exact congrArg (fun v : CentralQuotient => (e v).toAdd)
    (Subgroup.quotientAut_apply_mk (Subgroup.center involutionTwoCore) a q)

-- Isolating the abstract carrier avoids expensive matrix-subgroup instance unfolding.
private theorem extraspecial_quotientAut_ker_eq_inner {Q : Type*} [Group Q] [Finite Q] [IsExtraspecial 2 Q] :
    (Subgroup.quotientAut (Subgroup.center Q)).ker =
      (MulAut.conj (G := Q)).range := by
  have hfix (a : MulAut Q) (z : Subgroup.center Q) :
      a (z : Q) = z := by
    let e := Subgroup.centerCongr a
    have he : e z = z := by
      by_cases hz : z = 1
      · simp [hz]
      · obtain ⟨w, _, hw⟩ := (Nat.card_eq_two_iff'
          (1 : Subgroup.center Q)).mp
            (IsExtraspecial.center_order_p 2 Q)
        have hn : e z ≠ 1 := fun h => hz (e.injective (h.trans e.map_one.symm))
        exact (hw (e z) hn).trans (hw z hz).symm
    exact congrArg Subtype.val he
  ext a
  change Subgroup.quotientAut (Subgroup.center Q) a = 1 ↔ _
  constructor
  · intro ha
    have hdisplacement (x : Q) :
        a x * x⁻¹ ∈ Subgroup.center Q := by
      have hx := DFunLike.congr_fun ha
        (QuotientGroup.mk' (Subgroup.center Q) x)
      rw [Subgroup.quotientAut_apply_mk] at hx
      have h := QuotientGroup.eq.mp hx.symm
      have hc := Subgroup.Normal.conj_mem
        (show (Subgroup.center Q).Normal from inferInstance)
        (x⁻¹ * a x) h x
      simpa only [mul_assoc, mul_inv_cancel_left] using hc
    obtain ⟨r, hr⟩ := extraspecial_two_exists_inner_twist_fixing_subgroup
      (⊤ : Subgroup Q) le_top a
      (fun z hz => hfix a ⟨z, hz⟩) (fun x _ => hdisplacement x)
    have heq : a * MulAut.conj r = 1 := by
      apply MulEquiv.ext
      intro x
      exact hr x (Subgroup.mem_top x)
    refine ⟨r⁻¹, ?_⟩
    have h := mul_eq_one_iff_eq_inv.mp heq
    simpa only [map_inv] using h.symm
  · rintro ⟨r, rfl⟩
    let _ := IsExtraspecial.quotient_elementary_abelian 2 Q
    apply MulEquiv.ext
    intro v
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
      (Subgroup.center Q) v
    rw [Subgroup.quotientAut_apply_mk]
    change QuotientGroup.mk' (Subgroup.center Q) (r * x * r⁻¹) =
      QuotientGroup.mk' (Subgroup.center Q) x
    simp [mul_comm]

/-- Extraspecial commutator duality identifies the kernel of the quotient action. -/
theorem quotientAut_ker_eq_inner [IsExtraspecial 2 involutionTwoCore] :
    (Subgroup.quotientAut (Subgroup.center involutionTwoCore)).ker =
      (MulAut.conj (G := involutionTwoCore)).range :=
  extraspecial_quotientAut_ker_eq_inner

/-- A coordinate change preserves the kernel, which is exactly the inner group. -/
theorem matrixAction_ker [IsExtraspecial 2 involutionTwoCore] (e : Coordinates) :
    (matrixAction e).ker = (MulAut.conj (G := involutionTwoCore)).range := by
  rw [← quotientAut_ker_eq_inner]
  ext a
  exact map_eq_one_iff ((MulAut.congr e).trans binaryAutMatrix)
    ((MulAut.congr e).trans binaryAutMatrix).injective

/-- Only the order of the center remains once the quotient coordinates are supplied. -/
theorem extraspecial_of_coordinates
    (hcenter : Nat.card (Subgroup.center involutionTwoCore) = 2)
    (e : Coordinates) : IsExtraspecial 2 involutionTwoCore := by
  refine ⟨hcenter, ?_, e.surjective.nontrivial⟩
  refine { toIsMulCommutative := ⟨⟨fun x y => e.injective (by simp [mul_comm])⟩⟩
           exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro x
  apply e.injective
  rw [map_pow, map_one]
  change (2 : ℕ) • (e x).toAdd = 0
  rw [← Nat.cast_smul_eq_nsmul (ZMod 2)]
  exact zero_smul (ZMod 2) (e x).toAdd

/-- Conjugation by C on Q/Z(Q), expressed in the supplied coordinates. -/
def localAction (e : Coordinates) : involutionCentralizer →* TwoCoreLinearModel.Matrix12ˣ :=
  (matrixAction e).comp involutionTwoCoreAction

/-- The coordinate vector of the coset of an element of Q. -/
@[expose] def vector (e : Coordinates) (q : involutionTwoCore) : Vector :=
  (e (QuotientGroup.mk' (Subgroup.center involutionTwoCore) q)).toAdd

theorem vector_surjective (e : Coordinates) : Function.Surjective (vector e) := by
  intro v
  obtain ⟨q, hq⟩ := QuotientGroup.mk'_surjective (Subgroup.center involutionTwoCore)
    (e.symm (Multiplicative.ofAdd v))
  exact ⟨q, by simp [vector, hq]⟩

/-- Concrete coordinates and two generators modulo Q, with their exact conjugation matrices.
No center order, automorphism-kernel bound, or image equality is a field. -/
structure ActionGenerators where
  coordinates : Coordinates
  first : involutionCentralizer
  second : involutionCentralizer
  generate : Subgroup.closure ({first, second} : Set involutionCentralizer) ⊔
    involutionTwoCore = ⊤
  first_action : ∀ q, TwoCoreLinearModel.matrixC *ᵥ vector coordinates q =
    vector coordinates (involutionTwoCoreAction first q)
  second_action : ∀ q, TwoCoreLinearModel.matrixD *ᵥ vector coordinates q =
    vector coordinates (involutionTwoCoreAction second q)

/-- Pointwise coordinate identities identify the entire matrix unit. -/
theorem localAction_eq_of_mulVec (e : Coordinates) (c : involutionCentralizer)
    (u : TwoCoreLinearModel.Matrix12ˣ)
    (h : ∀ q, (u : TwoCoreLinearModel.Matrix12) *ᵥ vector e q =
      vector e (involutionTwoCoreAction c q)) : localAction e c = u := by
  apply Units.ext
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  obtain ⟨q, rfl⟩ := vector_surjective e v
  exact (matrixAction_mulVec e (involutionTwoCoreAction c) q).trans (h q).symm

theorem ActionGenerators.first_image (d : ActionGenerators) :
    localAction d.coordinates d.first = TwoCoreLinearModel.unitC :=
  localAction_eq_of_mulVec d.coordinates d.first TwoCoreLinearModel.unitC d.first_action

theorem ActionGenerators.second_image (d : ActionGenerators) :
    localAction d.coordinates d.second = TwoCoreLinearModel.unitD :=
  localAction_eq_of_mulVec d.coordinates d.second TwoCoreLinearModel.unitD d.second_action

/-- Inner automorphisms act trivially on the abelian central quotient. -/
theorem twoCore_le_localAction_ker [IsExtraspecial 2 involutionTwoCore] (e : Coordinates) :
    involutionTwoCore ≤ (localAction e).ker := by
  intro q hq
  change involutionTwoCoreAction q ∈ (matrixAction e).ker
  rw [matrixAction_ker]
  exact ⟨⟨q, hq⟩, MulAut.conjNormal_val.symm⟩

/-- Generation modulo Q and the two coordinate identities give the exact matrix image. -/
theorem ActionGenerators.localAction_range [IsExtraspecial 2 involutionTwoCore]
    (d : ActionGenerators) :
    (localAction d.coordinates).range = TwoCoreLinearModel.actionGroup := by
  rw [MonoidHom.range_eq_map, ← d.generate, Subgroup.map_sup,
    (Subgroup.map_eq_bot_iff involutionTwoCore).mpr
      (twoCore_le_localAction_ker d.coordinates), sup_bot_eq,
    MonoidHom.map_closure]
  simp only [Set.image_pair, d.first_image, d.second_image, TwoCoreLinearModel.actionGroup]

/-- The image clause in the comparison, for the actual conjugation homomorphism. -/
theorem ActionGenerators.map_range [IsExtraspecial 2 involutionTwoCore]
    (d : ActionGenerators) :
    involutionTwoCoreAction.range.map (matrixAction d.coordinates) =
      TwoCoreLinearModel.actionGroup :=
  (MonoidHom.map_range _ _).trans d.localAction_range

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreComparison
