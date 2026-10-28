module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Outer.Model
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Outer.Bounds
public import Theory.Representation.ScalarDescent
public import Theory.FieldTheory.BinaryTorusTwoPower

/-!
# Original-module transport for the symplectic tensor

Compose the published tensor coordinates with a supplied scalar-extension
identification of the Hermitian model, then apply Noether–Deuring descent.
This yields a Schur-field-linear representation equivalence retaining the
original component marking. No compatibility of the originally published
tensor equivalence with the Hermitian fixed form is assumed.

Every outer involution acts on the component as a conjugate, by an actual
symplectic matrix, of the coefficient-field involution. The cocycle descent
supplies that matrix. Comparing the original operator with the corresponding
linear model operator gives a commuting binary endomorphism, hence an element
of the actual Schur field. Squaring forces this element to be one in
characteristic two. This also proves scalar linearity of the original operator.

The final theorem is conditional only on the displayed model scalar-extension
equivalence and its intertwining identity. The model-geometry producer and the
outer-geometry assembly discharge this input; no fixed-dimension calculation
or complete K.3.4.2 conclusion is asserted here. The proved even-degree group
normal form makes an additional diagram-preservation premise unnecessary.

Source: Aschbacher–Smith, K.3.4.2, printed pp.456–457 (PDF pp.467–468),
with the comparison to H.4.4(6) made in the source proof.
-/

@[expose] public section

open scoped TensorProduct MonoidAlgebra
open Representation
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms
namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer.Transport
variable {D V F : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) D V)
  [ρ.IsIrreducible] [Field F] [Algebra (SchurField ρ) F]

/-- Descent of the supplied matrix coordinates, with the original group marking. -/
theorem original_equiv {s : ℕ} (h : TensorIdentification ρ F s)
    (eM : (F ⊗[SchurField ρ] Model.Space h.sigma h.sigma_involutive) ≃ₗ[F] Mat (F := F))
    (heM : ∀ g v, eM (extendScalars F (Model.action h.sigma h.sigma_involutive) g v) =
      matrixAction h.sigma.toRingEquiv g (eM v)) :
    Nonempty (ρ.endFieldRep ≃ₗ
      (Model.action h.sigma h.sigma_involutive).comp h.groupEquiv.toMonoidHom) := by
  let : Finite F := Nat.finite_of_card_ne_zero (h.field_card ▸ pow_ne_zero _ (by decide))
  let : Module.Finite (SchurField ρ) ρ.asModule :=
    Module.Finite.of_restrictScalars_finite (ZMod 2) (SchurField ρ) ρ.asModule
  let e := h.linearEquiv.trans (coordinates.trans eM.symm)
  apply repEquiv_of_extendScalars (S := F)
  refine ⟨RepEquiv.mk e ?_⟩
  intro g
  apply LinearMap.ext
  intro v
  apply eM.injective
  change eM (e (extendScalars F ρ.endFieldRep g v)) =
    eM (extendScalars F (Model.action h.sigma h.sigma_involutive) (h.groupEquiv g) (e v))
  simp only [e, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    h.intertwines, coordinates_action, heM]

end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer.Transport

open scoped MonoidAlgebra
open Representation
namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer.Transport
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) D V) [ρ.IsIrreducible]

private theorem involution_unique
    (T : ρ.asModule →ₗ[ZMod 2] ρ.asModule)
    (U : ρ.asModule ≃ₗ[SchurField ρ] ρ.asModule)
    (hT : Function.Involutive T) (hU : Function.Involutive U)
    (α : D ≃* D)
    (hTi : ∀ g x, T (ρ.endFieldRep g x) = ρ.endFieldRep (α g) (T x))
    (hUi : ∀ g x, U (ρ.endFieldRep g x) = ρ.endFieldRep (α g) (U x)) :
    ∀ x, T x = U x := by
  let q := (U.symm.restrictScalars (ZMod 2)).toLinearMap.comp T
  have hq (g : D) (x : ρ.asModule) :
      q (ρ.endFieldRep g x) = ρ.endFieldRep g (q x) := by
    apply U.injective
    change U (U.symm (T (ρ.endFieldRep g x))) = U (ρ.endFieldRep g (U.symm (T x)))
    rw [U.apply_symm_apply, hTi, hUi, U.apply_symm_apply]
  let a : SchurField ρ := {
    toFun := q
    map_add' := q.map_add
    map_smul' := by
      intro r x
      induction r using MonoidAlgebra.induction_linear with
      | zero => simp
      | add r s hr hs => simp only [add_smul, map_add, hr, hs]
      | single g b =>
        simp only [RingHom.id_apply, Representation.single_smul]
        change q (b • ρ.endFieldRep g x) = b • ρ.endFieldRep g (q x)
        rw [map_smul, hq] }
  have ha (x : ρ.asModule) : T x = a • U x := by
    have hh : a • x = U.symm (T x) := rfl
    have hh' := congrArg U hh
    rw [map_smul, U.apply_symm_apply] at hh'
    exact hh'.symm
  have hs : a * a = 1 := by
    ext x
    change a • (a • x) = x
    have he := hT x
    rw [ha, ha, map_smul, hU] at he
    exact he
  have hchar : CharP (SchurField ρ) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (SchurField ρ)).injective 2
  let := hchar
  have ha1 : a = 1 := by
    have he : a = 1 ∨ a = -1 := (mul_self_eq_one_iff).mp hs
    rcases he with he | he
    · exact he
    · simpa only [CharTwo.neg_eq] using he
  intro x
  simpa only [ha1, one_smul] using ha x
end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer.Transport

open Representation
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms
namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer.Transport
variable {D V F : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) D V)
  [ρ.IsIrreducible] [Field F] [Algebra (SchurField ρ) F]

/-- The published Galois involution is the unique half-degree Frobenius. -/
theorem sigma_eq_half_frobenius [Finite F] [CharP F 2]
    {s : ℕ} (h : TensorIdentification ρ F s) :
    h.sigma.toRingEquiv = frobeniusEquiv F 2 ^ s := by
  have hsq : h.sigma.toRingEquiv ^ 2 = 1 := by
    ext x
    exact h.sigma_involutive x
  have hne : h.sigma.toRingEquiv ≠ 1 := by
    intro he
    apply h.sigma_ne
    ext x
    exact DFunLike.congr_fun he x
  obtain ⟨m, hm, hn, he⟩ :=
    FiniteField.BinaryTorusTwoPower.involution_eq_half_frobenius h.field_card _ hsq hne
  have hm' : m = s := by omega
  subst m
  ext x
  rw [← iterateFrobeniusEquiv_eq_pow]
  exact he x

variable {G : Type*} [Group G] [Finite G]
  (ρG : Representation (ZMod 2) G V) (L : Subgroup G) [L.Normal]
  [IsIrreducible (ρG.comp L.subtype)]
  [Algebra (SchurField (ρG.comp L.subtype)) F]

/-- An actual symplectic conjugator for each outer involution. -/
theorem outer_group_normal_form {K : GroupClass}
    (hS : SourceHypothesis K ρG L) {s : ℕ} (hs : 0 < s)
    (h : TensorIdentification (ρG.comp L.subtype) F s)
    (t : G) (ht : orderOf t = 2) (hout : t ∉ L) :
    ∃ c : Sp F, extensionAction L h.groupEquiv.symm t =
      MulAut.conj c * fieldAutomorphism h.sigma.toRingEquiv * (MulAut.conj c)⁻¹ := by
  let : Finite F := Nat.finite_of_card_ne_zero (h.field_card ▸ pow_ne_zero _ (by decide))
  let : CharP (SchurField (ρG.comp L.subtype)) 2 := charP_of_injective_algebraMap
    (algebraMap (ZMod 2) (SchurField (ρG.comp L.subtype))).injective 2
  let : CharP F 2 := charP_of_injective_algebraMap
    (algebraMap (SchurField (ρG.comp L.subtype)) F).injective 2
  have hC := component_centralizer_eq_bot ρG L hS h.groupEquiv.symm
  let α := extensionAction L h.groupEquiv.symm
  have ho : orderOf (α t) = 2 :=
    (orderOf_injective α (extensionAction_injective L _ hC) t).trans ht
  have hi : α t ∉ MulAut.innerSubgroup (Sp F) :=
    fun hh => hout ((extensionAction_mem_inner_iff L _ hC t).mp hh)
  rcases involution_inner_or_twist h.field_card (by omega)
      SemilinearClassification.inner_field_of_preservesDiagram (α t) ho with ⟨g, hg, he⟩ | ⟨g, he, hg⟩
  · exact (hi ⟨g, he.symm⟩).elim
  · have heven : Even (2 * s) := even_two_mul s
    rw [graph_pow_eq_field_of_even heven, Nat.mul_div_cancel_left s (by decide : 0 < 2)] at he hg
    obtain ⟨c, hc⟩ := half_frobenius_cocycle_coboundary h.field_card (by omega) heven g (by simpa using hg)
    refine ⟨c, ?_⟩
    rw [sigma_eq_half_frobenius (ρG.comp L.subtype) h]
    exact he.trans (inner_twist_eq_conjugate _ g c (by simpa using hc))
end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer.Transport

open Representation
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer.Transport
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
  (σ : F ≃ₐ[k] F) (hσ : Function.Involutive σ)

/-- The linear involution obtained by conjugating the model field swap. -/
noncomputable def conjugatedSwap (c : Sp F) : Model.Space σ hσ ≃ₗ[k] Model.Space σ hσ where
  toFun x := Model.action σ hσ c (Model.fieldSwap σ hσ (Model.action σ hσ c⁻¹ x))
  invFun x := Model.action σ hσ c (Model.fieldSwap σ hσ (Model.action σ hσ c⁻¹ x))
  left_inv x := by
    dsimp only
    rw [Representation.inv_self_apply]
    have he := DFunLike.congr_fun (Model.fieldSwap_sq σ hσ) (Model.action σ hσ c⁻¹ x)
    change Model.fieldSwap σ hσ (Model.fieldSwap σ hσ (Model.action σ hσ c⁻¹ x)) =
      Model.action σ hσ c⁻¹ x at he
    rw [he, Representation.self_inv_apply]
  right_inv x := by
    dsimp only
    rw [Representation.inv_self_apply]
    have he := DFunLike.congr_fun (Model.fieldSwap_sq σ hσ) (Model.action σ hσ c⁻¹ x)
    change Model.fieldSwap σ hσ (Model.fieldSwap σ hσ (Model.action σ hσ c⁻¹ x)) =
      Model.action σ hσ c⁻¹ x at he
    rw [he, Representation.self_inv_apply]
  map_add' x y := by simp only [map_add]
  map_smul' a x := by simp only [map_smul, RingHom.id_apply]

theorem conjugatedSwap_involutive (c : Sp F) : Function.Involutive (conjugatedSwap σ hσ c) :=
  (conjugatedSwap σ hσ c).left_inv

theorem conjugatedSwap_action (c g : Sp F) (x : Model.Space σ hσ) :
    conjugatedSwap σ hσ c (Model.action σ hσ g x) =
      Model.action σ hσ
        ((MulAut.conj c * fieldAutomorphism σ.toRingEquiv * (MulAut.conj c)⁻¹) g)
        (conjugatedSwap σ hσ c x) := by
  change Model.action σ hσ c (Model.fieldSwap σ hσ (Model.action σ hσ c⁻¹ (Model.action σ hσ g x))) =
    Model.action σ hσ (c * fieldAutomorphism σ.toRingEquiv (c⁻¹ * g * c) * c⁻¹)
      (Model.action σ hσ c (Model.fieldSwap σ hσ (Model.action σ hσ c⁻¹ x)))
  simp only [map_mul, map_inv, Module.End.mul_apply, Model.fieldSwap_action,
    Representation.inv_self_apply, Representation.self_inv_apply]
end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer.Transport

open scoped TensorProduct
open Representation
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer.Transport
variable {G V F : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
  (L : Subgroup G) [L.Normal] [IsIrreducible (ρ.comp L.subtype)]
  [Field F] [Algebra (SchurField (ρ.comp L.subtype)) F]

/-- Every descended component equivalence identifies the original outer operator. -/
theorem outer_operator_of_equiv {K : GroupClass} (hS : SourceHypothesis K ρ L)
    {s : ℕ} (hs : 0 < s) (h : TensorIdentification (ρ.comp L.subtype) F s)
    (E : (Representation.endFieldRep (ρ.comp L.subtype)) ≃ₗ
      (Model.action h.sigma h.sigma_involutive).comp h.groupEquiv.toMonoidHom)
    (t : G) (ht : orderOf t = 2) (hout : t ∉ L) :
    ∃ c : Sp F, ∀ v : V,
      E ((Representation.asModuleEquiv (ρ.comp L.subtype)).symm (ρ t v)) =
        Model.action h.sigma h.sigma_involutive c
          (Model.fieldSwap h.sigma h.sigma_involutive
            (Model.action h.sigma h.sigma_involutive c⁻¹
              (E ((Representation.asModuleEquiv (ρ.comp L.subtype)).symm v)))) := by
  obtain ⟨c, hc⟩ := outer_group_normal_form ρ L hS hs h t ht hout
  let ρL : Representation (ZMod 2) L V := ρ.comp L.subtype
  let e := E.toLinearEquiv
  let C := conjugatedSwap h.sigma h.sigma_involutive c
  let U := e.trans (C.trans e.symm)
  let T := ρL.asModuleEquiv.symm.toLinearMap.comp ((ρ t).comp ρL.asModuleEquiv.toLinearMap)
  let α : L ≃* L := h.groupEquiv.trans ((extensionAction L h.groupEquiv.symm t).trans h.groupEquiv.symm)
  have hα (g : L) : h.groupEquiv (α g) = extensionAction L h.groupEquiv.symm t (h.groupEquiv g) :=
    h.groupEquiv.apply_symm_apply _
  have hconj (g : L) : (α g).val = t * g.val * t⁻¹ := by
    simpa only [α, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] using
      extensionAction_apply L h.groupEquiv.symm t (h.groupEquiv g)
  have he (g : L) (x : ρL.asModule) :
      e (ρL.endFieldRep g x) = Model.action h.sigma h.sigma_involutive (h.groupEquiv g) (e x) :=
    E.isIntertwining g x
  have hU : Function.Involutive U := by
    intro x
    change e.symm (C (e (e.symm (C (e x))))) = x
    rw [e.apply_symm_apply, conjugatedSwap_involutive, e.symm_apply_apply]
  have hUi (g : L) (x : ρL.asModule) :
      U (ρL.endFieldRep g x) = ρL.endFieldRep (α g) (U x) := by
    apply e.injective
    change e (e.symm (C (e (ρL.endFieldRep g x)))) =
      e (ρL.endFieldRep (α g) (e.symm (C (e x))))
    rw [e.apply_symm_apply, he, he, e.apply_symm_apply, hα, hc]
    exact conjugatedSwap_action h.sigma h.sigma_involutive c (h.groupEquiv g) (e x)
  have ht2 : t * t = 1 := by simpa only [← pow_two, ht] using pow_orderOf_eq_one t
  have hT : Function.Involutive T := by
    intro x
    change ρL.asModuleEquiv.symm (ρ t (ρL.asModuleEquiv
      (ρL.asModuleEquiv.symm (ρ t (ρL.asModuleEquiv x))))) = x
    rw [LinearEquiv.apply_symm_apply, ← Module.End.mul_apply, ← map_mul, ht2, map_one]
    exact ρL.asModuleEquiv.symm_apply_apply x
  have hTi (g : L) (x : ρL.asModule) :
      T (ρL.endFieldRep g x) = ρL.endFieldRep (α g) (T x) := by
    change ρL.asModuleEquiv.symm (ρ t (ρ g.val (ρL.asModuleEquiv x))) =
      ρL.asModuleEquiv.symm (ρ (α g).val (ρ t (ρL.asModuleEquiv x)))
    rw [hconj, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  have heq := involution_unique ρL T U hT hU α hTi hUi
  refine ⟨c, fun v => ?_⟩
  have hh := congrArg e (heq (ρL.asModuleEquiv.symm v))
  change e (ρL.asModuleEquiv.symm (ρ t (ρL.asModuleEquiv (ρL.asModuleEquiv.symm v)))) =
    e (e.symm (C (e (ρL.asModuleEquiv.symm v)))) at hh
  rw [LinearEquiv.apply_symm_apply, e.apply_symm_apply] at hh
  exact hh

/-- The outer involution is linear over the actual component Schur field. -/
theorem outer_operator_smul {K : GroupClass} (hS : SourceHypothesis K ρ L)
    {s : ℕ} (hs : 0 < s) (h : TensorIdentification (ρ.comp L.subtype) F s)
    (E : (Representation.endFieldRep (ρ.comp L.subtype)) ≃ₗ
      (Model.action h.sigma h.sigma_involutive).comp h.groupEquiv.toMonoidHom)
    (t : G) (ht : orderOf t = 2) (hout : t ∉ L)
    (a : SchurField (ρ.comp L.subtype)) (x : (Representation.asModule (ρ.comp L.subtype))) :
    (Representation.asModuleEquiv (ρ.comp L.subtype)).symm
        (ρ t ((Representation.asModuleEquiv (ρ.comp L.subtype)) (a • x))) =
      a • (Representation.asModuleEquiv (ρ.comp L.subtype)).symm
        (ρ t ((Representation.asModuleEquiv (ρ.comp L.subtype)) x)) := by
  obtain ⟨c, hc⟩ := outer_operator_of_equiv ρ L hS hs h E t ht hout
  apply E.toLinearEquiv.injective
  change E _ = E.toLinearEquiv (a • _)
  rw [E.toLinearEquiv.map_smul]
  change E _ = a • E _
  rw [hc, hc]
  simp only [LinearEquiv.symm_apply_apply]
  change (conjugatedSwap h.sigma h.sigma_involutive c)
    (E.toLinearEquiv (a • x)) = a • (conjugatedSwap h.sigma h.sigma_involutive c) (E x)
  rw [E.toLinearEquiv.map_smul]
  exact (conjugatedSwap h.sigma h.sigma_involutive c).map_smul a (E x)

omit [Finite G] [L.Normal] in
/-- One marked equivalence simultaneously transports all outer involutions.
The sole extra input is the model scalar-extension identification. -/
theorem original_equiv_outer {K : GroupClass} (hS : SourceHypothesis K ρ L)
    {s : ℕ} (hs : 0 < s) (h : TensorIdentification (ρ.comp L.subtype) F s)
    (eM : (F ⊗[SchurField (ρ.comp L.subtype)] Model.Space h.sigma h.sigma_involutive) ≃ₗ[F] Mat (F := F))
    (heM : ∀ g v, eM (extendScalars F (Model.action h.sigma h.sigma_involutive) g v) =
      matrixAction h.sigma.toRingEquiv g (eM v)) :
    ∃ E : (Representation.endFieldRep (ρ.comp L.subtype)) ≃ₗ
      (Model.action h.sigma h.sigma_involutive).comp h.groupEquiv.toMonoidHom,
      ∀ t : G, orderOf t = 2 → t ∉ L → ∃ c : Sp F, ∀ v : V,
        E ((Representation.asModuleEquiv (ρ.comp L.subtype)).symm (ρ t v)) =
          Model.action h.sigma h.sigma_involutive c
            (Model.fieldSwap h.sigma h.sigma_involutive
              (Model.action h.sigma h.sigma_involutive c⁻¹
                (E ((Representation.asModuleEquiv (ρ.comp L.subtype)).symm v)))) := by
  let : Finite G := hS.finite_group
  let : L.Normal := by rw [← hS.fitting]; infer_instance
  obtain ⟨E⟩ := original_equiv (ρ.comp L.subtype) h eM heM
  exact ⟨E, fun t ht hout => outer_operator_of_equiv ρ L hS hs h E t ht hout⟩
end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer.Transport
