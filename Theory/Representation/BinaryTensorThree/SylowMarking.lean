module
public import Theory.Representation.BinaryTensorThree.SylowNonFF
public import Theory.Representation.BinaryOffender.SylowTransport
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Sylow markings in the full binary tensor action

The full general-linear wreath product maps onto the tensor group generated
by the two factors and interchange. The dihedral wreath square embeds in it
with index 441, so its image is a Sylow two-subgroup. The existing small
model acts faithfully, as a check on the nine basis vectors shows. Sylow
conjugacy now extends its non-FF theorem to the full tensor action.

For an arbitrary two-group acting through this full tensor group, the same
conjugacy constructs a homomorphism into the small model and transports the
module equivalence. No chosen Sylow coordinates or injectivity of the original
acting-group map is required. The source adapter applies this to the actual
induced automizer, retaining the original conjugation kernel.

Source: Aschbacher--Smith H.4.8(4) and H.4.10--11,
printed pp.383--384; applied in the original 8.3.13--14.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open BinaryPermutation.FiveTensorSquare
namespace BinaryTensorThree
instance : Finite Factor :=
  Finite.of_injective (fun g : Factor => (g : Natural → Natural))
    (fun _ _ h => LinearEquiv.ext (congrFun h))
abbrev Wreath := RegularWreathProduct Factor C2

/-- The full tensor wreath action, in the existing generated matrix group. -/
noncomputable def wreathMap (w : Wreath) : Group :=
  if w.right = 1 then baseEmbedding (w.left 1,w.left swapIndex)
  else baseEmbedding (w.left 1,w.left swapIndex) * swap

/-- The natural map from the abstract wreath product onto the tensor group. -/
noncomputable def wreathHom : Wreath →* Group where
  toFun := wreathMap
  map_one' := by
    simp only [wreathMap,RegularWreathProduct.one_right,ite_true,
      RegularWreathProduct.one_left,Pi.one_apply]
    exact baseEmbedding.map_one
  map_mul' a b := by
    apply action_faithful
    ext X i j
    change action (wreathMap (a*b)) X i j = action (wreathMap a) (action (wreathMap b) X) i j
    rcases index_cases a.right with ha|ha <;> rcases index_cases b.right with hb|hb <;>
      simp [wreathMap,RegularWreathProduct.mul_left,RegularWreathProduct.mul_right,
        ha,hb,Module.End.mul_apply,flip_baseAction,Small.baseAction_mul_apply]

noncomputable def wreathBase (a : Factor × Factor) : Wreath :=
  ⟨fun i => if i=1 then a.1 else a.2,1⟩

theorem wreathHom_base (a : Factor × Factor) : wreathHom (wreathBase a) = baseEmbedding a := by
  simp [wreathHom,wreathMap,wreathBase]

noncomputable def wreathSwap : Wreath := ⟨1,swapIndex⟩

theorem wreathHom_swap : wreathHom wreathSwap = swap := by
  simp [wreathHom,wreathMap,wreathSwap]
  exact baseEmbedding.map_one

/-- The two factors and their interchange generate the entire tensor group. -/
theorem wreathHom_surjective : Function.Surjective wreathHom := by
  intro x
  have hall (y : Space ≃ₗ[ZMod 2] Space) (hy : y ∈ tensorGroup) :
      ∃ w, (wreathHom w).val = y := by
    induction hy using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with ⟨a,rfl⟩ | hg
      · exact ⟨wreathBase a,congrArg Subtype.val (wreathHom_base a)⟩
      · obtain rfl : g = flip := hg
        exact ⟨wreathSwap,congrArg Subtype.val wreathHom_swap⟩
    | one => exact ⟨1,by simp⟩
    | mul a b ha hb ia ib =>
      obtain ⟨u,rfl⟩ := ia
      obtain ⟨v,rfl⟩ := ib
      exact ⟨u*v,by simp⟩
    | inv a ha ia =>
      obtain ⟨u,rfl⟩ := ia
      exact ⟨u⁻¹,by simp⟩
  obtain ⟨w,hw⟩ := hall x.val x.property
  exact ⟨w,Subtype.ext hw⟩

namespace Small

/-- The checked small Sylow action as a homomorphism into the tensor group. -/
noncomputable def toTensorHom : P →* BinaryTensorThree.Group where
  toFun := toTensor
  map_one' := by
    apply action_faithful
    exact actionSmall.map_one
  map_mul' a b := by
    apply action_faithful
    exact actionSmall.map_mul a b

/-- The small tensor action is faithful, checked on its nine basis vectors. -/
theorem toTensorHom_injective : Function.Injective toTensorHom := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro g hg
  have hfix : ∀ k : Fin 9, act g (unit k) = unit k := by
    intro k
    rw [act_eq]
    change action (toTensorHom g) _ = _
    rw [show toTensorHom g = 1 from hg,map_one]
    rfl
  exact (by decide +kernel : ∀ g : P,
    (∀ k : Fin 9, act g (unit k) = unit k) → g = 1) g hfix

def naturalHom : D8 →* Factor where
  toFun := naturalEquiv
  map_one' := naturalEquiv_one
  map_mul' := naturalEquiv_mul

theorem naturalHom_injective : Function.Injective naturalHom := by
  intro g h he
  have he' : ∀ x, natural g x = natural h x := fun x =>
    congrArg (fun e : Factor => e x) he
  exact (by decide +kernel : ∀ g h : D8, (∀ x, natural g x = natural h x) → g = h) g h he'

def wreathEmbedding : P →* Wreath where
  toFun g := ⟨fun i => naturalHom (g.left i),g.right⟩
  map_one' := by ext i <;> simp
  map_mul' a b := by ext i <;> simp [RegularWreathProduct.mul_left,RegularWreathProduct.mul_right]

theorem wreathEmbedding_injective : Function.Injective wreathEmbedding := by
  intro a b h
  apply RegularWreathProduct.ext
  · funext i
    apply naturalHom_injective
    exact congrArg (fun w : Wreath => w.left i) h
  · exact congrArg (fun w : Wreath => w.right) h

theorem wreathHom_comp : wreathHom.comp wreathEmbedding = toTensorHom := by
  ext g
  rfl

noncomputable def wreathSylow : Sylow 2 Wreath := by
  have hc : Nat.card wreathEmbedding.range = 128 :=
    (Nat.card_congr (MonoidHom.ofInjective wreathEmbedding_injective).toEquiv).symm.trans
      BinaryPermutation.FiveTensorSquare.Small.card_P
  have hw : Nat.card Wreath = 56448 := by
    rw [RegularWreathProduct.card]
    have hF : Nat.card Factor = 168 := by
      rw [← Nat.card_congr ((Matrix.GeneralLinearGroup.toLin (n := Fin 3) (R := ZMod 2)).trans
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Natural)).toEquiv,
        Matrix.card_GL_field]
      norm_num [Fin.prod_univ_succ]
    have hC : Nat.card C2 = 2 := Nat.card_zmod 2
    rw [hF,hC]
    decide
  have hi : wreathEmbedding.range.index = 441 := by
    have h := wreathEmbedding.range.card_mul_index
    rw [hc,hw] at h
    omega
  exact (IsPGroup.of_card (p := 2) (n := 7) hc).toSylow (by rw [hi];decide)

/-- The image of the dihedral wreath square is Sylow in the tensor group. -/
noncomputable def tensorSylow : Sylow 2 BinaryTensorThree.Group :=
  wreathSylow.mapSurjective wreathHom_surjective

theorem tensorSylow_coe : (tensorSylow : Subgroup BinaryTensorThree.Group) = toTensorHom.range := by
  change wreathEmbedding.range.map wreathHom = toTensorHom.range
  rw [MonoidHom.map_range,wreathHom_comp]

end Small

/-- Sylow conjugacy extends the checked non-FF result to the whole tensor group. -/
theorem action_notFF : ¬ IsFFModule action := by
  rintro ⟨A,hA⟩
  obtain ⟨B,hB,hr,hc⟩ := elementary_geometry_of_sylow_range
    Small.actionSmall action Small.toTensorHom Small.toTensorHom_injective
    (LinearEquiv.refl (ZMod 2) Space) (fun _ _ => rfl)
    Small.tensorSylow Small.tensorSylow_coe.le A hA.1
  exact Small.notFF ⟨B,hB,by rw [hc,hr];exact hA.2⟩

/-- Conjugate any original two-group action into the checked Sylow model,
transporting the module coordinates by the same conjugator. -/
theorem exists_twoGroup_coordinates
    {H V : Type*} [_root_.Group H]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) H V) (hH : IsPGroup 2 H)
    (q : H →* Group) (e : V ≃ₗ[ZMod 2] Space)
    (he : ∀ h v, e (ρ h v) = action (q h) (e v)) :
    ∃ (f : H →* Small.P) (b : V ≃ₗ[ZMod 2] Space),
      ∀ h v, b (ρ h v) = Small.actionSmall (f h) (b v) := by
  have hq : IsPGroup 2 q.range := hH.of_surjective q.rangeRestrict q.rangeRestrict_surjective
  obtain ⟨P,hP⟩ := hq.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Group P Small.tensorSylow
  let c := (MulAut.conj g).toMonoidHom.comp q
  have hc : c.range ≤ Small.toTensorHom.range := by
    rw [←Small.tensorSylow_coe]
    have hp := congrArg Sylow.toSubgroup hg
    rw [←hp]
    rw [MonoidHom.range_comp]
    exact Subgroup.map_mono hP
  let f : H →* Small.P :=
    (MonoidHom.ofInjective Small.toTensorHom_injective).symm.toMonoidHom.comp
      (c.codRestrict Small.toTensorHom.range (fun h => hc ⟨h,rfl⟩))
  have hf (h : H) : Small.toTensorHom (f h) = g * q h * g⁻¹ := by
    exact congrArg Subtype.val
      ((MonoidHom.ofInjective Small.toTensorHom_injective).apply_symm_apply
        ⟨c h,hc ⟨h,rfl⟩⟩)
  let b := e.trans (LinearEquiv.ofBijective (action g) (action.apply_bijective g))
  refine ⟨f,b,fun h v => ?_⟩
  change action g (e (ρ h v)) = action (Small.toTensorHom (f h)) (action g (e v))
  rw [he,hf]
  simp only [←Module.End.mul_apply,←map_mul,mul_assoc,inv_mul_cancel,mul_one]

end BinaryTensorThree

