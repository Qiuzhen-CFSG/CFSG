module

public import Theory.SpecificGroups.SymmetricSix.Parabolics
public import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic

/-!
# Three binary blocks in the actual syntheme stabilizer

Affine permutations of `Fin 3 × ZMod 2` give the wreath product C₂ wr S₃.
The coordinate `(i,b)` is the six-letter point `2*i+b`. The embedding is
injective, preserves `{01,23,45}`, and has the full stabilizer order. Its
even subgroup consists exactly of vectors whose three bits sum to zero.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, I.5.7,
printed pp. 420–421 (the local syntheme calculation in the proof).
-/

@[expose] public section

namespace Theory.SpecificGroups.SymmetricSix.SynthemeCalculation
abbrev Binary := Multiplicative (Fin 3 → ZMod 2)
abbrev Three := Equiv.Perm (Fin 3)

def permute : Three →* MulAut Binary where
  toFun g := {
    toFun := fun v => Multiplicative.ofAdd (fun i => v.toAdd (g⁻¹ i))
    invFun := fun v => Multiplicative.ofAdd (fun i => v.toAdd (g i))
    left_inv := by intro v; funext i; exact congrArg v.toAdd (g.symm_apply_apply i)
    right_inv := by intro v; funext i; exact congrArg v.toAdd (g.apply_symm_apply i)
    map_mul' := by intros; rfl }
  map_one' := by rfl
  map_mul' := by intros; rfl

abbrev Model := Binary ⋊[permute] Three
instance : Fintype Model := Fintype.ofEquiv (Binary × Three) SemidirectProduct.equivProd.symm

def letterEquiv : Fin 3 × ZMod 2 ≃ Letter := finProdFinEquiv

def coordinateHom : Model →* Equiv.Perm (Fin 3 × ZMod 2) where
  toFun g := {
    toFun := fun x => (g.right x.1, x.2 + g.left.toAdd (g.right x.1))
    invFun := fun x => (g.right⁻¹ x.1, x.2 - g.left.toAdd x.1)
    left_inv := by rintro ⟨i,b⟩; simp
    right_inv := by rintro ⟨i,b⟩; simp }
  map_one' := by ext ⟨i,b⟩ <;> simp
  map_mul' g h := by
    ext ⟨i,b⟩ <;> simp [permute, add_comm, add_left_comm]

def modelHom : Model →* S6 :=
  (Equiv.permCongrHom letterEquiv).toMonoidHom.comp coordinateHom

theorem modelHom_apply (g : Model) (i : Fin 3) (b : ZMod 2) :
    modelHom g (letterEquiv (i,b)) =
      letterEquiv (g.right i, b + g.left.toAdd (g.right i)) := by
  simp [modelHom, Equiv.permCongrHom, Equiv.permCongr, coordinateHom]

theorem modelHom_injective : Function.Injective modelHom := by
  intro g h he
  have hc : coordinateHom g = coordinateHom h := (Equiv.permCongrHom letterEquiv).injective he
  have hr : g.right = h.right := by
    apply Equiv.ext
    intro i
    exact congrArg Prod.fst (Equiv.congr_fun hc (i,0))
  apply SemidirectProduct.ext _ hr
  funext i
  change g.left.toAdd i = h.left.toAdd i
  have hi := congrArg Prod.snd (Equiv.congr_fun hc (g.right⁻¹ i,0))
  simpa [coordinateHom, hr] using hi

instance : DecidablePred (· ∈ synthemeStabilizer) := fun g =>
  inferInstanceAs (Decidable (baseSyntheme.image (fun t => t.image g) = baseSyntheme))

-- Only 48 explicit affine transformations are tested here.
theorem modelHom_mem : ∀ g, modelHom g ∈ synthemeStabilizer := by decide +kernel

def toStabilizer : Model →* synthemeStabilizer := modelHom.codRestrict _ modelHom_mem

theorem model_card : Nat.card Model = 48 := by
  rw [SemidirectProduct.card]
  norm_num [Binary, Three, Nat.card_eq_fintype_card, Fintype.card_perm]

noncomputable def modelEquiv : Model ≃* synthemeStabilizer :=
  MulEquiv.ofBijective toStabilizer
    ((Nat.bijective_iff_injective_and_card _).mpr ⟨fun _ _ h =>
      modelHom_injective (congrArg Subtype.val h), model_card.trans synthemeStabilizer_order.symm⟩)

/-- The literal even subgroup of the affine block-permutation model. -/
def evenModel : Subgroup Model := (alternatingGroup Letter).comap modelHom
instance : DecidablePred (· ∈ evenModel) := fun g =>
  inferInstanceAs (Decidable ((modelHom g).sign = 1))

theorem mem_evenModel : ∀ g : Model, g ∈ evenModel ↔
    g.left.toAdd 0 + g.left.toAdd 1 + g.left.toAdd 2 = 0 := by decide +kernel

def evenToStabilizer : evenModel →* a6SynthemeStabilizer :=
  ((modelHom.comp evenModel.subtype).codRestrict _ (fun g => g.2)).codRestrict _
    (fun g => modelHom_mem g.1)

theorem evenModel_card : Nat.card evenModel = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

noncomputable def evenModelEquiv : evenModel ≃* a6SynthemeStabilizer :=
  MulEquiv.ofBijective evenToStabilizer
    ((Nat.bijective_iff_injective_and_card _).mpr ⟨fun _ _ h =>
      Subtype.ext (modelHom_injective (congrArg (fun g : a6SynthemeStabilizer => g.val.val) h)),
      evenModel_card.trans a6SynthemeStabilizer_order.symm⟩)

/-- The three blocks, in the order `{01}`, `{23}`, `{45}`. -/
def block (i : Fin 3) : Finset Letter := ![pair 0 1, pair 2 3, pair 4 5] i

theorem block_injective : Function.Injective block := by decide +kernel

theorem blocks_baseSyntheme : Finset.univ.image block = baseSyntheme := by decide +kernel

theorem modelHom_blocks : ∀ (g : Model) (i : Fin 3),
    (block i).image (modelHom g) = block (g.right i) := by decide +kernel

end Theory.SpecificGroups.SymmetricSix.SynthemeCalculation
