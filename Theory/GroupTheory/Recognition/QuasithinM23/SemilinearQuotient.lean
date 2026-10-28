module
public import Theory.Representation.SL2FourNaturalOrbits.SemilinearNormalizer.Normalizer
public import Theory.SpecificGroups.SL2.Affine.Core
/-!
# Recognizing the full natural semilinear quotient

Transport the actual special affine group through a field equivalence.
For a binary action whose kernel is U and whose marked normal subgroup
has exactly the natural SL₂(4) image, the action of X/U lies in the exact
semilinear normalizer. Its order 360 makes the inclusion surjective.
The resulting ΓL₂(4) equivalence retains the given action pointwise.

Source application: Aschbacher–Smith 5.2.11(3), printed pp.653–654
(`refs/quasithin.pdf`). The source consumer constructs the action, kernel,
and marked image from its original affine local and two-core.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.QuasithinM23
open Representation.SL2FourNatural
open Representation.SL2FourNatural.SemilinearNormalizer

/-- Coefficient transport of the actual special affine group. -/
def affineFieldEquiv {E K : Type*} [Field E] [Field K] (a : E ≃+* K) :
    Matrix.SL2.Affine E ≃* Matrix.SL2.Affine K := by
  let v : Multiplicative (Fin 2 → E) ≃* Multiplicative (Fin 2 → K) := {
    toFun := fun x => Multiplicative.ofAdd (fun i => a (x.toAdd i))
    invFun := fun x => Multiplicative.ofAdd (fun i => a.symm (x.toAdd i))
    left_inv := fun x => by ext i; exact a.symm_apply_apply _
    right_inv := fun x => by ext i; exact a.apply_symm_apply _
    map_mul' := fun x y => by ext i; exact a.map_add _ _ }
  let s : Matrix.SpecialLinearGroup (Fin 2) E ≃* Matrix.SpecialLinearGroup (Fin 2) K := {
    Matrix.SpecialLinearGroup.map a.toRingHom with
    invFun := Matrix.SpecialLinearGroup.map a.symm.toRingHom
    left_inv := fun x => by ext i j; exact a.symm_apply_apply _
    right_inv := fun x => by ext i j; exact a.apply_symm_apply _ }
  exact SemidirectProduct.congr v s (by
    intro g
    ext x i
    change a (∑ j, g.val i j * x.toAdd j) = ∑ j, a (g.val i j) * a (x.toAdd j)
    simp only [map_sum,map_mul])

/-- Multiplicative automorphisms of a binary vector group are binary linear. -/
def binaryAutEquiv : MulAut (Multiplicative V) ≃* BinaryGL where
  toFun g :=
    let b : V ≃+ V := {
      toFun := fun x => (g (Multiplicative.ofAdd x)).toAdd
      invFun := fun x => (g.symm (Multiplicative.ofAdd x)).toAdd
      left_inv := fun x => g.symm_apply_apply x
      right_inv := fun x => g.apply_symm_apply x
      map_add' := fun x y => g.map_mul x y }
    b.toLinearEquiv (fun c v => ZMod.map_smul b.toAddMonoidHom c v)
  invFun g := g.toAddEquiv.toMultiplicative
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem binaryAutEquiv_apply (g : MulAut (Multiplicative V)) (v : V) :
    binaryAutEquiv g v = (g (Multiplicative.ofAdd v)).toAdd := by rfl

/-- A faithful quotient action containing the natural SL₂ and of full order
is the whole semilinear normalizer; it retains the given action pointwise. -/
theorem gamma_quotient_of_natural_image
    {X : Type*} [Group X] [Finite X]
    (U K : Subgroup X) [U.Normal] [K.Normal]
    (a : X →* BinaryGL) (hk : a.ker = U)
    (hK : K.map a = action.range) (hc : Nat.card (X ⧸ U) = 360) :
    ∃ e : (X ⧸ U) ≃* Gamma,
      (∀ x : X, natural (e (QuotientGroup.mk' U x)) = a x) ∧
      K.map (e.toMonoidHom.comp (QuotientGroup.mk' U)) = special.range := by
  have hn : ∀ x : X, a x ∈ normalizer := by
    intro x
    change a x ∈ Subgroup.normalizer (action.range : Set BinaryGL)
    rw [←hK]
    exact K.le_normalizer_map a (mem_map_of_mem a (le_normalizer_of_normal (mem_top x)))
  let b : X →* normalizer := a.codRestrict normalizer hn
  have hb : b.ker = U := by
    ext x
    change (⟨a x,hn x⟩ : normalizer) = 1 ↔ x ∈ U
    rw [Subtype.ext_iff]
    exact show a x = 1 ↔ x ∈ U from by rw [←hk]; rfl
  let c : X ⧸ U →* normalizer := QuotientGroup.lift U b hb.ge
  have hi : Function.Injective c := (QuotientGroup.injective_lift_iff _ _ _).mpr hb.symm
  have hcard : Nat.card normalizer = 360 :=
    (Nat.card_congr normalizerEquiv.symm.toEquiv).trans gamma_card
  let : Finite normalizer := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  let e := (MulEquiv.ofBijective c ((Nat.bijective_iff_injective_and_card c).mpr
    ⟨hi,hc.trans hcard.symm⟩)).trans normalizerEquiv.symm
  have he (x : X) : natural (e (QuotientGroup.mk' U x)) = a x := by
    change (normalizerEquiv (normalizerEquiv.symm (b x)) : BinaryGL) = a x
    rw [normalizerEquiv.apply_symm_apply]
    rfl
  refine ⟨e,he,?_⟩
  apply Subgroup.map_injective natural_injective
  rw [map_map]
  have hh : natural.comp (e.toMonoidHom.comp (QuotientGroup.mk' U)) = a := MonoidHom.ext he
  rw [hh,hK,←MonoidHom.range_comp]
  exact congrArg MonoidHom.range (MonoidHom.ext natural_special).symm
end Theory.GroupTheory.QuasithinM23
