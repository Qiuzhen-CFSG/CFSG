module
public import Theory.Representation.OrthogonalFourPlusMatrix.QuotientLocal.DiagonalCore
public import Theory.Representation.OrthogonalFourPlusMatrix.Comparison
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
/-!
# Marking the actual orthogonal component square

The checked determinant-model comparison and PSL₂(4) projective-line action
identify the existing PΩ₄⁺(4) carrier with A₅ × A₅. Conjugation on a normal
copy of this square is faithful when it is the generalized Fitting subgroup.
An involution exchanging the components can be straightened on the group
coordinates. Its fixed component subgroup then has the actual inner diagonal
image required by the core calculation.

Straightening the group coordinates does not identify the selected action on
the binary natural module with adjugation. The module action is retained by
its existing owner, and no displacement-rank inference is made here.

Source: Aschbacher–Smith G.11.2(7), 14.4.2(3), and 14.4.9, printed p.1010.
The orthogonal comparison reuses the attributed ATLAS-derived construction;
all new arguments here are structural group arguments.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.FourPlusMatrix.QuotientLocal
open Subgroup Theory.GroupTheory
/-- The actual determinant-one factor, identified through its projective line. -/
def factorAlternatingEquiv : Representation.SL2FourNatural.SL ≃* alternatingGroup (Fin 5) :=
  Atlas.RankOneFieldAutomorphisms.slEquivPSL.trans
    (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
      (by rw [Nat.card_eq_fintype_card, Representation.SL2FourNatural.card_field])).some

/-- The checked orthogonal carrier is the actual product of two A₅ groups. -/
def orthogonalAlternatingEquiv : POmegaPlus 2 Binary.F ≃*
    alternatingGroup (Fin 5) × alternatingGroup (Fin 5) :=
  Binary.orthogonalEquiv.symm.trans
    (factorAlternatingEquiv.prodCongr factorAlternatingEquiv)

variable {Q S : Type*} [Group Q] [Group S]
/-- The actual conjugation action on a marked product of components. -/
def componentAction (K : Subgroup Q) [K.Normal] (e : K ≃* S × S) :
    Q →* MulAut (S × S) := (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal

theorem componentAction_apply (K : Subgroup Q) [K.Normal] (e : K ≃* S × S)
    (g : Q) (s : S × S) :
    componentAction K e g s = e (MulAut.conjNormal g (e.symm s)) := rfl

theorem componentAction_injective (K : Subgroup Q) [K.Normal] (e : K ≃* S × S)
    (hK : centralizer (K : Set Q) = ⊥) : Function.Injective (componentAction K e) :=
  (MulAut.congr e).injective.comp (MulAut.conjNormal_injective_of_centralizer_eq_bot K hK)

theorem componentAction_on_K (K : Subgroup Q) [K.Normal] (e : K ≃* S × S)
    (k : K) : componentAction K e k = MulAut.conj (e k) := by
  apply MulEquiv.ext
  intro s
  change e (k * e.symm s * k⁻¹) = e k * s * (e k)⁻¹
  simp

/-- The whole inner square is in the image, with the prescribed coordinates. -/
theorem componentAction_inner_le_range (K : Subgroup Q) [K.Normal] (e : K ≃* S × S) :
    (MulAut.conj : S × S →* MulAut (S × S)).range ≤ (componentAction K e).range := by
  rintro _ ⟨s,rfl⟩
  refine ⟨(e.symm s : Q), ?_⟩
  rw [componentAction_on_K, e.apply_symm_apply]

/-- The selected involution fixes the diagonal group exactly. This is a
 statement about component conjugation, independent of its module action. -/
theorem componentAction_eq_swap (K : Subgroup Q) [K.Normal] (e : K ≃* S × S)
    (i : Q) (hi : ∀ k : K, e (MulAut.conjNormal i k) = ((e k).2, (e k).1)) :
    componentAction K e i = swap := by
  apply MulEquiv.ext
  intro s
  change e (MulAut.conjNormal i (e.symm s)) = (s.2,s.1)
  simpa only [e.apply_symm_apply] using hi (e.symm s)
/-- An involution exchanging the factors can be straightened on the group
 components. This coordinate change makes no assertion about its natural
 module action. -/
theorem straighten_exchange (a b : MulAut S)
    (h : (a.prodCongr b * (MulEquiv.prodComm : MulAut (S × S))) ^ 2 = 1) :
    MulAut.congr ((MulEquiv.refl S).prodCongr a)
      (a.prodCongr b * (MulEquiv.prodComm : MulAut (S × S))) = swap := by
  have hab (s : S) : a (b s) = s := by
    have hs := MulEquiv.congr_fun h (s,1)
    simpa [pow_two, MulEquiv.prodCongr] using congrArg Prod.fst hs
  apply MulEquiv.ext
  rintro ⟨x,y⟩
  apply Prod.ext
  · change a (a.symm y) = y
    exact a.apply_symm_apply y
  · change a (b x) = x
    exact hab x

/-- The generalized-Fitting hypothesis of G.11.2(7) supplies faithfulness
of the component action; no additional faithfulness certificate is needed. -/
theorem componentAction_injective_of_generalizedFitting [Finite Q]
    (K : Subgroup Q) [K.Normal] (e : K ≃* S × S)
    (hK : generalizedFitting Q = K) (hZ : center S = ⊥) :
    Function.Injective (componentAction K e) := by
  apply componentAction_injective
  apply eq_bot_iff.mpr
  intro g hg
  have hle : centralizer (K : Set Q) ≤ K :=
    hK ▸ centralizer_generalizedFitting_le Q
  have hz : e ⟨g,hle hg⟩ ∈ center (S × S) := by
    rw [mem_center_iff]
    intro a
    obtain ⟨k,rfl⟩ := e.surjective a
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (hg k k.property))
  have he : e ⟨g,hle hg⟩ = 1 := by
    simpa only [Subgroup.center_prod, hZ, bot_prod_bot, mem_bot] using hz
  exact congrArg Subtype.val (e.injective (he.trans e.map_one.symm))

/-- The fixed subgroup of the component square has precisely the inner
 diagonal image in coordinates straightened by the selected involution. -/
theorem fixed_component_image (K : Subgroup Q) [K.Normal] (e : K ≃* S × S)
    (i : Q) (hi : componentAction K e i = swap) :
    (K ⊓ centralizer ({i} : Set Q)).map (componentAction K e) = diagonalInner.range := by
  apply le_antisymm
  · rintro a ⟨g, ⟨hgK,hgi⟩,rfl⟩
    let k : K := ⟨g,hgK⟩
    have hk : MulAut.conjNormal i k = k := by
      apply Subtype.ext
      change i * g * i⁻¹ = g
      rw [← mem_centralizer_singleton_iff.mp hgi, mul_inv_cancel_right]
    have he : (e k).1 = (e k).2 := by
      have h := MulEquiv.congr_fun hi (e k)
      rw [componentAction_apply, e.symm_apply_apply, hk] at h
      exact congrArg Prod.fst h
    refine ⟨(e k).1, ?_⟩
    change diagonalInner (e k).1 = componentAction K e k
    rw [componentAction_on_K]
    exact congrArg MulAut.conj (Prod.ext rfl he)
  · rintro _ ⟨s,rfl⟩
    let k : K := e.symm (s,s)
    have hk : MulAut.conjNormal i k = k := by
      apply e.injective
      have h := MulEquiv.congr_fun hi (s,s)
      change e (MulAut.conjNormal i k) = (s,s) at h
      exact h.trans (e.apply_symm_apply (s,s)).symm
    refine ⟨(k : Q), ⟨k.property, ?_⟩, ?_⟩
    · apply mem_centralizer_singleton_iff.mpr
      have h := congrArg Subtype.val hk
      change i * (k : Q) * i⁻¹ = (k : Q) at h
      exact (mul_inv_eq_iff_eq_mul.mp h).symm
    · rw [componentAction_on_K]
      change MulAut.conj (e (e.symm (s,s))) = MulAut.conj (s,s)
      rw [e.apply_symm_apply]

end ClassicalOrthogonal.FourPlusMatrix.QuotientLocal
