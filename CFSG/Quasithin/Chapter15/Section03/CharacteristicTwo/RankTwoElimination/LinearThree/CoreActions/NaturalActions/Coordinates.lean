module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.Layers
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.Frattini
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases.Projection
public import Mathlib.Algebra.Module.ZMod

/-!
# Actual conjugation on the natural commutator core

The layer's multiplicative isomorphism transports ambient conjugation to a
binary representation. An element of the abelian core acts trivially there.
Since the residual's displacement on L lies in Q, its transported action
commutes with the whole SL₃(2) natural action under the given quotient marking.
This constructs the action and its commutation; it does not assume that the
residual centralizes L or Q.

Source: Aschbacher–Smith, proof of 15.3.23, printed p.1129, and the compatible
natural layers in C.1.34(1),(2), printed pp.136–137.
-/

@[expose] public section

open Subgroup Representation
open scoped commutatorElement
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.NaturalActions
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- Actual ambient conjugation written in additive coordinates. -/
noncomputable def coordinateAut {Q : Subgroup G} (e : Q ≃* Multiplicative V) :
    normalizer (Q : Set G) →* MulAut (Multiplicative V) :=
  (MulAut.congr e).toMonoidHom.comp Q.normalizerMonoidHom

noncomputable def coordinateAction {Q A : Subgroup G} (e : Q ≃* Multiplicative V)
    (hn : A ≤ normalizer (Q : Set G)) : Representation (ZMod 2) A V where
  toFun a := (AddMonoidHom.toMultiplicative.symm (coordinateAut e (inclusion hn a)).toMonoidHom).toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro v
    change coordinateAut e (inclusion hn 1) (Multiplicative.ofAdd v) = _
    rw [map_one, map_one]
    rfl
  map_mul' a b := by
    apply LinearMap.ext
    intro v
    change coordinateAut e (inclusion hn (a*b)) (Multiplicative.ofAdd v) = _
    rw [map_mul, map_mul]
    rfl

theorem coordinateAction_apply {Q A : Subgroup G} (e : Q ≃* Multiplicative V)
    (hn : A ≤ normalizer (Q : Set G)) (a : A) (q : Q) :
    coordinateAction e hn a (Multiplicative.toAdd (e q)) =
      Multiplicative.toAdd (e (layerConjugate A Q hn a q)) := by
  change Multiplicative.toAdd (e (Q.normalizerMonoidHom (inclusion hn a) (e.symm (e q)))) = _
  rw [e.symm_apply_apply]
  rfl

omit [Module (ZMod 2) V] in
private lemma coordinateAut_core {Q : Subgroup G} (e : Q ≃* Multiplicative V)
    (x : normalizer (Q : Set G)) (hx : (x : G) ∈ Q) : coordinateAut e x = 1 := by
  ext v
  obtain ⟨q, rfl⟩ := e.surjective v
  change e (Q.normalizerMonoidHom x (e.symm (e q))) = e q
  rw [e.symm_apply_apply]
  apply congrArg e
  apply Subtype.ext
  have hc : (x : G) * (q : G) = (q : G) * (x : G) :=
    congrArg Subtype.val (e.injective (show e ((⟨x, hx⟩ : Q) * q) = e (q * ⟨x, hx⟩) by
      simp only [map_mul, mul_comm]))
  change (x : G) * (q : G) * (x : G)⁻¹ = q
  rw [hc, mul_inv_cancel_right]

omit [Module (ZMod 2) V] in
/-- The section kernel commutes with the component on an abelian core.
The displacement is allowed in Q; centralization of L is not assumed. -/
theorem coordinateAut_commute {Q : Subgroup G} (e : Q ≃* Multiplicative V)
    (x y : normalizer (Q : Set G)) (hxy : ⁅(x : G), (y : G)⁆ ∈ Q) :
    Commute (coordinateAut e x) (coordinateAut e y) := by
  apply commutatorElement_eq_one_iff_commute.mp
  rw [← map_commutatorElement]
  exact coordinateAut_core e ⁅x,y⁆ hxy

variable {d : LocalData G} {I : Subgroup G} (c : ComponentWitness d I)
variable {a : ℕ} {e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}

/-- The actual residual action on the actual natural copies in Q. -/
noncomputable def residualAction
    (m : LayerModel c.L (commutatorCore c.L) ⊥ e (NaturalCopies (ZMod 2) a)) :
    Representation (ZMod 2) (YC d c.L) (Fin a → Fin 3 → ZMod 2) :=
  coordinateAction m.upperIso ((YC_section_action d c.L).1.trans
    (normalizer_le_normalizer_commutatorCore c.L))

/-- The quotient marking of the natural layer makes the residual action
commute with the whole literal SL₃(2) action. -/
theorem residualAction_commutes
    (m : LayerModel c.L (commutatorCore c.L) ⊥ e (NaturalCopies (ZMod 2) a))
    (y : YC d c.L) (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (v : Fin a → Fin 3 → ZMod 2) :
    residualAction c m y (NaturalCopies (ZMod 2) a g v) =
      NaturalCopies (ZMod 2) a g (residualAction c m y v) := by
  obtain ⟨l, hl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 c.L))) g
  change e (QuotientGroup.mk' (pCore 2 c.L) l) = g at hl
  let ny : normalizer (commutatorCore c.L : Set G) :=
    ⟨y, ((YC_section_action d c.L).1.trans (normalizer_le_normalizer_commutatorCore c.L)) y.property⟩
  let nl : normalizer (commutatorCore c.L : Set G) := ⟨l, m.normalized l.property⟩
  have hh := coordinateAut_commute m.upperIso ny nl
    (YC_commutator_le d c (commutator_mem_commutator y.property l.property))
  have ht (w : Fin a → Fin 3 → ZMod 2) :
      coordinateAut m.upperIso nl (Multiplicative.ofAdd w) =
        Multiplicative.ofAdd (NaturalCopies (ZMod 2) a g w) := by
    obtain ⟨u, rfl⟩ := m.upperIso.surjective (Multiplicative.ofAdd w)
    change m.upperIso ((commutatorCore c.L).normalizerMonoidHom nl (m.upperIso.symm (m.upperIso u))) = _
    rw [m.upperIso.symm_apply_apply]
    have hi := m.upperIso_intertwining l u
    rw [hl] at hi
    exact congrArg Multiplicative.ofAdd hi
  have h := congrArg (fun f : MulAut (Multiplicative (Fin a → Fin 3 → ZMod 2)) =>
    f (Multiplicative.ofAdd v)) hh.eq
  change coordinateAut m.upperIso ny (coordinateAut m.upperIso nl (Multiplicative.ofAdd v)) =
    coordinateAut m.upperIso nl (coordinateAut m.upperIso ny (Multiplicative.ofAdd v)) at h
  rw [ht v] at h
  change coordinateAut m.upperIso ny (Multiplicative.ofAdd (NaturalCopies (ZMod 2) a g v)) =
    coordinateAut m.upperIso nl (Multiplicative.ofAdd (residualAction c m y v)) at h
  rw [ht] at h
  exact congrArg Multiplicative.toAdd h
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.NaturalActions
