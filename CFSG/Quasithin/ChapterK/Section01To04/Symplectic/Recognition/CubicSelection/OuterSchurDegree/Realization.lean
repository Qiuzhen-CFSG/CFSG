module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.CubicSelection.OuterSchurDegree.Realization.Coordinates

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.CubicSelection.OuterSchurDegree.Realization.Paired

/-!
# Realization of an actual outer Schur-linear involution as tensor interchange

On the original component's absolute module, the tensor catalogue is invariant
under the half-order graph power. Pair its factors and conjugate the second
half by the matrix giving the actual actor's inner twist. The component then
acts by the tensor product of a half representation and its conjugate under
the actual ambient involution. Schur's lemma identifies that involution with
interchange, and faithfulness detects every nonidentity commuting inner
involution. Every coordinate map is constructed over the original Schur-field
closure; no support-selection, degree bound or group cocycle descent is assumed.

Source: Guralnick--Malle, Classification of 2F-modules II, Section 3.5 and
Proposition 6.2(2--3), manuscript pp.20,39--40; Aschbacher--Smith K.3.4,
printed pp.451,456--457.
-/

public section

open Representation Representation.FrobeniusTensor Fin.NatCast
open scoped TensorProduct
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Nonbinary

namespace CFSG.Quasithin.ChapterK.Symplectic.Recognition.OuterSchur

variable {G V F : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [Field F] [Finite F] [Algebra (ZMod 2) F]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- Pair the literal component tensor factors, absorbing the inner twist on the second half. -/
theorem source_pairedTensorCoordinates {K : GroupClass} (h : SourceHypothesis K ρ L)
    [Representation.IsIrreducible (ρ.comp L.subtype)] [L.Normal]
    {r : ℕ} (hr : 1 < r) (hF : Nat.card F = 2^r)
    (d : L ≃* Derived F) (P : TensorParameters (ρ.comp L.subtype) d r)
    (t : G) (htL : t ∉ L) (ht2 : t^2 = 1) (ht : IsSchurLinear ρ L t) :
    Nonempty (PairedTensorCoordinates ρ L t) := by
  classical
  let : NeZero (2*r) := ⟨by omega⟩
  have hS := source_halfTurnSupport h hr hF d P t htL ht2 ht
  obtain ⟨x, hx, _⟩ := source_outer_twist h hr hF d t htL ht2
  obtain ⟨φ⟩ := P.equivalence
  let ψ := tensorModel_paired_equiv hF P.embedding P.support hS
  let η := (φ.trans ψ).toLinearEquiv
  let k := Closure (ρ.comp L.subtype)
  let W := (halfSupport P.support → Coordinate) → k
  let π : Representation k (Derived F) W := tensorModel P.embedding (halfSupport P.support)
  let n := Module.finrank k W
  let b : W ≃ₗ[k] (Fin n → k) := (Module.finBasis k W).equivFun
  let X : W ≃ₗ[k] W := LinearMap.GeneralLinearGroup.toLinearEquiv (π.asGroupHom x)
  have hX (v : W) : X v = π x v := rfl
  let C := TensorProduct.congr b (X.trans b)
  let half : Representation k L (Fin n → k) :=
    b.conjRingEquiv.toMonoidHom.comp (π.comp d.toMonoidHom)
  have hhalf (u : L) (v : W) : half u (b v) = b (π (d u) v) := by
    change b (π (d u) (b.symm (b v))) = _
    rw [b.symm_apply_apply]
  have hη (u : L) (v : AbsoluteSpace (ρ.comp L.subtype)) :
      η (absoluteRep (ρ.comp L.subtype) u v) =
        TensorProduct.map (π (d u)) (π ((graphDerived F ^ r) (d u))) (η v) := by
    have hh := IntertwiningMap.isIntertwining _ _ (φ.trans ψ).toIntertwiningMap (d u) v
    change η (absoluteRep (ρ.comp L.subtype) (d.symm (d u)) v) =
      TensorProduct.map (π (d u)) (π ((graphDerived F ^ r) (d u))) (η v) at hh
    simpa only [d.symm_apply_apply] using hh
  have hC (u : L) (z : W ⊗[k] W) :
      C (TensorProduct.map (π (d u)) (π ((graphDerived F ^ r) (d u))) z) =
        TensorProduct.map (half u) (half (MulAut.conjNormal t u)) (C z) := by
    have hm : π x * π ((graphDerived F ^ r) (d u)) =
        π (d (MulAut.conjNormal t u)) * π x := by
      calc
        π x * π ((graphDerived F ^ r) (d u)) = π (x * (graphDerived F ^ r) (d u)) :=
          (π.map_mul' _ _).symm
        _ = π (d (MulAut.conjNormal t u) * x) :=
          congrArg (fun g : Derived F => π g) (by rw [hx, inv_mul_cancel_right])
        _ = π (d (MulAut.conjNormal t u)) * π x := π.map_mul' _ _
    have he : C.toLinearMap ∘ₗ TensorProduct.map (π (d u))
        (π ((graphDerived F ^ r) (d u))) =
        TensorProduct.map (half u) (half (MulAut.conjNormal t u)) ∘ₗ C.toLinearMap := by
      apply TensorProduct.ext'
      intro v w
      change C (π (d u) v ⊗ₜ[k] π ((graphDerived F ^ r) (d u)) w) =
        TensorProduct.map (half u) (half (MulAut.conjNormal t u)) (C (v ⊗ₜ[k] w))
      simp only [C, TensorProduct.congr_tmul, LinearEquiv.trans_apply, hX,
        TensorProduct.map_tmul, hhalf]
      exact congrArg (fun w' : W => b (π (d u) v) ⊗ₜ[k] b w')
        (LinearMap.congr_fun hm w)
    exact LinearMap.congr_fun he z
  have hn : 4 ≤ n := by
    have hp : 0 < P.support.card := by
      rw [P.support_card]
      exact Nat.mul_pos P.factors_pos P.blocks_pos
    have hh : 0 < (halfSupport P.support).card :=
      Finset.card_pos.mpr (halfSupport_nonempty P.support hS (Finset.card_pos.mp hp))
    change 4 ≤ Module.finrank k ((halfSupport P.support → Coordinate) → k)
    rw [tensorModel_finrank]
    simpa using Nat.pow_le_pow_right (by decide : 0 < 4) hh
  refine ⟨⟨n, hn, half, η.trans C, ?_⟩⟩
  intro u v
  change C (η (absoluteRep (ρ.comp L.subtype) u v)) = _
  rw [hη, hC]
  rfl

/-- Every outer Schur-linear involution has the required actual tensor-swap realization.
In particular this applies with the full known-simple class in the source hypotheses. -/
theorem source_tensorSwapRealization {K : GroupClass} (h : SourceHypothesis K ρ L)
    {r : ℕ} (hr : 1 < r) (hF : Nat.card F = 2^r)
    (e : L ⧸ Subgroup.center L ≃* Sp F)
    (P : @TensorParameters F L V _ _ _ _ _ _ _ (ρ.comp L.subtype) h.irreducible
      (sourceDerivedEquiv h hr hF e) r)
    (t : G) (htL : t ∉ L) (ht2 : t^2 = 1) (ht : IsSchurLinear ρ L t) :
    letI := h.irreducible
    Nonempty (TensorSwapRealization ρ L t ht) := by
  let : Representation.IsIrreducible (ρ.comp L.subtype) := h.irreducible
  let : L.Normal := h.fitting ▸ inferInstance
  obtain ⟨Q⟩ := source_pairedTensorCoordinates h hr hF
    (sourceDerivedEquiv h hr hF e) P t htL ht2 ht
  exact tensorSwapRealization_of_pairedCoordinates h.faithful t ht ht2 Q

end CFSG.Quasithin.ChapterK.Symplectic.Recognition.OuterSchur
