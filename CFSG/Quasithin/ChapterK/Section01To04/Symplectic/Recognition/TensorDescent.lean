module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.SupportShape
public import Theory.Representation.SL3.BinaryFieldDescent.BaseChange
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.TensorDescent.Fields
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.TensorDescent.GraphPair

/-!
# Quadratic Schur-field tensor descent for K.3.4

For the one-factor, two-block catalogue branch, embed the original Schur
endomorphism field into the defining field as a quadratic subfield. Reapply
the absolute catalogue at an embedding compatible with this inclusion;
character periodicity again gives the two positions j,j+r. Noether--Deuring
descends the actual intertwiner to the defining field. The explicit pair
coordinates and graph-power comparison then identify its scalar extension
with the natural module tensored with its relative Frobenius twist.

`TensorParameters.tensor` constructs the algebra structure and every field of
`TensorIdentification`, including the actual group and module maps. The final
source application uses the literal component action. The independent
support-selection argument must establish factors = 1 and blocks = 2;
this module proves the complete descent under precisely that branch contract.

Source: Aschbacher--Smith, K.3.4, printed p.456/PDF p.467;
GLS3, Remark 2.8.8 and Examples 2.8.10(d).
-/

public section
open Representation Representation.FrobeniusTensor Fin.NatCast
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Nonbinary
open scoped TensorProduct
namespace CFSG.Quasithin.ChapterK.Symplectic.Recognition.TensorDescent
noncomputable section
variable {F K : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F] [Field K]

private theorem mapCoefficients_tensorModel {n : ℕ} (e : F →+* K)
    (S : Finset (Fin (2*n))) :
    mapCoefficients e (tensorModel (RingHom.id F) S) = tensorModel e S := by
  classical
  ext g : 1
  apply LinearMap.toMatrix'.injective
  rw [mapCoefficients_toMatrix]
  change ((LinearMap.toMatrix' ((tensorMatrix (RingHom.id F) S g).mulVecLin)).map e) =
    LinearMap.toMatrix' ((tensorMatrix e S g).mulVecLin)
  simp only [← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
  ext x y
  simp [tensorMatrix]

/-- Base change preserves the literal tensor coordinates. -/
private def tensorModel_baseChange [Algebra F K] {n : ℕ} (S : Finset (Fin (2*n))) :
    (extendScalars K (tensorModel (RingHom.id F) S)).Equiv
      (tensorModel (algebraMap F K) S) := by
  classical
  rw [← mapCoefficients_tensorModel (algebraMap F K) S]
  exact (extendScalarsMapCoefficientsEquiv (E := K) _).toRepresentationEquiv

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V) [ρ.IsIrreducible]

/-- Reapply the absolute catalogue at a chosen compatible embedding. -/
private theorem pair_at_embedding {d : D ≃* Derived F} {r : ℕ}
    (P : TensorParameters ρ d r) (hr : 1 < r) (hF : Nat.card F = 2^r)
    (ha : P.factors = 1) (ht : P.blocks = 2) (e : F →+* Closure ρ)
    [NeZero (2*r)] :
    ∃ j : Fin (2*r), Nonempty (Representation.Equiv ((absoluteRep ρ).comp d.symm.toMonoidHom)
      (tensorModel e {j, j + (r : Fin (2*r))})) := by
  classical
  let : Algebra (ZMod 2) (Closure ρ) := ZMod.algebra _ _
  let τ := (absoluteRep ρ).comp d.symm.toMonoidHom
  have hi : IsIrreducible τ :=
    (irreducible_comp_surjective_iff d.symm.toMonoidHom d.symm.surjective _).mpr inferInstance
  obtain ⟨S, ⟨φ⟩⟩ := exists_tensorModel_equiv e hF (by omega) τ hi
  obtain ⟨φ₀⟩ := P.equivalence
  have hcard : S.card = P.support.card := by
    apply Nat.pow_right_injective (by decide : 1 < 4)
    simpa only [tensorModel_finrank] using
      φ.toLinearEquiv.finrank_eq.symm.trans φ₀.toLinearEquiv.finrank_eq
  have hperiod : ∀ [NeZero (2*r)],
      rotateSupport (Module.finrank (ZMod 2) (SchurField ρ)) S = S := by
    intro _
    apply rotateSupport_eq_of_character_fixed hF e (absoluteTensorCatalogue e hF (by omega))
    intro g
    have hh := congrFun (char_iso φ) g
    rw [← hh]
    exact (character_pow_iff ρ _).mpr (dvd_refl _) (d.symm g)
  let Q : TensorParameters ρ d r := { P with
    embedding := e
    support := S
    support_card := hcard.trans P.support_card
    periodic := hperiod
    equivalence := ⟨φ⟩ }
  obtain ⟨j, hj⟩ := Q.half_support ha ht
  exact ⟨j, hj ▸ Q.equivalence⟩
end
end CFSG.Quasithin.ChapterK.Symplectic.Recognition.TensorDescent
namespace CFSG.Quasithin.ChapterK.Symplectic.Recognition
open TensorDescent
noncomputable section
variable {F D V : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
  [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V) [ρ.IsIrreducible]

/-- Quadratic tensor descent on the original component and original Schur field. -/
theorem TensorParameters.tensor {d : D ≃* Derived F} {r : ℕ}
    (P : TensorParameters ρ d r) (hr : 1 < r) (hF : Nat.card F = 2^r)
    (ha : P.factors = 1) (ht : P.blocks = 2) :
    ∃ a : Algebra (Symplectic.SchurField ρ) F, letI := a
      Nonempty (TensorIdentification ρ F
        (Module.finrank (ZMod 2) (Symplectic.SchurField ρ))) := by
  classical
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  let : NeZero (2*r) := ⟨by omega⟩
  let s := Module.finrank (ZMod 2) (Symplectic.SchurField ρ)
  have hs := P.half_degree ha ht
  let : Module.Finite (ZMod 2) (Symplectic.SchurField ρ) := Module.Finite.of_finite
  have hE : Nat.card (Symplectic.SchurField ρ) = 2^s := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hF' : Nat.card F = 2^(2*s) := by rw [hF, hs.2.1]
  obtain ⟨a, σ, hne, hinv, hdeg, hσ⟩ := exists_quadratic_extension hs.1 hE hF'
  let := a
  let : Module.Finite (Symplectic.SchurField ρ) F := Module.Finite.of_finite
  let f : F →ₐ[Symplectic.SchurField ρ] Closure ρ := IsAlgClosed.lift
  let : Algebra F (Closure ρ) := f.toRingHom.toAlgebra
  let : IsScalarTower (Symplectic.SchurField ρ) F (Closure ρ) :=
    IsScalarTower.of_algebraMap_eq (fun x => (f.commutes x).symm)
  obtain ⟨j, ⟨φ⟩⟩ := pair_at_embedding ρ P hr hF ha ht (algebraMap F (Closure ρ))
  let S : Finset (Fin (2*r)) := {j, j + (r : Fin (2*r))}
  let τ : Representation F D ((S → Coordinate) → F) :=
    (tensorModel (RingHom.id F) S).comp d.toMonoidHom
  let φD : (absoluteRep ρ).Equiv
      ((tensorModel (algebraMap F (Closure ρ)) S).comp d.toMonoidHom) :=
    .mk φ.toLinearEquiv (by
      intro g
      simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.symm_apply_apply] using φ.isIntertwining' (d g))
  obtain ⟨ψ⟩ : Nonempty ((extendScalars (Closure ρ) (tensorModel (RingHom.id F) S)).Equiv
      (tensorModel (algebraMap F (Closure ρ)) S)) :=
    ⟨tensorModel_baseChange (F := F) (K := Closure ρ) S⟩
  let ψD : (extendScalars (Closure ρ) τ).Equiv
      ((tensorModel (algebraMap F (Closure ρ)) S).comp d.toMonoidHom) :=
    .mk ψ.toLinearEquiv (fun g => ψ.isIntertwining' (d g))
  obtain ⟨η⟩ := BinaryFieldDescent.equiv_of_extendScalars
    (K := Closure ρ) (extendScalars F ρ.endFieldRep) τ
    ⟨(extendScalars_comp F ρ.endFieldRep).toRepresentationEquiv.trans
      (φD.trans ψD.symm)⟩
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact (by norm_num : 2 = 2^1) ▸ Nat.pow_lt_pow_right (by decide) hr
  let g := (graphDerived F ^ (j : ℕ)).trans (derivedEquivFull_of_card_gt_two hq)
  let ξ := pair_twisted_equiv hF hs.2.1 (by omega) hq σ.toRingEquiv hσ j
  let ξD : τ.Equiv ((twistedTensor σ.toRingEquiv).comp (d.trans g).toMonoidHom) :=
    .mk ξ.toLinearEquiv (fun x => ξ.isIntertwining' (d x))
  let θ := η.trans ξD
  refine ⟨a, ⟨⟨d.trans g, σ, hne, hinv, hdeg, hE, hF', θ.toLinearEquiv, ?_⟩⟩⟩
  intro x v
  exact IntertwiningMap.isIntertwining _ _ θ.toIntertwiningMap x v


/-- The repeated-pair branch on the literal K.3.4 component supplies all fields
of the published tensor identification. The source support-selection theorem
is responsible only for establishing the two displayed parameter equalities. -/
theorem source_tensorIdentification_of_repeated_pair
    {G : Type*} [Group G] [Finite G]
    {ρG : Representation (ZMod 2) G V} {L : Subgroup G}
    {K : GroupClass} (h : SourceHypothesis K ρG L)
    {r : ℕ} (hr : 1 < r) (hF : Nat.card F = 2^r)
    (e : L ⧸ Subgroup.center L ≃* Sp F) :
    letI := h.irreducible
    ∀ P : TensorParameters (ρG.comp L.subtype) (sourceDerivedEquiv h hr hF e) r,
      P.factors = 1 → P.blocks = 2 →
      ∃ a : Algebra (Symplectic.SchurField (ρG.comp L.subtype)) F, letI := a
        Nonempty (TensorIdentification (ρG.comp L.subtype) F
          (Module.finrank (ZMod 2) (Symplectic.SchurField (ρG.comp L.subtype)))) := by
  let : IsIrreducible (ρG.comp L.subtype) := h.irreducible
  intro P ha ht
  exact TensorParameters.tensor (ρG.comp L.subtype) P hr hF ha ht

end
end CFSG.Quasithin.ChapterK.Symplectic.Recognition
