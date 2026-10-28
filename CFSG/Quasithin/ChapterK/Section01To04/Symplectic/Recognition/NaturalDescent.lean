module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.Catalogue
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.NaturalSource

/-!
# Descending a singleton support to the K.3.4 natural identification

A one-factor absolute module with full Schur degree descends along the actual
Schur field. A finite-field isomorphism identifies that field with F. Applying
the catalogue at the compatible embedding and using Noether--Deuring descent
produces a binary intertwiner. The graph twist is absorbed by the marked group
isomorphism. Thus the result inhabits `NaturalIdentification`, including its
Schur-field map, rather than merely asserting the natural degree.

The descent argument is the one in the G.9 `BinaryDescent.Singleton` module,
here carried out on the original component to preserve its literal Schur field.
Source: Aschbacher--Smith K.3.4, printed p.456; GLS3, Remark 2.8.8.
-/

public section
namespace CFSG.Quasithin.ChapterK.Symplectic.Recognition
open Representation Representation.FrobeniusTensor
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Nonbinary

noncomputable section

variable {F E D ι : Type*} [Field F] [Field E] [Group D]
  [Algebra (ZMod 2) F] [Algebra (ZMod 2) E] [Fintype ι] [DecidableEq ι]

private def coefficientEquiv (h : F ≃ₐ[ZMod 2] E)
    (τ : Representation F D (ι → F)) :
    (restrictScalars (k := ZMod 2) τ).Equiv
      (restrictScalars (k := ZMod 2) (mapCoefficients h.toRingHom τ)) := by
  refine .mk (LinearEquiv.piCongrRight (fun _ : ι => h.toLinearEquiv)) ?_
  intro g
  apply LinearMap.ext
  intro v
  funext i
  change h (τ g v i) = mapCoefficients h.toRingHom τ g (fun j => h (v j)) i
  rw [← LinearMap.toMatrix'_mulVec (τ g) v,
    ← LinearMap.toMatrix'_mulVec (mapCoefficients h.toRingHom τ g), mapCoefficients_toMatrix]
  simp [Matrix.mulVec, dotProduct]

variable [Finite F] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V) [IsIrreducible ρ]

/-- Construct all maps in the published natural identification from full Schur
degree and absolute degree four. The complete catalogue is discharged here. -/
theorem naturalIdentification_of_schur_degree (d : D ≃* Derived F) {r : ℕ}
    (hr : 1 < r) (hF : Nat.card F = 2^r)
    (hs : Module.finrank (ZMod 2) (Symplectic.SchurField ρ) = r)
    (hd : Module.finrank (Closure ρ) (AbsoluteSpace ρ) = 4) :
    Nonempty (NaturalIdentification (F := F) ρ) := by
  classical
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  let : Fintype F := Fintype.ofFinite F
  let : Fintype (Symplectic.SchurField ρ) := Fintype.ofFinite _
  let : Module.Finite (ZMod 2) (Symplectic.SchurField ρ) := Module.Finite.of_finite
  have hc : Fintype.card F = Fintype.card (Symplectic.SchurField ρ) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Symplectic.SchurField ρ),
      Nat.card_zmod, hs, hF]
  let h : F ≃ₐ[ZMod 2] Symplectic.SchurField ρ := FiniteField.algEquivOfCardEq 2 hc
  let e : F →+* Closure ρ := (algebraMap (Symplectic.SchurField ρ) (Closure ρ)).comp h.toRingHom
  let ρ' := (absoluteRep ρ).comp d.symm.toMonoidHom
  have hi : IsIrreducible ρ' :=
    (irreducible_comp_surjective_iff d.symm.toMonoidHom d.symm.surjective _).mpr inferInstance
  obtain ⟨S, ⟨φ⟩⟩ := exists_tensorModel_equiv e hF (by omega) ρ' hi
  have hsize : 4 ^ S.card = 4^1 := by
    rw [← tensorModel_finrank (E := Closure ρ), ← φ.toLinearEquiv.finrank_eq, hd, pow_one]
  have hcard : S.card = 1 := Nat.pow_right_injective (by omega) hsize
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
  subst S
  let τ : Representation F D (Coordinate → F) := (basicTwist F j).comp d.toMonoidHom
  let σ := mapCoefficients h.toRingHom τ
  have hmap : mapCoefficients (algebraMap (Symplectic.SchurField ρ) (Closure ρ)) σ =
      mapCoefficients e τ := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.toMatrix'.injective
    simp only [σ, mapCoefficients_toMatrix, Matrix.map_map, e, RingHom.coe_comp]
  have hext : (extendScalars (Closure ρ) σ).Equiv (mapCoefficients e τ) := by
    rw [← hmap]
    exact (extendScalarsMapCoefficientsEquiv (E := Closure ρ) σ).toRepresentationEquiv
  let ψ := φ.trans (tensorModel_singleton_equiv e j)
  have ψ' : (absoluteRep ρ).Equiv (mapCoefficients e τ) :=
    .mk ψ.toLinearEquiv (by
      intro g
      have hh := ψ.isIntertwining' (d g)
      simpa only [ρ', τ, mapCoefficients, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.symm_apply_apply] using hh)
  obtain ⟨ψ₀⟩ := repEquiv_of_extendScalars (S := Closure ρ) ρ.endFieldRep σ
    ⟨RepEquiv.ofRepresentationEquiv (ψ'.trans hext.symm)⟩
  let η := ψ₀.toRepresentationEquiv
  let η₂ : ρ.Equiv (restrictScalars (k := ZMod 2) σ) :=
    .mk (ρ.asModuleEquiv.symm.trans (η.toLinearEquiv.restrictScalars (ZMod 2))) (by
      intro g
      apply LinearMap.ext
      intro v
      exact IntertwiningMap.isIntertwining ρ.endFieldRep σ η.toIntertwiningMap g
        (ρ.asModuleEquiv.symm v))
  let θ := η₂.trans (coefficientEquiv h τ).symm
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact (by norm_num : 2 = 2^1) ▸ Nat.pow_lt_pow_right (by decide) hr
  refine ⟨⟨(d.trans (graphDerived F ^ (j : ℕ))).trans (derivedEquivFull_of_card_gt_two hq),
    θ.toLinearEquiv, ?_, h.symm.toRingEquiv⟩⟩
  intro g v
  have hh := IntertwiningMap.isIntertwining ρ (restrictScalars (k := ZMod 2) τ)
    θ.toIntertwiningMap g v
  change θ.toLinearEquiv (ρ g v) =
    symplecticNatural 2 (((graphDerived F ^ (j : ℕ)) (d g)).val) (θ.toLinearEquiv v) at hh
  simpa only [MulEquiv.trans_apply, derivedEquivFull_of_card_gt_two_apply] using hh

/-- The singleton branch of the full catalogue supplies a genuine natural witness.
Selecting this branch from the ambient cubic hypothesis remains a separate step. -/
theorem TensorParameters.natural {d : D ≃* Derived F} {r : ℕ}
    (P : TensorParameters ρ d r) (hr : 1 < r) (hF : Nat.card F = 2^r)
    (ha : P.factors = 1) (ht : P.blocks = 1) :
    Nonempty (NaturalIdentification (F := F) ρ) := by
  obtain ⟨φ⟩ := P.equivalence
  apply naturalIdentification_of_schur_degree ρ d hr hF
  · simpa only [ht, mul_one] using P.field_degree.symm
  · rw [φ.toLinearEquiv.finrank_eq, tensorModel_finrank, P.support_card, ha, ht]
    norm_num

open scoped ENNReal
open Representation.BinaryOffender

/-- The singleton catalogue branch feeds the existing natural parabolic
calculation on the same original ambient action. -/
theorem source_natural_ratio_of_single_factor
    {G : Type*} [Group G] [Finite G]
    {ρG : Representation (ZMod 2) G V} {L : Subgroup G}
    {K : GroupClass} (h : SourceHypothesis K ρG L)
    {r : ℕ} (hr : 1 < r) (hF : Nat.card F = 2^r)
    (e : L ⧸ Subgroup.center L ≃* Sp F) :
    letI := h.irreducible
    ∀ P : TensorParameters (ρG.comp L.subtype) (sourceDerivedEquiv h hr hF e) r,
      P.factors = 1 → P.blocks = 1 → quadraticRatio ρG ≤ (2 : ℝ≥0∞) / 3 := by
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  let : IsIrreducible (ρG.comp L.subtype) := h.irreducible
  intro P ha ht
  obtain ⟨η⟩ := TensorParameters.natural (ρG.comp L.subtype) P hr hF ha ht
  exact natural_quadraticRatio_le ρG L hF (by omega) η

end
end CFSG.Quasithin.ChapterK.Symplectic.Recognition
