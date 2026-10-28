module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.NonbinaryRecognition.TensorModels
public import Theory.Representation.ReeF4.BinaryDegree.SchurDescent
public import Theory.Representation.InjectiveDescent
public import Mathlib.FieldTheory.Finite.GaloisField


/-!
# Descent of the one-factor symplectic action

When the Schur degree is n and the absolute degree is four, identify F with
the actual endomorphism field by a binary algebra isomorphism. Apply the
absolute catalogue using the embedding induced by this isomorphism. Its
support is a singleton by the tensor dimension formula. The explicit
singleton intertwiner and Noether--Deuring descent give an equivalence
over the Schur field. Restrict this equivalence to the binary field and
transport coordinates back along the field isomorphism.

Reapplying the catalogue at the compatible embedding avoids assuming that
an arbitrary previously chosen embedding already identifies the two fields.
The conclusion identifies the actions, not merely their dimensions.

Source: GLS3, Remark 2.8.8 and Examples 2.8.10(d); the natural-module case
in the proof of G.9.3 on printed pp.356–357 of `refs/quasithin.pdf`.
-/

public section

open Representation Representation.FrobeniusTensor
open scoped MonoidAlgebra TensorProduct
namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Nonbinary
noncomputable section

variable {F E G ι : Type*} [Field F] [Field E] [Group G]
  [Algebra (ZMod 2) F] [Algebra (ZMod 2) E] [Fintype ι] [DecidableEq ι]

private def mapCoefficients_binary_equiv (h : F ≃ₐ[ZMod 2] E)
    (σ : Representation F G (ι → F)) :
    (restrictScalars (k := ZMod 2) σ).Equiv
      (restrictScalars (k := ZMod 2) (mapCoefficients h.toRingHom σ)) := by
  refine .mk (LinearEquiv.piCongrRight (fun _ : ι => h.toLinearEquiv)) ?_
  intro g
  apply LinearMap.ext
  intro v
  funext i
  change h (σ g v i) = mapCoefficients h.toRingHom σ g (fun j => h (v j)) i
  rw [← LinearMap.toMatrix'_mulVec (σ g) v,
    ← LinearMap.toMatrix'_mulVec (mapCoefficients h.toRingHom σ g), mapCoefficients_toMatrix]
  simp [Matrix.mulVec, dotProduct]

variable [Finite F]
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) (Derived F) V) [ρ.IsIrreducible]

/-- Descend a four-dimensional absolute action when its Schur field has the
defining-field degree. The resulting binary equivalence intertwines the actual actions. -/
theorem binary_basicTwist_equiv_of_schur_degree_eq {n : ℕ}
    (hF : Nat.card F = 2^n)
    (hs : Module.finrank (ZMod 2) (SchurField ρ) = n)
    (hd : Module.finrank (Closure ρ) (AbsoluteSpace ρ) = 4)
    (cat : ∀ e : F →+* Closure ρ, AbsoluteTensorCatalogue F (Closure ρ) e n) :
    ∃ j : Fin (2*n),
      Nonempty (ρ.Equiv (restrictScalars (k := ZMod 2) (basicTwist F j))) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let : Fintype (SchurField ρ) := Fintype.ofFinite _
  let : Module.Finite (ZMod 2) (SchurField ρ) := Module.Finite.of_finite
  have hc : Fintype.card F = Fintype.card (SchurField ρ) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := SchurField ρ), Nat.card_zmod, hs, hF]
  let h : F ≃ₐ[ZMod 2] SchurField ρ := FiniteField.algEquivOfCardEq 2 hc
  let e : F →+* Closure ρ := (algebraMap (SchurField ρ) (Closure ρ)).comp h.toRingHom
  obtain ⟨S, ⟨φ⟩⟩ := (cat e).exhaustive (AbsoluteSpace ρ) (absoluteRep ρ) inferInstance
  have hsize : 4 ^ S.card = 4^1 := by
    rw [← tensorModel_finrank (E := Closure ρ), ← φ.toLinearEquiv.finrank_eq, hd, pow_one]
  have hcard : S.card = 1 := Nat.pow_right_injective (by omega) hsize
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
  subst S
  let σ : Representation (SchurField ρ) (Derived F) (Coordinate → SchurField ρ) :=
    mapCoefficients h.toRingHom (basicTwist F j)
  have hmap : mapCoefficients (algebraMap (SchurField ρ) (Closure ρ)) σ =
      mapCoefficients e (basicTwist F j) := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.toMatrix'.injective
    simp only [σ, mapCoefficients_toMatrix, Matrix.map_map, e, RingHom.coe_comp]
  have hext : (extendScalars (Closure ρ) σ).Equiv
      (mapCoefficients e (basicTwist F j)) := by
    rw [← hmap]
    exact (extendScalarsMapCoefficientsEquiv (E := Closure ρ) σ).toRepresentationEquiv
  obtain ⟨ψ₀⟩ := repEquiv_of_extendScalars (S := Closure ρ) ρ.endFieldRep σ
    ⟨RepEquiv.ofRepresentationEquiv
      ((φ.trans (tensorModel_singleton_equiv e j)).trans hext.symm)⟩
  let ψ := ψ₀.toRepresentationEquiv
  let ψ₂ : ρ.Equiv (restrictScalars (k := ZMod 2) σ) :=
    .mk (ρ.asModuleEquiv.symm.trans (ψ.toLinearEquiv.restrictScalars (ZMod 2))) (by
      intro g
      apply LinearMap.ext
      intro v
      exact IntertwiningMap.isIntertwining ρ.endFieldRep σ ψ.toIntertwiningMap g
        (ρ.asModuleEquiv.symm v))
  exact ⟨j, ⟨ψ₂.trans (mapCoefficients_binary_equiv h (basicTwist F j)).symm⟩⟩

end
end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Nonbinary
