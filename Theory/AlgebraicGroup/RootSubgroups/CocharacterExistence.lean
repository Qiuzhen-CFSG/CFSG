module

public import Theory.AlgebraicGroup.RootSubgroups.Cocharacter
public import Theory.AlgebraicGroup.Tori.Character.Tuple

universe u

open scoped BigOperators

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Every integral functional on the character lattice of a subtorus is
represented by an algebraic cocharacter. -/
public theorem exists_cocharacter_realizing_characterFunctional
    {G : Variety k} [AlgebraicGroup G] (T : ClosedSubgroup G)
    (hT : IsSubtorus T)
    (φ : Additive (TorusWeight T) →+ ℤ) :
    ∃ h : ClosedSubgroupTorusCocharacter T,
      ∀ χ, WeightCocharacterEquation T χ h (φ (Additive.ofMul χ)) := by
  classical
  obtain ⟨n, ⟨e⟩⟩ := hT
  let b : Fin n → TorusCharacter T.carrierVariety := fun i =>
    TorusCharacter.pullback e.inv (dCoordinateCharacter n i)
  let z : Fin n → ℤ := fun i => φ (Additive.ofMul (b i))
  let cD : AlgebraicGroup.Morphism (KMult k) (dVariety k n) :=
    dCharacterTupleMorphism n 1 (fun i _ => z i)
  let h : ClosedSubgroupTorusCocharacter T := e.hom.comp cD
  refine ⟨h, ?_⟩
  intro χ t
  let χD : TorusCharacter (dVariety k n) := TorusCharacter.pullback e.hom χ
  let q : Fin n → ℤ :=
    (dLaurentCharacterAddEquiv (k := k) n).symm (Additive.ofMul χD)
  have hqχ : dLaurentCharacter (k := k) n q = χD := by
    exact congrArg Additive.toMul
      ((dLaurentCharacterAddEquiv (k := k) n).apply_symm_apply
        (Additive.ofMul χD))
  have hχ : TorusCharacter.pullback e.inv
      (dLaurentCharacter (k := k) n q) = χ := by
    rw [hqχ]
    apply AlgebraicGroup.Morphism.ext
    funext x
    change χ.onPoints (e.hom.onPoints (e.inv.onPoints x)) = χ.onPoints x
    rw [e.inv_hom_id]
  have hχexpand : Additive.ofMul χ =
      ∑ i, q i • Additive.ofMul (b i) := by
    rw [← hχ]
    simp [dLaurentCharacter, b]
  have hφ : φ (Additive.ofMul χ) = ∑ i, q i * z i := by
    rw [hχexpand, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_zsmul]
    simp [z]
  change χ.pointCharacter (e.hom.onPoints (cD.onPoints t)) =
    (dPointEquiv 1 t 0 : k) ^ φ (Additive.ofMul χ)
  rw [hφ]
  rw [← hχ]
  change (dLaurentCharacter (k := k) n q).pointCharacter
      (e.inv.onPoints (e.hom.onPoints (cD.onPoints t))) = _
  rw [e.hom_inv_id]
  rw [TorusCharacter.pointCharacter_dLaurentCharacter]
  change (↑(∏ i, (dPointEquiv n (cD.onPoints t) i) ^ q i) : k) = _
  simp_rw [cD, dCharacterTupleMorphism_apply]
  rw [prod_laurentMonomial_zpow]
  simp

end Theory.AlgebraicGroup
