module
public import Theory.SpecificGroups.GL2.DeterminantTwoPower
public import Theory.FieldTheory.RootsOfUnityCard

/-!
# Central scalar two-power subgroups of GL2

For a finite odd field F, the scalar matrices arising from roots of unity
of order dividing 2^(m+1) form a cyclic central subgroup of that exact order
when 2^(m+1) divides |F|-1. Its intersection with the determinant kernel
has order two, including at level m=0.

The cyclic multiplicative group of F supplies a primitive root of each
specified order. Scalar matrices embed these roots injectively and centrally.
Their determinant is the square of the scalar, so intersection with the
determinant kernel is exactly the scalar image of the second roots of unity.

Together with the scalar-generation theorem this gives the actual central
product in Alperin--Brauer--Gorenstein II.2 Lemma 1(v), article pp17–18,
used in II.3 Proposition 3. The oddness assumption records the source setting;
the divisibility assumption itself already forces odd field order.
-/

namespace Matrix.GeneralLinearGroup

private theorem scalar_injective_two (F : Type*) [Field F] :
    Function.Injective (scalar (Fin 2) : Fˣ →* GL (Fin 2) F) := by
  intro a b h
  apply Units.ext
  have h' := congrArg (fun A : GL (Fin 2) F => A.val 0 0) h
  simpa [coe_scalar, Matrix.scalar_apply] using h'

public theorem twoPowerScalar_structure
    (F : Type*) [Field F] [Finite F] (_hodd : Odd (Nat.card F))
    (m : ℕ) (hd : 2 ^ (m + 1) ∣ Nat.card F - 1) :
    let C := (rootsOfUnity (2 ^ (m + 1)) F).map (scalar (Fin 2))
    IsCyclic C ∧ Nat.card C = 2 ^ (m + 1) ∧
      C ≤ Subgroup.center (GL (Fin 2) F) ∧
      Nat.card (C ⊓ (det : GL (Fin 2) F →* Fˣ).ker : Subgroup (GL (Fin 2) F)) = 2 := by
  let C := (rootsOfUnity (2 ^ (m + 1)) F).map (scalar (Fin 2))
  let e := Subgroup.equivMapOfInjective (rootsOfUnity (2 ^ (m + 1)) F)
    (scalar (Fin 2)) (scalar_injective_two F)
  have hcyc : IsCyclic C := isCyclic_of_injective e.symm.toMonoidHom e.symm.injective
  have hc : Nat.card C = 2 ^ (m + 1) :=
    (Nat.card_congr e.symm.toEquiv).trans (FiniteField.card_rootsOfUnity_of_dvd F _ hd)
  have hcent : C ≤ Subgroup.center (GL (Fin 2) F) := by
    rintro A ⟨c, _hc, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro B
    exact (scalar_commute c B).symm
  have hi : C ⊓ (det : GL (Fin 2) F →* Fˣ).ker =
      (rootsOfUnity 2 F).map (scalar (Fin 2)) := by
    ext A
    constructor
    · rintro ⟨⟨c, _hc, rfl⟩, hdet⟩
      refine ⟨c, ?_, rfl⟩
      change det (scalar (Fin 2) c) = 1 at hdet
      change c ^ 2 = 1
      simpa only [det_scalar, Fintype.card_fin] using hdet
    · rintro ⟨c, hc2, rfl⟩
      refine ⟨⟨c, ?_, rfl⟩, ?_⟩
      · exact rootsOfUnity_le_of_dvd (dvd_pow_self 2 (by omega : m + 1 ≠ 0)) hc2
      · change det (scalar (Fin 2) c) = 1
        change c ^ 2 = 1 at hc2
        simpa only [det_scalar, Fintype.card_fin] using hc2
  refine ⟨hcyc, hc, hcent, ?_⟩
  rw [hi, Subgroup.card_map_of_injective (scalar_injective_two F)]
  exact FiniteField.card_rootsOfUnity_of_dvd F 2
    ((dvd_pow_self 2 (by omega : m + 1 ≠ 0)).trans hd)

end Matrix.GeneralLinearGroup
