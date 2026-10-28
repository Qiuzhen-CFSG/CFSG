module

public import CFSG.Quasithin.ClassicalModels
public import CFSG.Quasithin.MainConverse.SmallModels
public import CFSG.Quasithin.MainConverse.EvenUnitarySymplecticLocal.ModelTransport
public import CFSG.Quasithin.MainConverse.EvenUnitarySymplecticLocal.SymplecticSix
public import CFSG.Quasithin.MainConverse.EvenUnitarySymplecticLocal.UnitaryFour
public import CFSG.Quasithin.MainConverse.EvenUnitarySymplecticLocal.UnitaryFive
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived

/-!
# Local conditions for the even unitary and symplectic converse branches

The full parabolic rank bounds and intrinsic two-core centralizer calculations
prove QT and E for PSU₄(2^f), f ≥ 1, PSU₅(4), PSp₄(2^f), f ≥ 2, and PSp₆(2).
Unpacking the exact `IsPSU` and `IsPSp` witnesses transports these results to
each group in the classification list. The unitary calculations allow every
nondegenerate Hermitian form with the prescribed Frobenius involution;
PSU₅(4) uses a matrix field of order 16.

The small derived symplectic carrier is the commutator of the actual central
quotient PSp₄(2). The proved polar-representation equivalence identifies it
with A₆. Its cube-free odd order gives QT, and the alternating local calculation
gives E. No proper-K hypothesis is needed for any of these local conclusions.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Theorem 0.1.2(1–2), printed p.4, repeated as Theorem 0.1.1(1–2) on p.482.
The proper-K induction hypothesis belongs to the final classification assembly.
-/

namespace CFSG.Quasithin.MainConverse

open Theory.SpecificGroups.SymplecticFour.Binary

/-- QT and E for every PSU₄(2^f) witness in the classification list, including
`f = 1` and arbitrary allowed Hermitian forms. -/
public theorem psu4_two_pow_quasithin_and_evenCharacteristic
    {G : Type*} [Group G] [Finite G] {f : ℕ}
    (hf : 1 ≤ f) (hG : ClassicalGroup.IsPSU G 4 (2 ^ f)) :
    IsQuasithin G ∧ IsEvenCharacteristic G := by
  obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := hG
  let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_equiv G e.toEquiv
  exact ⟨quasithin_of_model_equiv e
      (UnitaryFour.projective_quasithin J f hf hcard hconj),
    evenCharacteristic_of_model_equiv e
      (UnitaryFour.projective_evenCharacteristic J f hf hcard hconj)⟩

/-- QT and E for PSU₅(4). The witness supplies matrix-field order `4² = 16`
and fourth-power Frobenius, with no restriction on its nondegenerate form. -/
public theorem psu5_four_quasithin_and_evenCharacteristic
    {G : Type*} [Group G] [Finite G] (hG : ClassicalGroup.IsPSU G 5 4) :
    IsQuasithin G ∧ IsEvenCharacteristic G := by
  obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := hG
  let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_equiv G e.toEquiv
  exact ⟨quasithin_of_model_equiv e (UnitaryFive.quasithin J hcard hconj),
    evenCharacteristic_of_model_equiv e (UnitaryFive.evenCharacteristic J hcard hconj)⟩

/-- The PSU₅ alternative in the rank-two list has exactly `f = 2`. -/
public theorem psu5_two_pow_quasithin_and_evenCharacteristic
    {G : Type*} [Group G] [Finite G] {f : ℕ}
    (hf : f = 2) (hG : ClassicalGroup.IsPSU G 5 (2 ^ f)) :
    IsQuasithin G ∧ IsEvenCharacteristic G := by
  subst f
  exact psu5_four_quasithin_and_evenCharacteristic hG

/-- QT and E for the PSp₆(2) alternative, over every coefficient field of
order two and through the actual projective matrix-group isomorphism. -/
public theorem psp6_two_quasithin_and_evenCharacteristic
    {G : Type*} [Group G] [Finite G] (hG : ClassicalGroup.IsPSp G 3 2) :
    IsQuasithin G ∧ IsEvenCharacteristic G := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hG
  exact ⟨quasithin_of_model_equiv e (SymplecticSix.projective_quasithin hcard),
    evenCharacteristic_of_model_equiv e (SymplecticSix.projective_evenCharacteristic hcard)⟩

/-- Every odd prime rank of the actual small derived symplectic carrier
is at most two. The A₆ identification is a proved multiplicative equivalence. -/
public theorem symplectic_derived_stronglyQuasithin :
    IsStronglyQuasithin (commutator (ClassicalGroup.PSp 2 (ZMod 2))) :=
  (alternating_stronglyQuasithin (Or.inr (Or.inl rfl))).of_injective
    projectiveDerivedEquivAlternatingSix.toMonoidHom
    projectiveDerivedEquivAlternatingSix.injective

public theorem symplectic_derived_quasithin :
    IsQuasithin (commutator (ClassicalGroup.PSp 2 (ZMod 2))) :=
  symplectic_derived_stronglyQuasithin.quasithin

/-- QT for the exact isomorphism witness used by the rank-two model list. -/
public theorem symplectic_derived_quasithin_of_iso
    {G : Type*} [Group G] [Finite G]
    (e : G ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) : IsQuasithin G :=
  quasithin_of_model_equiv e symplectic_derived_quasithin

/-- Both local conditions for the exact small derived carrier witness. -/
public theorem symplectic_derived_quasithin_and_evenCharacteristic_of_iso
    {G : Type*} [Group G] [Finite G]
    (e : G ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) :
    IsQuasithin G ∧ IsEvenCharacteristic G :=
  ⟨symplectic_derived_quasithin_of_iso e, symplectic_derived_evenCharacteristic_of_iso e⟩

end CFSG.Quasithin.MainConverse
