module
public import CFSG.Quasithin.ChapterE.Section02.SolvableStructure
public import Theory.GroupTheory.PResidual.TwoCoreOddDivisors
public import Theory.GroupTheory.WreathTwoSylowModel
/-!
# Cubic specialization of the solvable E.2.1 source theorem

Odd divisibility survives the normal two-core quotient and its two-residual.
Thus an actual S₃, SL₂(2), or binary-plane wreath actor forces the prime in
E.2.1 to be three. The conclusion keeps the literal residual of H/O₂(H)
and actual cyclic, elementary-plane, and extraspecial Heisenberg models.
The actor epimorphism alone supplies divisibility; its whole kernel is not
identified with O₂(H).

Source: Aschbacher--Smith E.2.1, printed p.215, and original 13.2.9,
printed pp.880--881. The Chapter 13 assembly supplies its source actor and
centralizer escape; this theorem discharges the E.2.1 model deduction.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.SolvableMinimalParabolic
open ChapterB
variable {H : Type*} [Group H] [Finite H]

/-- The exact cubic alternatives for the residual in the original two-core
quotient. The extraspecial case retains its exponent-three Heisenberg model. -/
@[expose] def CubicResidualModels (H : Type*) [Group H] : Prop :=
  (Nat.card (pResidual 2 (H ⧸ pCore 2 H)) = 3 ∧
    Nonempty (pResidual 2 (H ⧸ pCore 2 H) ≃* Multiplicative (ZMod 3))) ∨
  (Nat.card (pResidual 2 (H ⧸ pCore 2 H)) = 9 ∧
    Nonempty (pResidual 2 (H ⧸ pCore 2 H) ≃*
      (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)))) ∨
  (Nat.card (pResidual 2 (H ⧸ pCore 2 H)) = 27 ∧
    IsExtraspecial 3 (pResidual 2 (H ⧸ pCore 2 H)) ∧
    Nonempty (pResidual 2 (H ⧸ pCore 2 H) ≃* HeisenbergPrime 3))

/-- Cubic divisibility fixes the prime in the full E.2.1 source theorem. -/
theorem source_cubic_models {K : GroupClass} (hH : IsSQTK K H)
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤) (hs : Group.IsSolvable H)
    (hescape : ¬ (minimalParabolicMax T hP).pCoreIn 2 ≤ pCore 2 H ∨
      ¬ centralizerModulo (T : Subgroup H) (minimalParabolicCore T hP)
        ((minimalParabolicCore T hP).pCoreIn 2) ≤ pCore 2 H)
    (hthree : 3 ∣ Nat.card H) : CubicResidualModels H := by
  have hd := odd_prime_dvd_twoCore_quotient_residual Nat.prime_three (by decide) hthree
  obtain ⟨p,hp,_,hm⟩ := source_models hH T hP hs hescape
  have hprime (k : ℕ) (hcard : Nat.card (pResidual 2 (H ⧸ pCore 2 H)) = p ^ k) : p = 3 := by
    rw [hcard] at hd
    have hp3 : 3 ∣ p := Nat.prime_three.dvd_of_dvd_pow hd
    exact ((Nat.dvd_prime hp).mp hp3).resolve_left (by decide) |>.symm
  rcases hm with ⟨hc,he⟩ | ⟨hc,he⟩ | ⟨hc,hx,he⟩
  · have hp3 := hprime 1 (by simpa using hc)
    rw [hp3] at hc he
    exact Or.inl ⟨hc,he⟩
  · have hp3 := hprime 2 hc
    rw [hp3] at hc he
    exact Or.inr (Or.inl ⟨hc,he⟩)
  · have hp3 := hprime 3 hc
    rw [hp3] at hc hx he
    exact Or.inr (Or.inr ⟨hc,hx,he⟩)

/-- An actual actor epimorphism supplies the cubic divisibility; no assertion
about the action kernel is needed. -/
theorem source_cubic_models_of_surjective {K : GroupClass} (hH : IsSQTK K H)
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤) (hs : Group.IsSolvable H)
    (hescape : ¬ (minimalParabolicMax T hP).pCoreIn 2 ≤ pCore 2 H ∨
      ¬ centralizerModulo (T : Subgroup H) (minimalParabolicCore T hP)
        ((minimalParabolicCore T hP).pCoreIn 2) ≤ pCore 2 H)
    {A : Type*} [Group A] [Finite A] (f : H →* A) (hf : Function.Surjective f)
    (hthree : 3 ∣ Nat.card A) : CubicResidualModels H :=
  source_cubic_models hH T hP hs hescape (hthree.trans (card_dvd_of_surjective f hf))

/-- Literal S₃ or binary-plane wreath actors give the required cubic
specialization in the proof of original 13.2.9. -/
theorem source_cubic_models_of_symmetricThree_or_wreath
    {K : GroupClass} (hH : IsSQTK K H)
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤) (hs : Group.IsSolvable H)
    (hescape : ¬ (minimalParabolicMax T hP).pCoreIn 2 ≤ pCore 2 H ∨
      ¬ centralizerModulo (T : Subgroup H) (minimalParabolicCore T hP)
        ((minimalParabolicCore T hP).pCoreIn 2) ≤ pCore 2 H)
    (ha : (∃ f : H →* Equiv.Perm (Fin 3), Function.Surjective f) ∨
      (∃ f : H →* RegularWreathProduct (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
        (Multiplicative (ZMod 2)), Function.Surjective f)) : CubicResidualModels H := by
  rcases ha with ⟨f,hf⟩ | ⟨f,hf⟩
  · exact source_cubic_models_of_surjective hH T hP hs hescape f hf (by
      simp only [Nat.card_perm]
      norm_num)
  · apply source_cubic_models_of_surjective hH T hP hs hescape f hf
    have hc : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) = 6 := by
      rw [Nat.card_eq_fintype_card]
      decide +kernel
    rw [RegularWreathProduct.card,hc]
    norm_num [Nat.card_eq_fintype_card]

/-- The natural SL₂(2) actor uses the identical original two-core quotient. -/
theorem source_cubic_models_of_binaryLinearTwo
    {K : GroupClass} (hH : IsSQTK K H)
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤) (hs : Group.IsSolvable H)
    (hescape : ¬ (minimalParabolicMax T hP).pCoreIn 2 ≤ pCore 2 H ∨
      ¬ centralizerModulo (T : Subgroup H) (minimalParabolicCore T hP)
        ((minimalParabolicCore T hP).pCoreIn 2) ≤ pCore 2 H)
    (f : H →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (hf : Function.Surjective f) :
    CubicResidualModels H := by
  apply source_cubic_models_of_surjective hH T hP hs hescape f hf
  have hc : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) = 6 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  rw [hc]
  decide

/-- The literal faithful module quotient H/C_H(U) in original 13.2.8--9
supplies the epimorphism used above. The centralizer kernel remains the
specified one and is not replaced by the two-core. -/
theorem source_cubic_models_of_centralizer_quotient
    {K : GroupClass} (hH : IsSQTK K H)
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤) (hs : Group.IsSolvable H)
    (hescape : ¬ (minimalParabolicMax T hP).pCoreIn 2 ≤ pCore 2 H ∨
      ¬ centralizerModulo (T : Subgroup H) (minimalParabolicCore T hP)
        ((minimalParabolicCore T hP).pCoreIn 2) ≤ pCore 2 H)
    (U : Subgroup H) [U.Normal]
    (ha : Nonempty ((H ⧸ centralizer (U : Set H)) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) ∨
      Nonempty ((H ⧸ centralizer (U : Set H)) ≃*
        RegularWreathProduct (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
          (Multiplicative (ZMod 2)))) : CubicResidualModels H := by
  let q := QuotientGroup.mk' (centralizer (U : Set H))
  have hq := QuotientGroup.mk'_surjective (centralizer (U : Set H))
  rcases ha with ha | ha
  · obtain ⟨e⟩ := ha
    exact source_cubic_models_of_binaryLinearTwo hH T hP hs hescape
      (e.toMonoidHom.comp q) (e.surjective.comp hq)
  · obtain ⟨e⟩ := ha
    apply source_cubic_models_of_symmetricThree_or_wreath hH T hP hs hescape
    exact Or.inr ⟨e.toMonoidHom.comp q,e.surjective.comp hq⟩
end CFSG.Quasithin.ChapterE.SolvableMinimalParabolic
