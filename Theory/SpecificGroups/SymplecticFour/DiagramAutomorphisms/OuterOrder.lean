module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.OuterQuotient
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Algebra.Algebra.ZMod

/-!
# Order bound for the actual symplectic outer quotient

The action on the two parabolic conjugacy classes descends to Out(Sp₄(F)).
Under the explicit diagram-preserving semilinear classification, its kernel
is exactly the image of the field automorphisms. Since their order is n for
|F| = 2ⁿ, the order of the outer quotient divides 2n. This order bound does
not assert that the extension is cyclic; that requires the exceptional graph
map whose square is Frobenius.

Source: Aschbacher--Smith, `refs/quasithin.pdf`, Proposition 1.3.4, printed
p.511; GLS3, Theorem 2.5.12, `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public section

namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

private noncomputable def fieldAutAlgEquiv : (F ≃+* F) ≃* (F ≃ₐ[ZMod 2] F) := by
  let := ZMod.algebra F 2
  exact {
    toFun := fun σ => AlgEquiv.ofRingEquiv (f := σ) (fun z => by
      exact congrArg (fun f : ZMod 2 →+* F => f z)
        (Subsingleton.elim (σ.toRingHom.comp (algebraMap (ZMod 2) F))
          (algebraMap (ZMod 2) F)))
    invFun := fun σ => σ.toRingEquiv
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }

theorem card_fieldAut {n : ℕ} (hF : Nat.card F = 2^n) : Nat.card (F ≃+* F) = n := by
  let := ZMod.algebra F 2
  let := Fintype.ofFinite F
  rw [Nat.card_congr fieldAutAlgEquiv.toEquiv, IsGalois.card_aut_eq_finrank]
  apply Nat.pow_right_injective (by decide : 2 ≤ 2)
  have hc := Module.card_eq_pow_finrank (K := ZMod 2) (V := F)
  simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod, hF] using hc.symm


open Subgroup
noncomputable def outerDiagramAction (hF : 2 < Nat.card F) :
    MulAut.Outer (Sp F) →* Equiv.Perm (parabolicClasses hF) :=
  QuotientGroup.lift _ (parabolicClassAction hF) (by
    rintro a ⟨g, rfl⟩
    exact (mem_parabolicClassAction_ker_iff hF _).mpr (inner_preservesDiagram g))

noncomputable def outerFieldHom : (F ≃+* F) →* MulAut.Outer (Sp F) :=
  (QuotientGroup.mk' (MulAut.innerSubgroup (Sp F))).comp fieldAutomorphismHom

theorem outerDiagramAction_ker (hF : 2 < Nat.card F)
    (hclass : ∀ a : MulAut (Sp F), PreservesDiagram a →
      ∃ g : Sp F, ∃ σ : F ≃+* F, a = MulAut.conj g * fieldAutomorphism σ) :
    (outerDiagramAction hF).ker = (outerFieldHom (F := F)).range := by
  ext x
  induction x using QuotientGroup.induction_on with | H a => ?_
  constructor
  · intro ha
    obtain ⟨g, σ, rfl⟩ := hclass a ((mem_parabolicClassAction_ker_iff hF a).mp ha)
    refine ⟨σ, ?_⟩
    change QuotientGroup.mk' _ (fieldAutomorphism σ) =
      QuotientGroup.mk' _ (MulAut.conj g * fieldAutomorphism σ)
    have hi : QuotientGroup.mk' (MulAut.innerSubgroup (Sp F)) (MulAut.conj g) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
    rw [map_mul, hi, one_mul]
  · rintro ⟨σ, hσ⟩
    rw [← hσ]
    exact (mem_parabolicClassAction_ker_iff hF _).mpr (field_preservesDiagram σ)

theorem card_outer_dvd_two_mul {n : ℕ} (hcard : Nat.card F = 2^n)
    (hF : 2 < Nat.card F)
    (hclass : ∀ a : MulAut (Sp F), PreservesDiagram a →
      ∃ g : Sp F, ∃ σ : F ≃+* F, a = MulAut.conj g * fieldAutomorphism σ) :
    Nat.card (MulAut.Outer (Sp F)) ∣ 2 * n := by
  let ρ := outerDiagramAction hF
  have hk : Nat.card ρ.ker ∣ n := by
    rw [show ρ.ker = (outerFieldHom (F := F)).range from outerDiagramAction_ker hF hclass]
    rw [← card_fieldAut hcard]
    exact Subgroup.card_range_dvd _
  have hp : Nat.card (Equiv.Perm (parabolicClasses hF)) ∣ 2 := by
    let := Fintype.ofFinite (parabolicClasses hF)
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    have hc : Fintype.card (parabolicClasses hF) ≤ 2 := by
      simpa only [Nat.card_eq_fintype_card] using card_parabolicClasses_le_two hF
    exact (Nat.factorial_dvd_factorial hc).trans (by decide)
  have hq : Nat.card (MulAut.Outer (Sp F) ⧸ ρ.ker) ∣ 2 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv]
    exact (card_subgroup_dvd_card ρ.range).trans hp
  rw [card_eq_card_quotient_mul_card_subgroup ρ.ker]
  exact Nat.mul_dvd_mul hq hk

end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
