module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowSieveKernel
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.LinearThreeCommonActors
public import Theory.SpecificGroups.PSL3.BinaryOddCenterCover
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.GroupTheory.Fitting.PrimeComplementCentralizer

/-!
# The two natural SL₃ types on the chosen component

The natural module and its graph twist exhaust automorphism twists over the
binary prime field. The actual scalar-cover theorem also makes the kernel
of a natural SL₃ image characteristic: a nontrivial scalar centre forces
injectivity on the original two-core quotient, including field order four.
This avoids replacing the component by its projective quotient.

The actual consumer is `SeedAlternativesMovedSylowLinearThree`; it retains
the literal L-action and completes the marked constituent type bound.
Source: Aschbacher--Smith D.3.5(4), printed pp.195--196, using the
SL₃ multiplier and automorphism theorems stated in the imported modules.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
open ChapterB.QuasisimpleSource ChapterB.QuasisimpleSource.SourceCompletion

/-- The scalar-cover theorem makes a surjection to a noncenter-free SL₃
injective after taking the original two-core quotient. -/
theorem kernel_characteristic_of_linearThree
    {A : Type*} [Group A] [Finite A] [IsQuasisimple (A ⧸ pCore 2 A)]
    (F : BinaryField) (f : A →* SL(3,F.Carrier))
    (q : (A ⧸ pCore 2 A) →* SL(3,F.Carrier)) (hq : Function.Surjective q)
    (he : ∀ x, q (QuotientGroup.mk' (pCore 2 A) x) = f x) :
    f.ker.Characteristic := by
  let : Nontrivial SL(3,F.Carrier) := (Matrix.PSL3.projection_surjective F.Carrier).nontrivial
  by_cases hz : center SL(3,F.Carrier) = ⊥
  · exact kernel_characteristic_of_quasisimple_quotient (pCore 2 A) f q hq he hz
  have h2 : Nat.card F.Carrier ≠ 2 := by
    intro h2
    apply hz
    exact (Matrix.SL3.center_eq_bot_iff_card_mod_three F.Carrier).mpr (by simp [h2])
  let Q := A ⧸ pCore 2 A
  let e : Q ⧸ center Q ≃* PSL(3,F.Carrier) :=
    IsQuasisimple.centralQuotientEquiv q hq
  have ho : Odd (Nat.card (center Q)) := by
    have hfit : center Q ≤ fittingSubgroup Q := le_sSup ⟨inferInstance, inferInstance⟩
    apply Nat.coprime_two_left.mp
    exact pPrimeCore_coprime_card.of_dvd_right (card_dvd_of_le
      (hfit.trans (fitting_le_pPrimeCore_of_pCore_eq_bot 2
        (pCore_quotient_pCore_eq_bot 2))))
  obtain ⟨k,hk⟩ : ∃ k : SL(3,F.Carrier) →* Q, Function.Surjective k := by
    by_cases h4 : Nat.card F.Carrier = 4
    · obtain ⟨k,hk,_⟩ := Matrix.PSL3.BinaryOddCenterCover.exists_scalar_lift_four h4 e ho
      exact ⟨k,hk⟩
    · obtain ⟨k,hk,_⟩ := Matrix.PSL3.OrdinaryCenterRecognition.exists_scalar_lift h2 h4 e
      exact ⟨k,hk⟩
  have hi := (hq.bijective_of_nat_card_le (Nat.card_le_card_of_surjective k hk)).injective
  have hf : f.ker = pCore 2 A := by
    ext x
    change f x = 1 ↔ x ∈ pCore 2 A
    rw [←he]
    constructor
    · intro hx
      exact (QuotientGroup.eq_one_iff _).mp (hi (hx.trans (map_one q).symm))
    · intro hx
      exact (congrArg q ((QuotientGroup.eq_one_iff _).mpr hx)).trans (map_one q)
  rw [hf]
  infer_instance

/-- The same kernel statement in the original image coordinates. -/
theorem kernel_characteristic_of_linearThree_equiv
    {A B : Type*} [Group A] [Finite A] [Group B]
    [IsQuasisimple (A ⧸ pCore 2 A)]
    (F : BinaryField) (f : A →* B) (q : (A ⧸ pCore 2 A) →* B)
    (hq : Function.Surjective q)
    (he : ∀ x, q (QuotientGroup.mk' (pCore 2 A) x) = f x)
    (e : B ≃* SL(3,F.Carrier)) : f.ker.Characteristic := by
  have hk := kernel_characteristic_of_linearThree F
    (e.toMonoidHom.comp f) (e.toMonoidHom.comp q) (e.surjective.comp hq)
    (fun x => congrArg e (he x))
  rwa [MonoidHom.ker_comp_of_injective _ _ e.injective] at hk

/-- Every natural SL₃ automorphism twist has its original or graph type,
with the scalar centre and the actual actor retained. -/
theorem linearThree_two_twists (F : BinaryField) :
    ∃ τ₁ : Representation (ZMod 2) SL(3,F.Carrier) (Fin 3 → F.Carrier),
      ∀ a : MulAut SL(3,F.Carrier),
        Nonempty (Representation.Equiv ((linearNatural F 3).comp a.toMonoidHom)
          (linearNatural F 3)) ∨
        Nonempty (Representation.Equiv ((linearNatural F 3).comp a.toMonoidHom) τ₁) := by
  let τ := linearNatural F 3
  let γ := Matrix.PSL3.OuterSolvable.graphSL F.Carrier
  let d := linearThreeGraphDualAction F
  have hd : Representation.Equiv (τ.comp γ.toMonoidHom) τ.dual :=
    Representation.Equiv.mk d.linearEquiv (by
      intro g; apply LinearMap.ext; intro v
      have he := d.intertwines (γ g) v
      rw [linearThreeGraphDualAction_groupEquiv] at he
      change d.linearEquiv (τ (γ g) v) = τ.dual (γ.symm (γ g)) (d.linearEquiv v) at he
      change d.linearEquiv (τ (γ g) v) = τ.dual g (d.linearEquiv v)
      simpa only [MulEquiv.symm_apply_apply] using he)
  refine ⟨τ.comp γ.toMonoidHom, fun a => ?_⟩
  have ha : IsLinearNatural (τ.comp a.toMonoidHom) F 3 :=
    ⟨{ groupEquiv := a
       linearEquiv := LinearEquiv.refl (ZMod 2) _
       intertwines := fun _ _ => rfl }⟩
  have ht : IsLinearNatural τ F 3 :=
    ⟨{ groupEquiv := MulEquiv.refl _
       linearEquiv := LinearEquiv.refl (ZMod 2) _
       intertwines := fun _ _ => rfl }⟩
  rcases linearThree_naturals_same_or_dual (τ.comp a.toMonoidHom) τ F F ha ht with h | h
  · exact Or.inl h
  · obtain ⟨b⟩ := h
    exact Or.inr ⟨b.trans hd.symm⟩

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
