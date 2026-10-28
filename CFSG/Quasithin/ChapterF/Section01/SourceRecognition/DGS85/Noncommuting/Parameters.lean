module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.Recognition

/-!
# The actual local parameter of a recognized critical section

DGS defines q_delta as the order of Ω₁(Z(T)), where T is a Sylow subgroup
of L_delta/Q_delta. An actual SL₂ identification makes T elementary abelian
of defining-field order, so this parameter is exactly that field order.
The two marked natural sections therefore have equal source parameters,
for every choice of the original quotient Sylows.

Source: DGS, *Groups and Graphs* (1985), notation p.118 and (7.1)(a),
pp.126--127. The source application is in `RecognitionSource`.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
universe u v₀ v₁
variable {D : Type*} [Group D]

/-- The source parameter for any Sylow of the actual marked quotient. -/
theorem quotient_sylow_omega_card {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : D ≃* SL(2,F)) (T : Sylow 2 D) :
    Nat.card (omegaCenterIn (T : Subgroup D)) = Nat.card F := by
  let : Finite D := Finite.of_equiv SL(2,F) e.toEquiv.symm
  let U := T.mapSurjective (f := e.toMonoidHom) e.surjective
  let f : T ≃* Multiplicative F :=
    ((T : Subgroup D).equivMapOfInjective e.toMonoidHom e.injective).trans
      (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 U).symm
  have hs (t : T) : t ^ 2 = 1 := by
    apply f.injective
    rw [map_pow,map_one,pow_two]
    change (f t).toAdd + (f t).toAdd = 0
    exact CharTwo.add_self_eq_zero _
  have hm (s t : T) : s*t = t*s := f.injective (by rw [map_mul,map_mul,mul_comm])
  have hω : omegaCenterIn (T : Subgroup D) = (T : Subgroup D) := by
    apply le_antisymm (map_subtype_le _)
    intro t ht
    apply (mem_omegaCenterIn_iff _ _).mpr
    refine ⟨ht,?_,congrArg Subtype.val (hs ⟨t,ht⟩)⟩
    intro s hst
    exact congrArg Subtype.val (hm ⟨s,hst⟩ ⟨t,ht⟩)
  rw [hω]
  exact Nat.card_congr f.toEquiv

/-- Natural recognition gives equality of the actual q parameters in either orientation. -/
theorem EqualFieldNaturalSections.sylow_omega_card_eq
    {D₀ D₁ : Type u} [Group D₀] [Group D₁]
    {W₀ : Type v₀} {W₁ : Type v₁}
    [AddCommGroup W₀] [Module (ZMod 2) W₀]
    [AddCommGroup W₁] [Module (ZMod 2) W₁]
    {σ₀ : Representation (ZMod 2) D₀ W₀}
    {σ₁ : Representation (ZMod 2) D₁ W₁}
    (h : EqualFieldNaturalSections σ₀ σ₁) (T₀ : Sylow 2 D₀) (T₁ : Sylow 2 D₁) :
    Nat.card (omegaCenterIn (T₀ : Subgroup D₀)) =
      Nat.card (omegaCenterIn (T₁ : Subgroup D₁)) := by
  obtain ⟨F₀,i₀,f₀,c₀,F₁,i₁,f₁,c₁,e₀,e₁,E₀,E₁,he₀,he₁,hcard⟩ := h
  exact (quotient_sylow_omega_card e₀ T₀).trans (hcard.trans
    (quotient_sylow_omega_card e₁ T₁).symm)

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
