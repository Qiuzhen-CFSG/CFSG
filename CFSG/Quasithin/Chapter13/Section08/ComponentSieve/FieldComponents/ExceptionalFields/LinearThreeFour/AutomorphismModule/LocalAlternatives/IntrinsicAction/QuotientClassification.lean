module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.IntrinsicAction.QuotientClassification.Normalized
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.IntrinsicAction.CoreReduction


/-!
# Classification of the marked SL₃(4) Borel action

Conjugate the specified Sylow to the upper unitriangular subgroup. Relative
normality identifies each marked factor's two-core with its intersection
with that Sylow, so its order-three core quotient gives a nontrivial torus
image. Transport the fixing and inverting equations to the full Borel
quotient and apply its explicit linear, field and opposition-graph action.

The resulting central-line containment is transported back with its Sylow
kernel intact. Conjugation and opposition reversal are absorbed into the
GL₃ coefficient, yielding precisely the graph and graph-field alternatives.
The only classification premise is coverage by the standard automorphisms;
there is no order restriction on the actor or invariant-torus hypothesis.
The parent IntrinsicAction assembly removes the Sylow kernel and computes
the two residuals using these alternatives.

Source: Aschbacher–Smith, proof of 13.8.20, printed pp.954–955
(PDF pp.971–972), combined manuscript of 1 March 2004.
-/

public section

open Subgroup Representation.SL3FourNaturalDual
open Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.OuterSolvable.OddPrimeCoverage
open Matrix.PSL3.CartanActions Matrix.PSL3.CartanActions.BorelQuotient
open Matrix.PSL3.CartanActions.SixCommutators
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.IntrinsicAction
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.IntrinsicAction.QuotientClassification

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.IntrinsicAction

private theorem factor_not_le (A : Subgroup SL) (S : Sylow 2 SL)
    (hle : A ≤ normalizer (S : Set SL))
    (hn : (A.subgroupOf (normalizer (S : Set SL))).Normal)
    (hc : Nat.card (A ⧸ pCore 2 A) = 3) : ¬ A ≤ (S : Subgroup SL) := by
  intro h
  have he : A.pCoreIn 2 = A := by
    rw [factor_core_eq_inf A S hle hn, inf_eq_left.mpr h]
  have ht : pCore 2 A = ⊤ := by
    apply top_unique
    intro x _
    have hx : x.val ∈ A.pCoreIn 2 := by rw [he]; exact x.property
    obtain ⟨y, hy, hyx⟩ := hx
    have hyx' : y = x := Subtype.ext hyx
    exact hyx' ▸ hy
  rw [ht] at hc
  let : Subsingleton (A ⧸ (⊤ : Subgroup A)) := QuotientGroup.subsingleton_quotient_top
  have hcard : Nat.card (A ⧸ (⊤ : Subgroup A)) = 1 := Nat.card_unique
  omega

private theorem back_containment (e : MulAut SL) (S : Subgroup SL)
    (hS : (unipotentSL F).map e.toMonoidHom = S)
    (A : Subgroup SL) (hA : A.map e.symm.toMonoidHom ≤ center SL ⊔ unipotentSL F) :
    A ≤ center SL ⊔ S := by
  have hZ : (center SL).map e.toMonoidHom ≤ center SL := by
    rintro _ ⟨z, hz, rfl⟩
    exact MulEquivClass.apply_mem_center e hz
  have hsup : (center SL ⊔ unipotentSL F).map e.toMonoidHom ≤ center SL ⊔ S := by
    rw [Subgroup.map_sup, hS]
    exact sup_le_sup hZ le_rfl
  intro x hx
  have h := hsup (mem_map_of_mem e.toMonoidHom (hA (mem_map_of_mem e.symm.toMonoidHom hx)))
  simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulEquiv.apply_symm_apply] using h

private theorem conjugate_factor (g : SL) (α : MulAut SL)
    (m : Matrix.GeneralLinearGroup (Fin 3) F) (σ : F ≃+* F)
    (h : (MulAut.conj g)⁻¹ * α * MulAut.conj g = specialActor F m σ true) :
    ∃ c : Matrix.GeneralLinearGroup (Fin 3) F,
      centerAction F α = linearConj F c * fieldAction F σ * graph F := by
  let β := specialActor F m σ true
  let w := g * β g⁻¹
  have hα : α = MulAut.conj w * β := by
    calc
      α = MulAut.conj g * β * (MulAut.conj g)⁻¹ := by change α = MulAut.conj g * specialActor F m σ true * (MulAut.conj g)⁻¹; rw [← h]; group
      _ = MulAut.conj w * β := by
        apply MulEquiv.ext
        intro x
        change g * β (g⁻¹ * x * g) * g⁻¹ = (g * β g⁻¹) * β x * (g * β g⁻¹)⁻¹
        simp only [map_mul, map_inv]
        group
  have hw : centerAction F (MulAut.conj w) =
      linearConj F (Matrix.SpecialLinearGroup.toGL w) := by
    rw [linearConj_toGL]
    apply MulEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := projection_surjective F x
    change projection F (w * y * w⁻¹) = projection F w * projection F y * (projection F w)⁻¹
    simp only [map_mul, map_inv]
  refine ⟨Matrix.SpecialLinearGroup.toGL w * m *
    Matrix.GeneralLinearGroup.map σ.toRingHom (reversalGL F), ?_⟩
  rw [hα, map_mul, hw, centerAction_specialActor]
  change linearConj F (Matrix.SpecialLinearGroup.toGL w) *
    (linearConj F m * fieldAction F σ * (linearConj F (reversalGL F) * graph F)) = _
  simp only [map_mul, mul_assoc]
  rw [← mul_assoc (fieldAction F σ), ResidualLinear.field_linearConj]
  simp only [mul_assoc]

/-- The actual marked Borel action is graph or graph-field, with the corresponding
marked factor contained in the scalar center times the specified Sylow. -/
theorem central_mod_sylow_alternatives {α : MulAut SL} (d : MarkedBorelFactors α)
    (hcover : standard F = ⊤) :
    (∃ c : Matrix.GeneralLinearGroup (Fin 3) F,
      centerAction F α = linearConj F c * graph F ∧
        d.plusFactor ≤ center SL ⊔ (d.sylow : Subgroup SL)) ∨
    (∃ (c : Matrix.GeneralLinearGroup (Fin 3) F) (σ : F ≃+* F),
      σ ≠ 1 ∧ centerAction F α = linearConj F c * fieldAction F σ * graph F ∧
        d.zeroFactor ≤ center SL ⊔ (d.sylow : Subgroup SL)) := by
  obtain ⟨g, hgS, hgB⟩ := sylowSL_normalizer_conjugate F (by decide : 0 < 2) sl3Field_card d.sylow
  let e := MulAut.conj g
  let β := e⁻¹ * α * e
  have hSU : (d.sylow : Subgroup SL).map e.symm.toMonoidHom = unipotentSL F :=
    (map_symm_eq_iff_map_eq (e := e) (H := (d.sylow : Subgroup SL)) (unipotentSL F)).mpr hgS
  have hNB : (normalizer (d.sylow : Set SL)).map e.symm.toMonoidHom = borelSL F :=
    (map_symm_eq_iff_map_eq (e := e) (H := normalizer (d.sylow : Set SL)) (borelSL F)).mpr hgB
  have hb_apply (x : SL) : β (e.symm x) = e.symm (α x) := by
    simp only [β, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.apply_symm_apply]
  have hβU : (unipotentSL F).map β.toMonoidHom = unipotentSL F := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨u, hu, rfl⟩
      have heu : e u ∈ (d.sylow : Subgroup SL) := hgS.le (mem_map_of_mem _ hu)
      have hau := d.sylow_stable.le (mem_map_of_mem α.toMonoidHom heu)
      have hh : e.symm (α (e u)) ∈ unipotentSL F :=
        hSU.le (mem_map_of_mem e.symm.toMonoidHom hau)
      change β u ∈ unipotentSL F
      simpa only [β, MulAut.mul_apply, MulAut.inv_apply] using hh
    · exact (Nat.card_congr (equivMapOfInjective (unipotentSL F)
        β.toMonoidHom β.injective).toEquiv).le
  let A₀ := d.zeroFactor.map e.symm.toMonoidHom
  let Ap := d.plusFactor.map e.symm.toMonoidHom
  have h₀ : A₀ ≤ borelSL F := (map_mono d.zero_le).trans hNB.le
  have hp : Ap ≤ borelSL F := (map_mono d.plus_le).trans hNB.le
  have hn (A : Subgroup SL) (hA : ¬ A ≤ (d.sylow : Subgroup SL)) :
      ¬ A.map e.symm.toMonoidHom ≤ unipotentSL F := by
    intro h
    apply hA
    intro x hx
    have he := hgS.le (mem_map_of_mem e.toMonoidHom
      (h (mem_map_of_mem e.symm.toMonoidHom hx)))
    simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulEquiv.apply_symm_apply] using he
  have hn₀ : ¬ A₀ ≤ unipotentSL F :=
    hn _ (factor_not_le _ _ d.zero_le d.zero_normal d.zero_quotient_card)
  have hnp : ¬ Ap ≤ unipotentSL F :=
    hn _ (factor_not_le _ _ d.plus_le d.plus_normal d.plus_quotient_card)
  have hf : ∀ x ∈ A₀, β x * x⁻¹ ∈ unipotentSL F := by
    rintro _ ⟨x, hx, rfl⟩
    have hc := factor_core_le_sylow _ _ d.zero_le d.zero_normal (d.fix_zero x hx)
    have hh := hSU.le (mem_map_of_mem e.symm.toMonoidHom hc)
    simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, hb_apply, map_mul, map_inv] using hh
  have hi : ∀ x ∈ Ap, β x * x ∈ unipotentSL F := by
    rintro _ ⟨x, hx, rfl⟩
    have hc := factor_core_le_sylow _ _ d.plus_le d.plus_normal (d.invert_plus x hx)
    have hh := hSU.le (mem_map_of_mem e.symm.toMonoidHom hc)
    simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, hb_apply, map_mul] using hh
  obtain ⟨m, σ, hβ, hσ⟩ := normalized_classification β hβU A₀ Ap h₀ hp hn₀ hnp hf hi hcover
  obtain ⟨c, hc⟩ := conjugate_factor g α m σ hβ
  rcases hσ with ⟨rfl, hpZ⟩ | ⟨hσ, h₀Z⟩
  · exact Or.inl ⟨c, by simpa only [map_one, mul_one] using hc,
      back_containment e _ hgS d.plusFactor hpZ⟩
  · exact Or.inr ⟨c, σ, hσ, hc, back_containment e _ hgS d.zeroFactor h₀Z⟩
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.IntrinsicAction
