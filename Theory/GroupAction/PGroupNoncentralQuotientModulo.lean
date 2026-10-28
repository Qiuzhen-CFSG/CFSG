module

public import Theory.GroupAction.SubgroupQuotientIrreducible
public import Theory.GroupTheory.CommutatorPreimageFrattini
public import Mathlib.Order.Atoms.Finite

/-!
# Noncentral chief quotients above a layer with full support modulo that layer

Let P normalize a finite p-group U and a proper subgroup B. If E≤P and
[U,E]B=U, choose a maximal proper P-invariant denominator containing B and
the Frattini subgroup. The resulting literal quotient U/D is elementary,
nontrivial and P-irreducible, with full E-support. The action is specified on
every original quotient representative.

This extends the full-commutator construction to a possibly nontrivial fixed
layer B. It is needed when constructing the component-invariant section of
O₂(X)U/U in Aschbacher–Smith, Lemma 8.2.7, printed p.718 (PDF p.735).
The source application must establish properness and fullness modulo U;
neither is inferred from the existence of an unrelated H-chief factor.
-/

namespace Subgroup
open scoped Pointwise commutatorElement
universe u
/-- Fullness modulo a layer contained in the denominator descends to the literal
quotient action. The actor need not normalize a chosen complement. -/
public theorem quotient_action_full_modulo
    {G : Type u} [Group G] (P U Z E : Subgroup G)
    (hN : (Z.subgroupOf U).Normal)
    (hPU : P ≤ Subgroup.normalizer (U : Set G))
    (B : Subgroup G) (hBZ : B ≤ Z)
    (hEP : E ≤ P) (hfull : ⁅U,E⁆ ⊔ B = U) :
    let _ := hN
    ∀ ρ : P →* MulAut (U ⧸ Z.subgroupOf U),
      (∀ p : P, ∀ u : U,
        ρ p (QuotientGroup.mk' (Z.subgroupOf U) u) =
          QuotientGroup.mk' (Z.subgroupOf U)
            ⟨(p : G) * (u : G) * (p : G)⁻¹,
              (Subgroup.mem_normalizer_iff.mp (hPU p.property) u).mp u.property⟩) →
      commutatorAction ((E.subgroupOf P).map ρ) (U ⧸ Z.subgroupOf U) = ⊤ := by
  let _ := hN
  dsimp only
  intro ρ hρ
  let F := (E.subgroupOf P).map ρ
  let π := QuotientGroup.mk' (Z.subgroupOf U)
  let C := commutatorAction F (U ⧸ Z.subgroupOf U)
  let D := (C.comap π).map U.subtype
  have hUD : U ≤ D := by
    rw [← hfull]
    apply sup_le
    · apply Subgroup.commutator_le.mpr
      intro u hu e he
      let uU : U := ⟨u,hu⟩
      let eP : P := ⟨e,hEP he⟩
      let eF : F := ⟨ρ eP, Subgroup.mem_map_of_mem ρ he⟩
      have hmem : ⁅u,e⁆ ∈ U := hfull.le (mem_sup_left (Subgroup.commutator_mem_commutator hu he))
      refine ⟨⟨⁅u,e⁆,hmem⟩, ?_, rfl⟩
      change π ⟨⁅u,e⁆,hmem⟩ ∈ C
      have hh : (π uU⁻¹)⁻¹ * (eF • π uU⁻¹) ∈ C := by
        dsimp only [C]
        rw [commutatorAction_eq_closure]
        exact Subgroup.subset_closure ⟨eF, π uU⁻¹, rfl⟩
      have heq : (π uU⁻¹)⁻¹ * (eF • π uU⁻¹) = π ⟨⁅u,e⁆,hmem⟩ := by
        change (π uU⁻¹)⁻¹ * (ρ eP) (π uU⁻¹) = _
        rw [hρ, ← map_inv, ← map_mul]
        congr 1
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, commutatorElement_def]
        simp only [uU, eP, mul_assoc]
      exact heq ▸ hh
    · intro b hb
      have hbU : b ∈ U := hfull.le (mem_sup_right hb)
      refine ⟨⟨b, hbU⟩, ?_, rfl⟩
      change π ⟨b, hbU⟩ ∈ C
      have hbq : π ⟨b, hbU⟩ = 1 :=
        (QuotientGroup.eq_one_iff (N := Z.subgroupOf U) _).mpr (hBZ hb)
      rw [hbq]
      exact C.one_mem
  apply top_unique
  intro w _
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) w
  obtain ⟨v,hv,hvu⟩ := hUD u.property
  have hvu' : v = u := Subtype.ext hvu
  exact hvu' ▸ hv

/-- An invariant proper layer B and [U,E]B=U give an irreducible elementary
quotient of U above B with full, nontrivial E-action. -/
public theorem exists_noncentral_irreducible_quotient_modulo
    {G : Type*} [Group G] [Finite G] {prime : ℕ} [Fact prime.Prime]
    (P U B E : Subgroup G) (hUP : U ≤ P)
    (hPU : P ≤ normalizer (U : Set G)) (hPB : P ≤ normalizer (B : Set G))
    (hBU : B < U) (hU : IsPGroup prime U) (hEP : E ≤ P) (hfull : ⁅U,E⁆ ⊔ B = U) :
    ∃ D : Subgroup G, B ≤ D ∧ D < U ∧
      ∃ _hPD : P ≤ normalizer (D : Set G), ∃ hN : (D.subgroupOf U).Normal,
        let _ := hN
        ∃ action : P →* MulAut (U ⧸ D.subgroupOf U),
          (∀ mover : P, ∀ point : U,
            action mover (QuotientGroup.mk' (D.subgroupOf U) point) =
              QuotientGroup.mk' (D.subgroupOf U)
                ⟨(mover : G) * (point : G) * (mover : G)⁻¹,
                  (mem_normalizer_iff.mp (hPU mover.property) point).mp point.property⟩) ∧
          IsElementaryAbelian prime (U ⧸ D.subgroupOf U) ∧
          Nontrivial (U ⧸ D.subgroupOf U) ∧
          (∀ K : Subgroup (U ⧸ D.subgroupOf U),
            (∀ mover : P, ∀ point, point ∈ K → action mover point ∈ K) →
              K = ⊥ ∨ K = ⊤) ∧
          commutatorAction ((E.subgroupOf P).map action) (U ⧸ D.subgroupOf U) = ⊤ ∧
          ¬ E.subgroupOf P ≤ action.ker := by
  classical
  let Φ := (frattini U).map U.subtype
  let B₀ := B ⊔ Φ
  have hΦU : Φ ≤ U := map_subtype_le _
  have hPΦ : P ≤ normalizer (Φ : Set G) := by
    apply le_normalizer_iff.mpr
    rintro mover hmover point ⟨u, hu, rfl⟩
    let a : MulAut U := U.normalizerMonoidHom ⟨mover, hPU hmover⟩
    refine ⟨a u, ?_, ?_⟩
    · exact (characteristic_iff_le_comap.mp (inferInstance : (frattini U).Characteristic) a) hu
    · rfl
  have hPB₀ : P ≤ normalizer (B₀ : Set G) :=
    (le_inf hPB hPΦ).trans (normalizer_inf_normalizer_le_normalizer_sup B Φ)
  have hB₀U : B₀ < U := by
    apply lt_of_le_of_ne (sup_le hBU.le hΦU)
    intro heq
    have hnative : B.subgroupOf U ⊔ frattini U = ⊤ := by
      apply map_injective U.subtype_injective
      rw [map_sup, map_subgroupOf_eq_of_le hBU.le,
        ← MonoidHom.range_eq_map, range_subtype]
      exact heq
    have hBtop : B.subgroupOf U = ⊤ := frattini_nongenerating hnative
    have hh := congrArg (Subgroup.map U.subtype) hBtop
    rw [map_subgroupOf_eq_of_le hBU.le, ← MonoidHom.range_eq_map, range_subtype] at hh
    exact hBU.ne hh
  obtain ⟨D, hB₀D, hmax⟩ := Finite.exists_le_maximal
    (p := fun L : Subgroup G => L < U ∧ P ≤ normalizer (L : Set G))
    (a := B₀) ⟨hB₀U, hPB₀⟩
  have hBD : B ≤ D := (show B ≤ B₀ from le_sup_left).trans hB₀D
  have hDU : D < U := hmax.prop.1
  have hPD : P ≤ normalizer (D : Set G) := hmax.prop.2
  have hN : (D.subgroupOf U).Normal :=
    (normal_subgroupOf_iff_le_normalizer hDU.le).mpr (hUP.trans hPD)
  let _ := hN
  have helem : IsElementaryAbelian prime (U ⧸ D.subgroupOf U) := by
    apply elementary_quotient_of_frattini_le hU
    intro point hpoint
    exact hB₀D ((show Φ ≤ B₀ from le_sup_right) (mem_map_of_mem U.subtype hpoint))
  have hnontrivial : Nontrivial (U ⧸ D.subgroupOf U) := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hs
    let _ := hs
    apply hDU.not_ge
    intro point hpoint
    exact (QuotientGroup.eq_one_iff (N := D.subgroupOf U) (x := ⟨point,hpoint⟩)).mp
      (Subsingleton.elim (QuotientGroup.mk' (D.subgroupOf U) ⟨point,hpoint⟩) 1)
  obtain ⟨action, hformula⟩ := exists_quotient_conjugation_action P U D hPU hPD hN
  have hsupport := quotient_action_full_modulo P U D E hN hPU B hBD hEP hfull
    action hformula
  have hirr := quotient_conjugation_irreducible_of_maximal P U D hDU.le hPU hN
    (fun L hDL hLU hPL => le_antisymm (hmax.2 ⟨hLU,hPL⟩ hDL) hDL)
      action hformula
  refine ⟨D, hBD, hDU, hPD, hN, action, hformula, helem, hnontrivial, hirr, hsupport, ?_⟩
  intro hker
  have hUE : ⁅E,U⁆ ≤ D := by
    apply commutator_le.mpr
    intro e he u hu
    let eP : P := ⟨e,hEP he⟩
    have heone : action eP = 1 := MonoidHom.mem_ker.mp (hker he)
    have hh := hformula eP ⟨u,hu⟩
    rw [heone] at hh
    have hd := QuotientGroup.eq_iff_div_mem.mp hh.symm
    change e * u * e⁻¹ / u ∈ D at hd
    simpa only [commutatorElement_def, div_eq_mul_inv] using hd
  rw [commutator_comm] at hUE
  exact hDU.not_ge (hfull.symm.le.trans (sup_le hUE hBD))

end Subgroup
