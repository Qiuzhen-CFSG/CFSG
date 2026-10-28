module
public import Theory.GroupAction.SubgroupQuotientIrreducible
public import Theory.GroupTheory.CommutatorPreimageFrattini
public import Mathlib.Order.Atoms.Finite

/-!
# A noncentral chief quotient above a prescribed proper layer

Let P normalize a finite p-subgroup U and a proper subgroup B of U. If a
subgroup E of P satisfies [U,E]=U, there is a P-invariant denominator D
between B and U such that the literal conjugation quotient U/D is a
nontrivial elementary abelian irreducible P-module. The E-image has full
commutator support and acts nontrivially on this same quotient.

Adjoin the embedded Frattini subgroup to B. Frattini nongeneration leaves a
proper subgroup, while characteristicity makes it invariant under P. Choose
a maximal proper P-invariant overgroup D. The Frattini containment makes U/D
elementary abelian; the quotient correspondence gives irreducibility. The
original full-commutator identity descends through the exact quotient action,
and would contradict D<U if E acted trivially.

This source-neutral construction supplies the intrinsic noncentral chief
factor above the terminal module in Stellmacher (10.1), printed p.63 before
(15), without assuming a classification or a chief-module cardinality.
-/

namespace Subgroup
open scoped Pointwise commutatorElement

public theorem exists_noncentral_irreducible_quotient_above
    {G : Type*} [Group G] [Finite G] {prime : ℕ} [Fact prime.Prime]
    (P U B E : Subgroup G) (hUP : U ≤ P)
    (hPU : P ≤ normalizer (U : Set G)) (hPB : P ≤ normalizer (B : Set G))
    (hBU : B < U) (hU : IsPGroup prime U) (hEP : E ≤ P) (hfull : ⁅U,E⁆ = U) :
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
  obtain ⟨action, hformula, _, hsupport⟩ := exists_quotient_conjugation_full_action
    P U D E ⊥ hPU hPD hN hEP hfull (by simp)
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
  rw [commutator_comm, hfull] at hUE
  exact hDU.not_ge hUE

end Subgroup
