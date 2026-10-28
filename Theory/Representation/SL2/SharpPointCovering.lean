module
public import Theory.Representation.SL2.SharpSylowCovering

/-!
# Elementwise covering at a sharp binary SL₂ fixed index

Two generating Sylows with sharp fixed codimension n give complementary
fixed spaces on the quotient by all global fixed vectors. Uniformity there
and rank-nullity show that each nonidentity Sylow actor covers its fixed
space. For each nonfixed vector, the Sylow displacement map is injective;
equal finite cardinalities make it surjective. Lifting both statements
retains the entire central attachment without choosing a splitting.

Source: Niles, *Pushing-up in finite groups* (1979), Theorem 4.7(d), p.48.
The literal original-degree group application is
`Glauberman.PushingUpSL2DegreePointCovering`.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender Representation.SL2SylowFixedRecognition
open scoped MatrixGroups
namespace Representation.SL2
variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]

private theorem quotient_fixed_data (ρ : Representation (ZMod 2) SL(2,F) V)
    (hnt : ∃ g, ρ g ≠ 1) {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (R T : Sylow 2 SL(2,F)) (hgen : (R : Subgroup SL(2,F)) ⊔ T = ⊤)
    (hR : fixedCodim ρ R = n) (hT : fixedCodim ρ T = n) :
    IsCompl (fixedSpace (SL2SylowFixedRecognition.centralQuotient ρ) R) (fixedSpace (SL2SylowFixedRecognition.centralQuotient ρ) T) ∧
    Module.finrank (ZMod 2) (fixedSpace (SL2SylowFixedRecognition.centralQuotient ρ) R) = n ∧
    (∀ v : V, (fixedSpace ρ ⊤).mkQ v ∈ fixedSpace (SL2SylowFixedRecognition.centralQuotient ρ) R ↔
      v ∈ fixedSpace ρ R) := by
  obtain ⟨hspan,htotal,hyp⟩ := sharp_sylow_fixed_spaces ρ hnt hn hF R T hgen hR hT
  let σ := SL2SylowFixedRecognition.centralQuotient ρ
  have hcard : 4 ≤ Nat.card F := by
    rw [hF]
    exact (show 4 = 2^2 by decide) ▸ Nat.pow_le_pow_right (by decide) (by omega)
  have hc : IsCompl (fixedSpace σ R) (fixedSpace σ T) :=
    isCompl_fixedSpace_of_quadratic_generators σ R T hgen
      (centralQuotient_quadratic ρ R hyp R) (centralQuotient_quadratic ρ R hyp T)
      (centralQuotient_moved_eq_top ρ R hyp) (centralQuotient_fixed_eq_bot ρ hcard)
  have hd := (fixedSpace σ R).finrank_sup_add_finrank_inf_eq (fixedSpace σ T)
  rw [hc.sup_eq_top,hc.inf_eq_bot,finrank_top,finrank_bot] at hd
  have he : fixedCodim σ R = fixedCodim σ T := by
    obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq SL(2,F) R T
    exact (fixedCodim_map_conj σ R g).symm
  have hdR := fixedCodim_add_finrank σ (R : Subgroup SL(2,F))
  have hdT := fixedCodim_add_finrank σ (T : Subgroup SL(2,F))
  have hdim : Module.finrank (ZMod 2) (V ⧸ fixedSpace ρ ⊤) = 2*n := htotal
  have hd' : Module.finrank (ZMod 2) (fixedSpace σ R) = n := by omega
  refine ⟨hc,hd',?_⟩
  have hmap (A : Subgroup SL(2,F)) (v : V) (hv : v ∈ fixedSpace ρ A) :
      (fixedSpace ρ ⊤).mkQ v ∈ fixedSpace σ A := by
    intro a
    change σ (a : SL(2,F)) ((fixedSpace ρ ⊤).mkQ v) = _
    rw [centralQuotient_mk]
    exact congrArg (fixedSpace ρ ⊤).mkQ (hv a)
  intro v
  constructor
  · intro hv
    obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp (hspan.ge (Submodule.mem_top (x := v)))
    have hbR : (fixedSpace ρ ⊤).mkQ b ∈ fixedSpace σ R := by
      have hh := (fixedSpace σ R).sub_mem hv (hmap R a ha)
      simpa only [map_add,add_sub_cancel_left] using hh
    have hb0 : (fixedSpace ρ ⊤).mkQ b = 0 := hc.disjoint.le_bot ⟨hbR,hmap T b hb⟩
    have hbG : b ∈ fixedSpace ρ ⊤ := (Submodule.Quotient.mk_eq_zero _).mp hb0
    exact (fixedSpace ρ R).add_mem ha (fixedSpace_antitone ρ le_top hbG)
  · exact hmap R v

/-- Every nonidentity Sylow element covers the Sylow fixed space modulo
all global fixed vectors. -/
theorem sharp_sylow_actor_covering (ρ : Representation (ZMod 2) SL(2,F) V)
    (hnt : ∃ g, ρ g ≠ 1) {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (R T : Sylow 2 SL(2,F)) (hgen : (R : Subgroup SL(2,F)) ⊔ T = ⊤)
    (hR : fixedCodim ρ R = n) (hT : fixedCodim ρ T = n)
    (r : SL(2,F)) (hr : r ∈ R) (hr1 : r ≠ 1) :
    ∀ w ∈ fixedSpace ρ R, ∃ v : V, w - (ρ r v - v) ∈ fixedSpace ρ ⊤ := by
  obtain ⟨hc,hd,hfixed⟩ := quotient_fixed_data ρ hnt hn hF R T hgen hR hT
  let σ := SL2SylowFixedRecognition.centralQuotient ρ
  change Module.finrank (ZMod 2) (fixedSpace σ R) = n at hd
  have hyp := fixedSpaceHypotheses_of_isCompl σ R T hc
  let D := σ r - LinearMap.id
  have hle : D.range ≤ fixedSpace σ R := by
    rintro _ ⟨v,rfl⟩ a
    exact hyp.quadratic a a.property r hr v
  have hdim : Module.finrank (ZMod 2) D.range = n := by
    have hh := fixedCodim_add_finrank σ (zpowers r)
    rw [hyp.uniform r hr hr1] at hh
    have ht := (sharp_sylow_fixed_spaces ρ hnt hn hF R T hgen hR hT).2.1
    rw [fixedCodim_zpowers_eq_displacement_rank] at hh
    change Module.finrank (ZMod 2) D.range + _ = _ at hh
    change Module.finrank (ZMod 2) (V ⧸ fixedSpace ρ ⊤) = 2*n at ht
    omega
  have heq : D.range = fixedSpace σ R := Submodule.eq_of_le_of_finrank_eq hle (hdim.trans hd.symm)
  intro w hw
  obtain ⟨u,hu⟩ := heq ▸ ((hfixed w).mpr hw)
  obtain ⟨v,rfl⟩ := (fixedSpace ρ ⊤).mkQ_surjective u
  refine ⟨v,(Submodule.Quotient.mk_eq_zero _).mp ?_⟩
  change (fixedSpace ρ ⊤).mkQ (w - (ρ r v - v)) = 0
  rw [map_sub,map_sub,←centralQuotient_mk]
  change (fixedSpace ρ ⊤).mkQ w - D ((fixedSpace ρ ⊤).mkQ v) = 0
  rw [hu,sub_self]

/-- Every nonfixed vector has Sylow displacements covering the same fixed
quotient. Both the actor and vector remain literal. -/
theorem sharp_sylow_vector_covering (ρ : Representation (ZMod 2) SL(2,F) V)
    (hnt : ∃ g, ρ g ≠ 1) {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (R T : Sylow 2 SL(2,F)) (hgen : (R : Subgroup SL(2,F)) ⊔ T = ⊤)
    (hR : fixedCodim ρ R = n) (hT : fixedCodim ρ T = n)
    (v : V) (hv : v ∉ fixedSpace ρ R) :
    ∀ w ∈ fixedSpace ρ R, ∃ r ∈ (R : Subgroup SL(2,F)),
      w - (ρ r v - v) ∈ fixedSpace ρ ⊤ := by
  obtain ⟨hc,hd,hfixed⟩ := quotient_fixed_data ρ hnt hn hF R T hgen hR hT
  let σ := SL2SylowFixedRecognition.centralQuotient ρ
  let q := (fixedSpace ρ ⊤).mkQ
  have hyp := fixedSpaceHypotheses_of_isCompl σ R T hc
  let f : R → fixedSpace σ R := fun r =>
    ⟨σ r (q v) - q v,fun a => hyp.quadratic a a.property r r.property (q v)⟩
  have hf : Function.Injective f := by
    intro a b hab
    have he : σ (a : SL(2,F)) (q v) = σ (b : SL(2,F)) (q v) :=
      sub_left_injective (congrArg Subtype.val hab)
    have hh : σ ((b : SL(2,F))⁻¹ * a) (q v) = q v := by
      rw [map_mul,Module.End.mul_apply,he,σ.inv_self_apply]
    by_contra hnab
    have hne : (b : SL(2,F))⁻¹ * a ≠ 1 := by
      intro hz
      exact hnab (Subtype.ext (inv_mul_eq_one.mp hz).symm)
    have hfix := (mem_fixedSpace_zpowers_iff σ _ (q v)).mpr hh
    rw [hyp.uniform _ (mul_mem (inv_mem b.property) a.property) hne] at hfix
    exact hv ((hfixed v).mp hfix)
  have hcardR : Nat.card R = 2^n :=
    (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 R).symm.toEquiv).trans hF
  have hcardW : Nat.card (fixedSpace σ R) = 2^n := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hd]
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (V ⧸ fixedSpace ρ ⊤) := Finite.of_surjective _ (fixedSpace ρ ⊤).mkQ_surjective
  have hsurj : Function.Surjective f :=
    ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf,hcardR.trans hcardW.symm⟩).2
  intro w hw
  obtain ⟨r,hr⟩ := hsurj ⟨q w,(hfixed w).mpr hw⟩
  refine ⟨r,r.property,(Submodule.Quotient.mk_eq_zero _).mp ?_⟩
  change q (w - (ρ (r : SL(2,F)) v - v)) = 0
  rw [map_sub,map_sub,←centralQuotient_mk]
  change q w - (f r).val = 0
  rw [hr,sub_self]
end Representation.SL2
