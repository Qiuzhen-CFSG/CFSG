module

public import Theory.SpecificGroups.Monster.Construction.NOctad.LocalStructure.Radical.Actors

/-!
# Collection and the source setwise product for the radical

The two factors of the radical translate the first-coordinate Golay code.
Collection in the actual centralizer therefore has trivial linear part; the
second centralizer forces the remaining cocode automorphism to be even.
This proves the reverse collection theorem before taking any quotient.
Relative normality of the first factor then converts the collected word into
the literal setwise product in the source's order.

Source: Aschbacher, *Sporadic Groups*, Lemmas 14.4–14.5, printed pp. 61–62.
Products of the actual permutations use left composition.
-/

@[expose] public section
open scoped Pointwise
noncomputable section
namespace Sporadic.Monster.Construction.NOctad.LocalStructure.Radical
open TrialitySpin Atlas.Codes Atlas.Fischer

theorem psiAut2N_mem_N2 (α : ParkerStandardGroup) : psiAut2N α ∈ N2 := by
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  apply Subtype.ext
  ext ⟨a,b,c⟩ : 1
  change psiAut2 α.val (z2 (a,b,c)) = z2 (psiAut2 α.val (a,b,c))
  by_cases hα : α.val parkerOmega = parkerOmega <;>
    simp [psiAut2, hα, diagonal, flip2]

theorem Q2_le_N2 : Q2 ≤ N2 := by
  apply (Subgroup.closure_le _).mpr
  rintro g (⟨d,rfl⟩ | ⟨α,hα,hg⟩)
  · exact psi2N_mem_N2 d
  · have hg' : g = psiAut2N ⟨α,hα.1⟩ := Subtype.ext hg
    rw [hg']
    exact psiAut2N_mem_N2 _

theorem R_le_N2 : R ≤ N2 := sup_le inf_le_right (inf_le_left.trans Q2_le_N2)

theorem psiAut1N_mem_N2_iff (α : ParkerStandardGroup) :
    psiAut1N α ∈ N2 ↔ α.val parkerOmega = parkerOmega := by
  constructor
  · intro hg
    by_contra ho
    have hh := congrArg (fun g : N => g.val (axis2 loopOne))
      (Subgroup.mem_centralizer_singleton_iff.mp hg)
    change psiAut1 α.val (z2 (axis2 loopOne)) = z2 (psiAut1 α.val (axis2 loopOne)) at hh
    have hz : z2 (axis2 loopOne) = axis2 loopOne := by simp [axis2]
    rw [hz, psiAut1_axis2_odd α ho] at hh
    have he : α.val (loopInverse loopOne) = parkerSign 1 (α.val (loopInverse loopOne)) := by
      apply axis3_injective
      simpa [axis3] using hh
    exact parkerSign_one_ne _ he.symm
  · intro he
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    ext ⟨a,b,c⟩ : 1
    change psiAut1 α.val (z2 (a,b,c)) = z2 (psiAut1 α.val (a,b,c))
    simp [psiAut1, he, diagonal]

theorem normalForm_mem_N2_iff (d e : ParkerLoop) (α : ParkerStandardGroup) :
    (normalForm d e α).val ∈ N2 ↔ α.val parkerOmega = parkerOmega := by
  change psiAut1N α * psi2N e * psi1N d ∈ N2 ↔ _
  rw [N2.mul_mem_cancel_right (psi1N_mem_N2 d),
    N2.mul_mem_cancel_right (psi2N_mem_N2 e), psiAut1N_mem_N2_iff]

private def secondCode (x : Triple) : Option golay := x.2.1.map Prod.fst

private theorem Q2_fixes_secondCode {g : N} (hg : g ∈ Q2) (x : Triple) :
    secondCode (g.val x) = secondCode x := by
  induction hg using Subgroup.closure_induction generalizing x with
  | mem g hg =>
    rcases hg with ⟨d,rfl⟩ | ⟨α,hα,hg⟩
    · rcases x with ⟨a,b,c⟩
      change secondCode (psi2 d (a,b,c)) = _
      cases b <;> simp [secondCode, normalForm_sandwich, parkerSign]
    · rw [hg]
      rcases x with ⟨a,b,c⟩
      by_cases hpar : α parkerOmega = parkerOmega <;> cases b <;>
        simp [secondCode, psiAut2, hpar, diagonal, flip2, hα.2, loopInverse, parkerSign]
  | one => rfl
  | mul g h _ _ ihg ihh => exact (ihg (h.val x)).trans (ihh x)
  | inv g _ ih =>
    have ht := ih (g.val.symm x)
    simpa only [Subgroup.coe_inv, Equiv.Perm.inv_def, Equiv.apply_symm_apply] using ht.symm

private theorem normalForm_secondCode (d e : ParkerLoop) (α : ParkerStandardGroup)
    (hα : α.val parkerOmega = parkerOmega) (x : Triple) :
    secondCode ((normalForm d e α).val.val x) =
      (secondCode x).map (fun a => parkerCodeEquiv (parkerStandardProjection α) (d.1 + a)) := by
  rcases x with ⟨a,b,c⟩
  cases b <;>
    simp [secondCode, normalForm, psiAut1N, psi1N, psi2N, psiAut1, hα, diagonal,
      parkerStandardProjection_spec, parkerLoopMultiply, parkerMultiply]
  rw [add_comm ((parkerCodeEquiv (parkerStandardProjection α)) (loopInverse e).1),
    add_assoc, parkerGolay_add_self, add_zero]

theorem normalForm_Q2_parameters (d e : ParkerLoop) (α : ParkerStandardGroup)
    (hg : (normalForm d e α).val ∈ Q2) :
    d.1 = 0 ∧ parkerStandardProjection α = 1 := by
  have hα := (normalForm_mem_N2_iff d e α).mp (Q2_le_N2 hg)
  have hc (a : golay) : parkerCodeEquiv (parkerStandardProjection α) (d.1 + a) = a := by
    have ht := Q2_fixes_secondCode hg (axis2 (a,0))
    rw [normalForm_secondCode d e α hα] at ht
    exact Option.some.inj ht
  have hd : d.1 = 0 := by
    apply (parkerCodeEquiv (parkerStandardProjection α)).injective
    simpa only [add_zero, map_zero] using hc 0
  refine ⟨hd, parkerCodeEquiv_faithful _ 1 ?_⟩
  intro a
  simpa only [hd, zero_add, parkerCodeEquiv_one] using hc a

/-- Elements that translate the first-coordinate Golay code. -/
private def codeTranslations : Subgroup N where
  carrier := {g | ∃ t : golay, ∀ x : Triple,
    firstCode (g.val x) = (firstCode x).map (fun a => a + t)}
  one_mem' := ⟨0, by intro x; simp⟩
  mul_mem' := by
    rintro g h ⟨s,hs⟩ ⟨t,ht⟩
    refine ⟨t+s, ?_⟩
    intro x
    change firstCode (g.val (h.val x)) = _
    rw [hs, ht, Option.map_map]
    simp only [Function.comp_def, add_assoc]
  inv_mem' := by
    rintro g ⟨t,ht⟩
    refine ⟨t, ?_⟩
    intro x
    have he := congrArg (Option.map (fun a : golay => a+t)) (ht (g.val.symm x))
    simp only [Equiv.apply_symm_apply, Option.map_map, Function.comp_def,
      add_assoc, parkerGolay_add_self, add_zero] at he
    simpa using he.symm

private theorem normalForm_mem_codeTranslations_iff (d e : ParkerLoop) (α : ParkerStandardGroup) :
    (normalForm d e α).val ∈ codeTranslations ↔ parkerStandardProjection α = 1 := by
  constructor
  · rintro ⟨t,ht⟩
    have hc (a : golay) : parkerCodeEquiv (parkerStandardProjection α) (a+e.1) = a+t := by
      have hh := ht (axis1 (a,0))
      rw [normalForm_firstCode] at hh
      exact Option.some.inj hh
    have h0 : parkerCodeEquiv (parkerStandardProjection α) e.1 = t := by
      simpa only [zero_add] using hc 0
    apply parkerCodeEquiv_faithful _ 1
    intro a
    have hh := hc a
    rw [map_add,h0] at hh
    simpa only [parkerCodeEquiv_one] using add_right_cancel hh
  · intro hα
    refine ⟨e.1, ?_⟩
    intro x
    rw [normalForm_firstCode, hα]
    simp only [parkerCodeEquiv_one]

private theorem R_le_codeTranslations : R ≤ codeTranslations := by
  apply sup_le
  · intro g hg
    exact ⟨0, by intro x; simpa using Q1_fixes_firstCode hg.1 x⟩
  · intro g hg
    obtain ⟨⟨d,e,α⟩,he⟩ := normalForm_surjective ⟨g,hg.2⟩
    have hev : (normalForm d e α).val = g := congrArg Subtype.val he
    rw [← hev, normalForm_mem_codeTranslations_iff]
    exact (normalForm_Q2_parameters d e α (hev.symm ▸ hg.1)).2

/-- Every radical element is an actual collected word with even cocode. -/
theorem R_collection (g : N) (hg : g ∈ R) :
    ∃ d e : ParkerLoop, ∃ a : Cocode, EvenCocode a ∧
      (normalForm d e (parkerCocodeStandard a)).val = g := by
  obtain ⟨⟨d,e,α⟩,he⟩ := normalForm_surjective ⟨g,R_le_N1 hg⟩
  have hev : (normalForm d e α).val = g := congrArg Subtype.val he
  have hp := (normalForm_mem_codeTranslations_iff d e α).mp
    (hev.symm ▸ R_le_codeTranslations hg)
  obtain ⟨a,ha⟩ := (isSignAutomorphism_iff_cocode α.val).mp
    ((parkerStandardProjection_eq_one_iff α).mp hp)
  have ha' : parkerCocodeStandard a = α := Subtype.ext ha
  refine ⟨d,e,a,?_,by rw [ha']; exact hev⟩
  apply (evenCocode_iff a).mpr
  rw [ha']
  exact (normalForm_mem_N2_iff d e α).mp (hev.symm ▸ R_le_N2 hg)

/-- Exact parameterization of the source radical, before applying the bar convention. -/
theorem mem_R_iff (g : N) : g ∈ R ↔
    ∃ d e : ParkerLoop, ∃ a : Cocode, EvenCocode a ∧
      (normalForm d e (parkerCocodeStandard a)).val = g := by
  constructor
  · exact R_collection g
  · rintro ⟨d,e,a,ha,rfl⟩
    exact normalForm_mem_R d e a ha

/-- Even cocode automorphisms are also second-family generators. -/
theorem evenCocode_mem_Q2 (a : Cocode) (ha : EvenCocode a) :
    psiAut1N (parkerCocodeStandard a) ∈ Q2 := by
  apply Subgroup.subset_closure
  right
  refine ⟨(parkerCocodeStandard a).val,
    (parkerStandardProjection_eq_one_iff _).mp (parkerCocodeStandard_projection a), ?_⟩
  change psiAut1 (parkerCocodeStandard a).val = psiAut2 (parkerCocodeStandard a).val
  simp only [psiAut1, psiAut2, if_pos ((evenCocode_iff a).mp ha)]

/-- The first source factor is normal relative to the actual radical. -/
theorem firstFactor_normal : ((Q1 ⊓ N2).subgroupOf R).Normal := by
  refine ⟨?_⟩
  intro x hx g
  constructor
  · have ht := Q1_normal_in_N1.conj_mem
      (⟨x.val,R_le_N1 x.prop⟩ : N1) hx.1 (⟨g.val,R_le_N1 g.prop⟩ : N1)
    exact ht
  · exact R_le_N2 (R.mul_mem (R.mul_mem g.prop x.prop) (R.inv_mem g.prop))

/-- The source definition is a setwise product, in its literal factor order. -/
theorem mem_R_iff_product (g : N) : g ∈ R ↔
    ∃ x ∈ Q1 ⊓ N2, ∃ y ∈ Q2 ⊓ N1, x * y = g := by
  constructor
  · intro hg
    obtain ⟨d,e,a,ha,rfl⟩ := R_collection g hg
    let y := psiAut1N (parkerCocodeStandard a) * psi2N e
    have hy : y ∈ Q2 ⊓ N1 := ⟨
      Q2.mul_mem (evenCocode_mem_Q2 a ha) (Subgroup.subset_closure (Or.inl ⟨e,rfl⟩)),
      N1.mul_mem (psiAut1N_mem_N1 _) (psi2N_mem_N1 e)⟩
    have hyr : y ∈ R := (show Q2 ⊓ N1 ≤ R from le_sup_right) hy
    have hd : psi1N d ∈ Q1 ⊓ N2 :=
      ⟨Subgroup.subset_closure (Or.inl ⟨d,rfl⟩), psi1N_mem_N2 d⟩
    have hconj := firstFactor_normal.conj_mem
      (⟨psi1N d,psi1N_mem_R d⟩ : R) hd (⟨y,hyr⟩ : R)
    refine ⟨y * psi1N d * y⁻¹, hconj, y, hy, ?_⟩
    change y * psi1N d * y⁻¹ * y = y * psi1N d
    rw [inv_mul_cancel_right]
  · rintro ⟨x,hx,y,hy,rfl⟩
    exact R.mul_mem ((show Q1 ⊓ N2 ≤ R from le_sup_left) hx)
      ((show Q2 ⊓ N1 ≤ R from le_sup_right) hy)

/-- Equality with the setwise product in 14.5, before passing to `N/K`. -/
theorem R_eq_set_product : (R : Set N) = (Q1 ⊓ N2 : Subgroup N) * (Q2 ⊓ N1 : Subgroup N) := by
  ext g
  exact mem_R_iff_product g

end Sporadic.Monster.Construction.NOctad.LocalStructure.Radical
