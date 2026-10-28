module

public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.HigherFieldResiduals
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Flag preservation for repeated natural SL₃ modules

A binary intertwiner on positively many copies of the natural module distinguishes
point and line flags by fixed vectors of the derived parabolics. Sylow alignment
handles arbitrary group coordinates and the proof permits either natural/dual
coordinate orientation supplied by the group equivalence.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.6 module
application before 13.6.14 and the parabolic argument in 13.6.19,
printed pp.929–931.
-/

@[expose] public section

open Matrix Subgroup
open scoped MatrixGroups commutatorElement
namespace Representation.SL3RepeatedNaturalFlagTypes
variable {F : Type*} [Field F] [Finite F]
open Matrix.PSL3.LinearThree

private def pointScalar : pointParabolicSL F →* F where
  toFun g := g.val.val 0 0
  map_one' := by simp
  map_mul' g h := by
    have hh := (mem_pointParabolicSL_iff F h).mp h.property
    simp [Matrix.mul_apply, Fin.sum_univ_three, hh.1, hh.2]

private theorem point_derived_le :
    ⁅pointParabolicSL F, pointParabolicSL F⁆ ≤ pointLocalSL F := by
  rw [← (pointParabolicSL F).range_subtype, ← map_commutator_eq]
  rintro g ⟨x, hx, rfl⟩
  have he := Abelianization.commutator_subset_ker (pointScalar (F := F)).toHomUnits hx
  have he' := congrArg (fun u : Fˣ => (u : F)) he
  exact (mem_pointLocalSL_iff F x).mpr
    ⟨he', (mem_pointParabolicSL_iff F x).mp x.property⟩

private theorem line_derived_fixed_eq_zero [CharP F 2] (v : Fin 3 → F)
    (hv : ∀ g ∈ ⁅lineParabolicSL F, lineParabolicSL F⁆, g.val.mulVec v = v) : v = 0 := by
  let x := SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) (1 : F)
  let y := SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (1 : F)
  let z := SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) (1 : F)
  have hx : x ∈ lineParabolicSL F := by
    rw [mem_lineParabolicSL_iff]
    simp [x, SpecialLinearGroup.transvection_coe]
  have hy : y ∈ lineParabolicSL F := by
    rw [mem_lineParabolicSL_iff]
    simp [y, SpecialLinearGroup.transvection_coe]
  have hz : z ∈ lineParabolicSL F := by
    rw [mem_lineParabolicSL_iff]
    simp [z, SpecialLinearGroup.transvection_coe]
  have hxy := hv ⁅x, y⁆ (commutator_mem_commutator hx hy)
  have hyz := hv ⁅y, z⁆ (commutator_mem_commutator hy hz)
  have h0 := congrFun hxy 0
  have h1 := congrFun hxy 1
  have h2 := congrFun hyz 1
  simp [commutatorElement_def, x, y, z, SpecialLinearGroup.transvection_inv,
    SpecialLinearGroup.transvection_coe,
    Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    CharTwo.neg_eq, CharTwo.add_self_eq_zero] at h0 h1 h2
  ext i
  fin_cases i <;> simp_all

private def HasDerivedFixed (r : ℕ) (P : Subgroup SL(3, F)) : Prop :=
  ∃ w : Fin r → Fin 3 → F, w ≠ 0 ∧
    ∀ g ∈ ⁅P, P⁆, (fun i => g.val.mulVec (w i)) = w

private theorem point_hasDerivedFixed {r : ℕ} (hr : 0 < r) :
    HasDerivedFixed r (pointParabolicSL F) := by
  refine ⟨fun _ => ![1, 0, 0], ?_, ?_⟩
  · intro h
    have h' := congrFun (congrFun h ⟨0, hr⟩) 0
    exact one_ne_zero h'
  · intro g hg
    funext i
    exact point_derived_le hg

private theorem line_not_hasDerivedFixed [CharP F 2] (r : ℕ) :
    ¬ HasDerivedFixed r (lineParabolicSL F) := by
  rintro ⟨w, hw, hf⟩
  apply hw
  funext i
  exact line_derived_fixed_eq_zero (w i) (fun g hg => congrFun (hf g hg) i)

omit [Finite F] in
private theorem hasDerivedFixed_map_iff {r : ℕ}
    (a : MulAut SL(3, F))
    (b : (Fin r → Fin 3 → F) ≃+ (Fin r → Fin 3 → F))
    (hb : ∀ g w, b (fun i => g.val.mulVec (w i)) =
      fun i => (a g).val.mulVec ((b w) i)) (P : Subgroup SL(3, F)) :
    HasDerivedFixed r (P.map a.toMonoidHom) ↔ HasDerivedFixed r P := by
  constructor
  · rintro ⟨w, hw, hf⟩
    refine ⟨b.symm w, fun he => hw (by simpa using congrArg b he), ?_⟩
    intro g hg
    apply b.injective
    rw [hb]
    simpa only [b.apply_symm_apply] using
      hf (a g) (by rw [← map_commutator]; exact mem_map_of_mem _ hg)
  · rintro ⟨w, hw, hf⟩
    refine ⟨b w, fun he => hw (b.injective (he.trans b.map_zero.symm)), ?_⟩
    intro g hg
    rw [← map_commutator] at hg
    obtain ⟨x, hx, rfl⟩ := hg
    exact (hb x w).symm.trans (congrArg b (hf x hx))

private def innerOperator (r : ℕ) (c : SL(3, F)) :
    (Fin r → Fin 3 → F) ≃+ (Fin r → Fin 3 → F) :=
  (LinearEquiv.piCongrRight (fun _ : Fin r => SpecialLinearGroup.toLin' c)).toAddEquiv

omit [Finite F] in
private theorem innerOperator_intertwines (r : ℕ) (c g : SL(3, F))
    (w : Fin r → Fin 3 → F) :
    innerOperator r c (fun i => g.val.mulVec (w i)) =
      fun i => ((MulAut.conj c) g).val.mulVec ((innerOperator r c w) i) := by
  funext i
  change (SpecialLinearGroup.toLin' c) ((SpecialLinearGroup.toLin' g) (w i)) =
    (SpecialLinearGroup.toLin' (c * g * c⁻¹)) ((SpecialLinearGroup.toLin' c) (w i))
  simp [map_mul]

variable {E : Type*} [Field E] [Finite E]

omit [Finite F] in
private theorem coatom_image_eq_or
    (f : SL(3, F) ≃* SL(3, E)) (hB : (borelSL F).map f.toMonoidHom = borelSL E)
    (P : Subgroup SL(3, F)) (hP : IsCoatom P) (hBP : borelSL F ≤ P) :
    P.map f.toMonoidHom = pointParabolicSL E ∨
      P.map f.toMonoidHom = lineParabolicSL E := by
  have hm := (OrderIso.isCoatom_iff f.mapSubgroup P).mpr hP
  have hBP' : borelSL E ≤ P.map f.toMonoidHom := hB ▸ map_mono hBP
  rcases BorelOvergroups.overgroup_borelSL E _ hBP' hm.ne_top with hp | hl
  · exact Or.inl ((hm.le_iff_eq (pointParabolicSL_isCoatom E).ne_top).mp hp).symm
  · exact Or.inr ((hm.le_iff_eq (lineParabolicSL_isCoatom E).ne_top).mp hl).symm

private theorem parabolics_ne : pointParabolicSL F ≠ lineParabolicSL F := by
  intro he
  have ht := parabolicsSL_sup_eq_top F
  rw [he, sup_idem] at ht
  exact (lineParabolicSL_isCoatom F).ne_top ht

private theorem exists_borel_alignment [CharP F 2] [CharP E 2]
    (f : SL(3, F) ≃* SL(3, E)) :
    ∃ c : SL(3, E), (borelSL F).map (f.trans (MulAut.conj c)).toMonoidHom = borelSL E := by
  classical
  let := Fintype.ofFinite F
  let := Fintype.ofFinite E
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, _, hm⟩ := FiniteField.card F 2
  obtain ⟨n, _, hn⟩ := FiniteField.card E 2
  rw [← Nat.card_eq_fintype_card] at hm hn
  let S := (Matrix.PSL3.CartanActions.BorelQuotient.unipotentSLSylow F m.pos hm).mapSurjective
    (f := f.toMonoidHom) f.surjective
  obtain ⟨c, hc, _⟩ :=
    Matrix.PSL3.CartanActions.BorelQuotient.sylowSL_normalizer_conjugate E n.pos hn S
  have hc' : (unipotentSL E).map (MulAut.conj c).toMonoidHom =
      (unipotentSL F).map f.toMonoidHom := hc
  have hu : (unipotentSL F).map (f.trans (MulAut.conj c).symm).toMonoidHom =
      unipotentSL E := by
    change (unipotentSL F).map ((MulAut.conj c).symm.toMonoidHom.comp f.toMonoidHom) = _
    rw [← Subgroup.map_map, ← hc']
    exact (MulAut.conj c).mapSubgroup.symm_apply_apply _
  refine ⟨c⁻¹, ?_⟩
  have he : (MulAut.conj c).symm = MulAut.conj c⁻¹ := by
    ext x
    simp [MulAut.conj_symm_apply]
  rw [he] at hu
  rw [← normalizer_unipotentSL F, map_equiv_normalizer_eq, hu, normalizer_unipotentSL]

/-- A binary normalizer of positively repeated natural modules fixes both flag
types, even with an arbitrary identification of the acting special linear group. -/
theorem flags_of_intertwiner [CharP F 2] [CharP E 2] [Algebra (ZMod 2) E]
    (a : MulAut SL(3, F)) (hU : (unipotentSL F).map a.toMonoidHom = unipotentSL F)
    (f : SL(3, F) ≃* SL(3, E)) {r : ℕ} (hr : 0 < r)
    (b : (Fin r → Fin 3 → E) ≃ₗ[ZMod 2] (Fin r → Fin 3 → E))
    (hb : ∀ g w, b (fun i => (f g).val.mulVec (w i)) =
      fun i => (f (a g)).val.mulVec ((b w) i)) :
    (pointParabolicSL F).map a.toMonoidHom = pointParabolicSL F ∧
      (lineParabolicSL F).map a.toMonoidHom = lineParabolicSL F := by
  let α : MulAut SL(3, E) := f.symm.trans (a.trans f)
  have hα : ∀ g w, b.toAddEquiv (fun i => g.val.mulVec (w i)) =
      fun i => (α g).val.mulVec ((b.toAddEquiv w) i) := by
    intro g w
    simpa [α] using hb (f.symm g) w
  let Sig (P : Subgroup SL(3, F)) := HasDerivedFixed r (P.map f.toMonoidHom)
  have hinv (P : Subgroup SL(3, F)) : Sig (P.map a.toMonoidHom) ↔ Sig P := by
    have hm : (P.map a.toMonoidHom).map f.toMonoidHom =
        (P.map f.toMonoidHom).map α.toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext g
      simp [α]
    change HasDerivedFixed r ((P.map a.toMonoidHom).map f.toMonoidHom) ↔ _
    rw [hm]
    exact hasDerivedFixed_map_iff α b.toAddEquiv hα (P.map f.toMonoidHom)
  obtain ⟨c, hc⟩ := exists_borel_alignment f
  let d := f.trans (MulAut.conj c)
  have hd : (borelSL F).map d.toMonoidHom = borelSL E := hc
  have hsig (P : Subgroup SL(3, F)) :
      HasDerivedFixed r (P.map d.toMonoidHom) ↔ Sig P := by
    change HasDerivedFixed r (P.map ((MulAut.conj c).toMonoidHom.comp f.toMonoidHom)) ↔ _
    rw [← Subgroup.map_map]
    exact hasDerivedFixed_map_iff (MulAut.conj c) (innerOperator r c)
      (innerOperator_intertwines r c) _
  have hp := coatom_image_eq_or d hd _ (pointParabolicSL_isCoatom F) inf_le_left
  have hl := coatom_image_eq_or d hd _ (lineParabolicSL_isCoatom F) inf_le_right
  have hdiff : ¬ (Sig (pointParabolicSL F) ↔ Sig (lineParabolicSL F)) := by
    intro hs
    have hs' := (hsig (pointParabolicSL F)).trans (hs.trans (hsig (lineParabolicSL F)).symm)
    rcases hp with hp | hp <;> rcases hl with hl | hl
    · exact parabolics_ne (map_injective d.injective (hp.trans hl.symm))
    · rw [hp, hl] at hs'
      exact line_not_hasDerivedFixed r (hs'.mp (point_hasDerivedFixed hr))
    · rw [hp, hl] at hs'
      exact line_not_hasDerivedFixed r (hs'.mpr (point_hasDerivedFixed hr))
    · exact parabolics_ne (map_injective d.injective (hp.trans hl.symm))
  have hB : (borelSL F).map a.toMonoidHom = borelSL F := by
    rw [← normalizer_unipotentSL F, map_equiv_normalizer_eq, hU]
  have hpA := coatom_image_eq_or a hB _ (pointParabolicSL_isCoatom F) inf_le_left
  have hlA := coatom_image_eq_or a hB _ (lineParabolicSL_isCoatom F) inf_le_right
  have hpEq : (pointParabolicSL F).map a.toMonoidHom = pointParabolicSL F := by
    rcases hpA with h | h
    · exact h
    · have hh := (hinv (pointParabolicSL F)).symm
      rw [h] at hh
      exact (hdiff hh).elim
  refine ⟨hpEq, ?_⟩
  rcases hlA with h | h
  · exact (parabolics_ne (map_injective a.injective (hpEq.trans h.symm))).elim
  · exact h
end Representation.SL3RepeatedNaturalFlagTypes
