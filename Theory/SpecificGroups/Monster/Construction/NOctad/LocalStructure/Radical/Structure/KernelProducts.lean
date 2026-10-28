module

public import Theory.SpecificGroups.Monster.Construction.NOctad.LocalStructure.Radical.Structure.Action

/-!
# The full source kernel as an actual setwise product

Collection promotes the exact word calculation to the entire radical. The
loop-generated source factor and the octad cocode annihilator fix the block;
conversely every kernel element collects into one element of each factor.
Thus the assertion is equality of setwise products, in both action conventions.
The result descends through the actual bar map, retaining comparison with the
previously published `barredEcPlus`. The unbarred kernel is normal relative
to `R` and contains the original quotient kernel `K`.

Source: Aschbacher, *Sporadic Groups*, Lemma 29.13(4), printed pp. 160–161,
with the bar convention from Section 27, printed p. 144.
-/

@[expose] public section
open scoped Pointwise
noncomputable section
namespace Sporadic.Monster.Construction.NOctad.LocalStructure.Radical
open TrialitySpin Atlas.Codes Atlas.Fischer
/-- The prescribed loop products in the source, reversed for left composition. -/
def sourceLoopGenerators (c : Octad) : Set N := {g | ∃ d e : ParkerLoop,
  (c.val.val * d.1.val = 0 ∨ c.val.val * d.1.val = c.val.val) ∧
  (c.val.val * e.1.val = 0 ∨ c.val.val * e.1.val = c.val.val) ∧
  g = psi2N e * psi1N d}

/-- The loop-generated factor in the source block kernel. -/
def sourceLoopSubgroup (c : Octad) : Subgroup N := Subgroup.closure (sourceLoopGenerators c)

/-- Pull back the literal relative kernel and view it in the original group `N`. -/
def kernelPreimage (h : GeneratorLaws) (c : Octad) : Subgroup N :=
  ((relativeKernel h c).comap radicalBarMap).map R.subtype

theorem sourceLoopSubgroup_le_R (c : Octad) : sourceLoopSubgroup c ≤ R := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨d,e,_,_,rfl⟩
  exact R.mul_mem (psi2N_mem_R e) (psi1N_mem_R d)

theorem kernelPreimage_le_R (h : GeneratorLaws) (c : Octad) : kernelPreimage h c ≤ R := by
  rintro g ⟨q,_,rfl⟩
  exact q.prop

theorem kernelPreimage_subgroupOf (h : GeneratorLaws) (c : Octad) :
    (kernelPreimage h c).subgroupOf R = (relativeKernel h c).comap radicalBarMap :=
  Subgroup.comap_map_eq_self_of_injective R.subtype_injective _

/-- Normality is relative to the source radical, not asserted in the whole `N`. -/
instance kernelPreimage_normal (h : GeneratorLaws) (c : Octad) :
    ((kernelPreimage h c).subgroupOf R).Normal := by
  rw [kernelPreimage_subgroupOf]
  infer_instance

private theorem psi1_one : psi1N loopOne = 1 := by
  apply Subtype.ext
  ext ⟨a,b,c⟩ : 1
  change psi1 loopOne (a,b,c) = (a,b,c)
  simp

private theorem psi2_one : psi2N loopOne = 1 := by
  apply Subtype.ext
  ext ⟨a,b,c⟩ : 1
  change psi2 loopOne (a,b,c) = (a,b,c)
  simp

private theorem cocode_zero : psiAut1N (parkerCocodeStandard 0) = 1 := by
  have h0 : parkerCocodeStandard 0 = 1 := map_one parkerCocodeEmbedding
  rw [h0]
  apply Subtype.ext
  ext ⟨a,b,c⟩ : 1
  change psiAut1 (1 : ParkerStandardGroup).val (a,b,c) = (a,b,c)
  simp [psiAut1, diagonal]

private theorem even_zero : EvenCocode 0 := by simp [EvenCocode, cocodePairing]

theorem mem_kernelPreimage (h : GeneratorLaws) (c : Octad) (g : R) :
    g.val ∈ kernelPreimage h c ↔ radicalBarMap g ∈ relativeKernel h c := by
  constructor
  · rintro ⟨q,hq,he⟩
    have he' : q = g := Subtype.ext he
    exact he' ▸ hq
  · intro hg
    exact ⟨g,hg,rfl⟩

theorem normalForm_mem_kernelPreimage_iff (h : GeneratorLaws) (c : Octad)
    (d e : ParkerLoop) (a : Cocode) (ha : EvenCocode a) :
    (normalForm d e (parkerCocodeStandard a)).val ∈ kernelPreimage h c ↔
      KernelParameters c d e a := by
  rw [mem_kernelPreimage h c
    ⟨(normalForm d e (parkerCocodeStandard a)).val,normalForm_mem_R d e a ha⟩]
  exact relativeKernel_word_iff h c d e a ha

/-- Collection upgrades the word criterion to the full source kernel. -/
theorem mem_kernelPreimage_iff (h : GeneratorLaws) (c : Octad) (g : N) :
    g ∈ kernelPreimage h c ↔ ∃ d e : ParkerLoop, ∃ a : Cocode,
      EvenCocode a ∧ KernelParameters c d e a ∧
      (normalForm d e (parkerCocodeStandard a)).val = g := by
  constructor
  · intro hg
    obtain ⟨q,hq,he⟩ := hg
    obtain ⟨d,e,a,ha,hw⟩ := R_collection q.val q.prop
    have hg' : (normalForm d e (parkerCocodeStandard a)).val ∈ kernelPreimage h c :=
      hw.symm ▸ (show q.val ∈ kernelPreimage h c from ⟨q,hq,rfl⟩)
    exact ⟨d,e,a,ha,(normalForm_mem_kernelPreimage_iff h c d e a ha).mp hg',hw.trans he⟩
  · rintro ⟨d,e,a,ha,hk,rfl⟩
    exact (normalForm_mem_kernelPreimage_iff h c d e a ha).mpr hk

theorem sourceLoopSubgroup_le_kernelPreimage (h : GeneratorLaws) (c : Octad) :
    sourceLoopSubgroup c ≤ kernelPreimage h c := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨d,e,hd,he,rfl⟩
  have hw : (normalForm d e (parkerCocodeStandard 0)).val = psi2N e * psi1N d := by
    change psiAut1N (parkerCocodeStandard 0) * psi2N e * psi1N d = _
    rw [cocode_zero,one_mul]
  rw [← hw]
  exact (normalForm_mem_kernelPreimage_iff h c d e 0 even_zero).mpr
    ⟨hd,he,by simp [cocodePairing]⟩

/-- In particular the entire source four-group belongs to the loop factor. -/
theorem Z_le_sourceLoopSubgroup (c : Octad) : Z ≤ sourceLoopSubgroup c := by
  have h1 : z1N ∈ sourceLoopSubgroup c := by
    apply Subgroup.subset_closure
    refine ⟨loopPi,loopOne,Or.inl ?_,Or.inl ?_,?_⟩
    · change c.val.val * 0 = 0
      exact mul_zero _
    · change c.val.val * 0 = 0
      exact mul_zero _
    · rw [psi2_one,one_mul]
      rfl
  have h2 : z2N ∈ sourceLoopSubgroup c := by
    apply Subgroup.subset_closure
    refine ⟨loopOne,loopPi,Or.inl ?_,Or.inl ?_,?_⟩
    · change c.val.val * 0 = 0
      exact mul_zero _
    · change c.val.val * 0 = 0
      exact mul_zero _
    · rw [psi1_one,mul_one]
      rfl
  apply (Subgroup.closure_le _).mpr
  rintro g (rfl | rfl | rfl)
  · exact h1
  · exact h2
  · apply ((sourceLoopSubgroup c).mul_mem_cancel_left ((sourceLoopSubgroup c).mul_mem h1 h2)).mp
    rw [z1N_z2N_z3N]
    exact (sourceLoopSubgroup c).one_mem

/-- The full octad annihilator, including `Z`, acts trivially on this block. -/
theorem EcPlus_le_kernelPreimage (h : GeneratorLaws) (c : Octad) :
    EcPlus c ≤ kernelPreimage h c := by
  apply sup_le
  · exact (Z_le_sourceLoopSubgroup c).trans (sourceLoopSubgroup_le_kernelPreimage h c)
  · apply (Subgroup.closure_le _).mpr
    rintro g ⟨a,ha,hca,rfl⟩
    have hw : (normalForm loopOne loopOne (parkerCocodeStandard a)).val =
        psiAut1N (parkerCocodeStandard a) := by
      change psiAut1N (parkerCocodeStandard a) * psi2N loopOne * psi1N loopOne = _
      rw [psi1_one,psi2_one,mul_one,mul_one]
    rw [← hw]
    exact (normalForm_mem_kernelPreimage_iff h c loopOne loopOne a ha).mpr
      ⟨Or.inl (mul_zero _),Or.inl (mul_zero _),hca⟩

/-- The kernel is exactly the source setwise product, not just its generated join. -/
theorem kernelPreimage_eq_set_product (h : GeneratorLaws) (c : Octad) :
    (kernelPreimage h c : Set N) = (EcPlus c : Set N) * (sourceLoopSubgroup c : Set N) := by
  ext g
  constructor
  · intro hg
    obtain ⟨d,e,a,ha,hk,rfl⟩ := (mem_kernelPreimage_iff h c g).mp hg
    refine ⟨psiAut1N (parkerCocodeStandard a),?_,psi2N e * psi1N d,?_,?_⟩
    · apply (show Subgroup.closure (octadCocodeGenerators c) ≤ EcPlus c from le_sup_right)
      exact Subgroup.subset_closure ⟨a,ha,hk.2.2,rfl⟩
    · exact Subgroup.subset_closure ⟨d,e,hk.1,hk.2.1,rfl⟩
    · exact (mul_assoc _ _ _).symm
  · rintro ⟨x,hx,y,hy,rfl⟩
    exact (kernelPreimage h c).mul_mem (EcPlus_le_kernelPreimage h c hx)
      (sourceLoopSubgroup_le_kernelPreimage h c hy)

/-- The source loop factor inside the literal barred radical. -/
def barredSourceLoops (c : Octad) : Subgroup barredR :=
  (sourceLoopSubgroup c).comap R.subtype |>.map radicalBarMap

/-- The source octad annihilator inside the same barred radical. -/
def barredKernelAnnihilator (c : Octad) : Subgroup barredR :=
  (EcPlus c).comap R.subtype |>.map radicalBarMap

/-- The full kernel formula of 29.13(4) in the genuine barred actor. -/
theorem relativeKernel_eq_set_product (h : GeneratorLaws) (c : Octad) :
    (relativeKernel h c : Set barredR) =
      (barredKernelAnnihilator c : Set barredR) * (barredSourceLoops c : Set barredR) := by
  ext g
  constructor
  · intro hg
    obtain ⟨q,rfl⟩ := radicalBarMap_surjective g
    have hq : q.val ∈ kernelPreimage h c := (mem_kernelPreimage h c q).mpr hg
    change q.val ∈ (kernelPreimage h c : Set N) at hq
    rw [kernelPreimage_eq_set_product h c] at hq
    obtain ⟨x,hx,y,hy,hxy⟩ := hq
    have hyr : y ∈ R := sourceLoopSubgroup_le_R c hy
    let xr : R := ⟨x,EcPlus_le_R c hx⟩
    let yr : R := ⟨y,hyr⟩
    refine ⟨radicalBarMap xr,⟨xr,hx,rfl⟩,radicalBarMap yr,⟨yr,hy,rfl⟩,?_⟩
    change radicalBarMap xr * radicalBarMap yr = radicalBarMap q
    rw [← map_mul]
    exact congrArg radicalBarMap (Subtype.ext hxy)
  · rintro ⟨x,⟨xr,hxr,rfl⟩,y,⟨yr,hyr,rfl⟩,rfl⟩
    apply (relativeKernel h c).mul_mem
    · exact (mem_kernelPreimage h c xr).mp (EcPlus_le_kernelPreimage h c hxr)
    · exact (mem_kernelPreimage h c yr).mp (sourceLoopSubgroup_le_kernelPreimage h c hyr)

/-- The annihilator factor agrees with the previously published literal image. -/
theorem barredKernelAnnihilator_map_subtype (c : Octad) :
    (barredKernelAnnihilator c).map barredR.subtype = barredEcPlus c := by
  ext g
  constructor
  · rintro ⟨x,⟨q,hq,rfl⟩,rfl⟩
    exact ⟨⟨q.val,R_le_N1 q.prop⟩,hq,rfl⟩
  · rintro ⟨q,hq,rfl⟩
    let qr : R := ⟨q.val,EcPlus_le_R c hq⟩
    exact ⟨radicalBarMap qr,⟨qr,hq,rfl⟩,rfl⟩

/-- The source kernel contains the original four-group killed by the bar map. -/
theorem K_le_kernelPreimage (h : GeneratorLaws) (c : Octad) : TrialitySpin.K ≤ kernelPreimage h c := by
  intro g hg
  let gr : R := ⟨g,K_le_R hg⟩
  have he : radicalBarMap gr = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change nQuotientMap g = 1
    exact (QuotientGroup.eq_one_iff g).mpr hg
  apply (mem_kernelPreimage h c gr).mpr
  rw [he]
  exact (relativeKernel h c).one_mem

/-- Reversing the right-action source convention gives the same setwise product. -/
theorem kernelPreimage_eq_set_product_rev (h : GeneratorLaws) (c : Octad) :
    (kernelPreimage h c : Set N) = (sourceLoopSubgroup c : Set N) * (EcPlus c : Set N) := by
  have he := congrArg (fun s : Set N => s⁻¹) (kernelPreimage_eq_set_product h c)
  simpa only [mul_inv_rev, inv_coe_set] using he

/-- Both product orders agree in the literal barred actor. -/
theorem relativeKernel_eq_set_product_rev (h : GeneratorLaws) (c : Octad) :
    (relativeKernel h c : Set barredR) =
      (barredSourceLoops c : Set barredR) * (barredKernelAnnihilator c : Set barredR) := by
  have he := congrArg (fun s : Set barredR => s⁻¹) (relativeKernel_eq_set_product h c)
  simpa only [mul_inv_rev, inv_coe_set] using he

end Sporadic.Monster.Construction.NOctad.LocalStructure.Radical
