module
public import Theory.SpecificGroups.SymplecticFour.RootHyperplaneComparison
/-!
# Paired displacement on a symplectic root hyperplane

If the hyperplane displacement and the marked root both lie in a subgroup K,
but the total displacement escapes K, the hyperplane displacement is exactly
the root. Orthogonality excludes a two-dimensional isotropic fixed plane.
Every subactor's hyperplane displacement is then either zero or that whole
field line. All statements retain the injective conjugation marking.

Source: MS93 (3.3)(ii) and the paired calculation in (5.7), pp.867,919.
The original critical-path consumer is Sp4Four.SourceComparison.OriginalPairedDisplacement.
-/

public noncomputable section
open Subgroup Representation
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.TwoLocalCover
namespace Theory.SpecificGroups.SymplecticFour.RootHyperplaneComparison
open scoped commutatorElement
variable {F G : Type*} [Field F] [Group G]
/-- A prescribed displacement bound forces the whole critical root. -/
theorem embedded_hyperplane_commutator_eq_root_of_bound
    (B A K : Subgroup G)
    (j : Multiplicative (Vector F) →* G) (_hj : Function.Injective j)
    (hAr : A ≤ j.range)
    (f : B →* Sp F)
    (hact : ∀ (b : B) v,
      j (Multiplicative.ofAdd (f b • v)) = b.val*j (Multiplicative.ofAdd v)*b.val⁻¹)
    (R : Submodule F (Vector F))
    (hd : Module.finrank F R = 1)
    (hfix : ∀ b : B, ∀ v ∈ R, f b • v=v)
    (hquad : ∀ x y : B, ∀ v ∈ (form F).orthogonal R,
      f x • (f y • v-v)=f y • v-v)
    (hA : ∀ v, j (Multiplicative.ofAdd v) ∈ A ↔ v ∈ (form F).orthogonal R)
    (hline : ∀ v ∈ R, j (Multiplicative.ofAdd v) ∈ K)
    (hbound : ⁅B,A⁆ ≤ K) (hbad : ¬ ⁅B,j.range⁆ ≤ K) :
    ⁅B,A⁆ = (AddSubgroup.toSubgroup' R.toAddSubgroup).map j := by
  let H := (form F).orthogonal R
  let W := ⨆ b : B, H.map (symplecticNatural 2 (f b)-LinearMap.id)
  have hdisp (b : B) v :
      j (Multiplicative.ofAdd (f b • v-v)) = ⁅b.val,j (Multiplicative.ofAdd v)⁆ := by
    rw [ofAdd_sub,map_div,div_eq_mul_inv,hact,commutatorElement_def]
  have hW : ∀ v ∈ W, j (Multiplicative.ofAdd v) ∈ ⁅B,A⁆ := by
    intro v hv
    refine Submodule.iSup_induction _ (motive := fun v => j (Multiplicative.ofAdd v) ∈ ⁅B,A⁆) hv ?_ ?_ ?_
    · intro b w hw
      obtain ⟨v,hv,rfl⟩ := hw
      change j (Multiplicative.ofAdd (f b • v-v)) ∈ _
      rw [hdisp]
      exact commutator_mem_commutator b.property ((hA v).mpr hv)
    · simp
    · intro v w hv hw
      simpa only [ofAdd_add,map_mul] using (⁅B,A⁆).mul_mem hv hw
  have hnot : ¬ displacementSpace f.range ≤ R ⊔ W := by
    intro hle
    apply hbad
    apply commutator_le.mpr
    intro b hb u hu
    obtain ⟨v,rfl⟩ := hu
    have hv : f ⟨b,hb⟩ • v.toAdd-v.toAdd ∈ displacementSpace f.range :=
      Coinvariants.sub_mem_ker (ρ := (symplecticNatural 2).comp f.range.subtype)
        ⟨f ⟨b,hb⟩,⟨_,rfl⟩⟩ v.toAdd
    obtain ⟨r,hr,w,hw,he⟩ := Submodule.mem_sup.mp (hle hv)
    have hh := K.mul_mem (hline r hr) (hbound (hW w hw))
    rw [←map_mul,←ofAdd_add,he,hdisp] at hh
    exact hh
  have hWR : W ≤ R := by
    let Y := f.range
    have hWP : W ≤ displacementSpace Y := by
      apply iSup_le
      intro b v hv
      obtain ⟨w,hw,rfl⟩ := hv
      exact Coinvariants.sub_mem_ker (ρ := (symplecticNatural 2).comp Y.subtype)
        ⟨f b,⟨b,rfl⟩⟩ w
    have hRf : R ≤ fixedSpace Y := by
      rintro v hv y ⟨b,rfl⟩
      exact hfix b v hv
    have hWf : W ≤ fixedSpace Y := by
      apply iSup_le
      intro b v hv
      obtain ⟨w,hw,rfl⟩ := hv
      rintro y ⟨y,rfl⟩
      exact hquad y b w hw
    let P := R ⊔ W
    have hPf : P ≤ fixedSpace Y := sup_le hRf hWf
    have hRR : R ≤ (form F).orthogonal R := by
      have hne : R ≠ ⊥ := by intro h; rw [h,finrank_bot] at hd; omega
      obtain ⟨v,hv,hv0⟩ := R.ne_bot_iff.mp hne
      have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hd hv hv0
      intro x hx y hy
      rw [hspan] at hx hy
      obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hx
      obtain ⟨d,rfl⟩ := Submodule.mem_span_singleton.mp hy
      simp [form_alternating v]
    have hRW : R ≤ (form F).orthogonal W := by
      intro r hr w hw
      exact (orthogonal_displacementSpace Y ▸ hRf hr) w (hWP hw)
    have hWW : W ≤ (form F).orthogonal W := by
      intro v hv w hw
      exact (orthogonal_displacementSpace Y ▸ hWf hv) w (hWP hw)
    have hiso : ∀ v ∈ P, ∀ w ∈ P, form F v w = 0 := by
      intro v hv w hw
      obtain ⟨r,hr,s,hs,rfl⟩ := Submodule.mem_sup.mp hv
      obtain ⟨t,ht,u,hu,rfl⟩ := Submodule.mem_sup.mp hw
      simp only [map_add,LinearMap.add_apply,hRR ht r hr,form_alternating.eq_iff.mp (hRW hr u hu),
        hRW ht s hs,hWW hu s hs,add_zero]
    have hdim := finrank_le_two_of_isotropic P hiso
    have hless : Module.finrank F P < 2 := by
      by_contra! h
      have he : Module.finrank F P = 2 := by omega
      have hPo : (form F).orthogonal P = P := by
        symm
        apply Submodule.eq_of_le_of_finrank_eq
        · exact fun v hv w hw => hiso w hw v hv
        · rw [LinearMap.BilinForm.finrank_orthogonal form_nondegenerate,he]
          simp [Theory.SpecificGroups.SymplecticFour.Vector]
      apply hnot
      intro v hv
      change v ∈ P
      rw [←hPo]
      intro w hw
      exact form_alternating.eq_iff.mp ((orthogonal_displacementSpace Y ▸ hPf hw) v hv)
    have heq : R = P := Submodule.eq_of_le_of_finrank_le le_sup_left (by omega)
    exact (le_sup_right : W ≤ P).trans heq.ge
  have hWne : W ≠ ⊥ := by
    intro hzero
    have hHfix : H ≤ fixedSpace f.range := by
      intro v hv y hy
      obtain ⟨b,rfl⟩ := hy
      have hh : f b • v-v ∈ W :=
        (le_iSup (fun b : B => H.map (symplecticNatural 2 (f b)-LinearMap.id)) b) ⟨v,hv,rfl⟩
      rw [hzero] at hh
      exact sub_eq_zero.mp hh
    have htotal : displacementSpace f.range ≤ R := by
      intro v hv
      rw [←(form F).orthogonal_orthogonal form_nondegenerate form_alternating.isRefl R]
      intro w hw
      exact form_alternating.eq_iff.mp ((orthogonal_displacementSpace f.range ▸ hHfix hw) v hv)
    apply hbad
    apply commutator_le.mpr
    intro b hb u hu
    obtain ⟨v,rfl⟩ := hu
    have hv : f ⟨b,hb⟩ • v.toAdd-v.toAdd ∈ displacementSpace f.range :=
      Coinvariants.sub_mem_ker (ρ := (symplecticNatural 2).comp f.range.subtype)
        ⟨f ⟨b,hb⟩,⟨_,rfl⟩⟩ v.toAdd
    have hh := hline _ (htotal hv)
    rw [hdisp] at hh
    exact hh
  have heq : W = R := by
    apply Submodule.eq_of_le_of_finrank_le hWR
    rw [hd]
    have hh : Module.finrank F W ≠ 0 := fun h => hWne (Submodule.finrank_eq_zero.mp h)
    omega
  apply le_antisymm
  · apply commutator_le.mpr
    intro b hb a ha
    obtain ⟨v,hv⟩ := hAr ha
    have hvH : v.toAdd ∈ H := (hA v.toAdd).mp (hv ▸ ha)
    refine ⟨Multiplicative.ofAdd (f ⟨b,hb⟩ • v.toAdd-v.toAdd),?_,?_⟩
    · exact hWR ((le_iSup (fun b : B => H.map (symplecticNatural 2 (f b)-LinearMap.id))
        ⟨b,hb⟩) ⟨v.toAdd,hvH,rfl⟩)
    · rw [hdisp]
      exact congrArg (fun a => ⁅b,a⁆) hv
  · rintro _ ⟨v,hv,rfl⟩
    exact hW v.toAdd (heq.symm ▸ hv)

/-- A hyperplane commutator contained in a marked line is either trivial or
that whole line, including all field multiples. -/
theorem embedded_hyperplane_commutator_dichotomy
    (B A : Subgroup G)
    (j : Multiplicative (Vector F) →* G) (hj : Function.Injective j)
    (hAr : A ≤ j.range) (f : B →* Sp F)
    (hact : ∀ (b : B) v,
      j (Multiplicative.ofAdd (f b • v)) = b.val*j (Multiplicative.ofAdd v)*b.val⁻¹)
    (R : Submodule F (Vector F)) (hd : Module.finrank F R = 1)
    (hA : ∀ v, j (Multiplicative.ofAdd v) ∈ A ↔ v ∈ (form F).orthogonal R)
    (hle : ⁅B,A⁆ ≤ (AddSubgroup.toSubgroup' R.toAddSubgroup).map j) :
    ⁅B,A⁆ = ⊥ ∨ ⁅B,A⁆ = (AddSubgroup.toSubgroup' R.toAddSubgroup).map j := by
  let H := (form F).orthogonal R
  let W := ⨆ b : B, H.map (symplecticNatural 2 (f b)-LinearMap.id)
  have hdisp (b : B) v :
      j (Multiplicative.ofAdd (f b • v-v)) = ⁅b.val,j (Multiplicative.ofAdd v)⁆ := by
    rw [ofAdd_sub,map_div,div_eq_mul_inv,hact,commutatorElement_def]
  have hW : ∀ v ∈ W, j (Multiplicative.ofAdd v) ∈ ⁅B,A⁆ := by
    intro v hv
    refine Submodule.iSup_induction _ (motive := fun v => j (Multiplicative.ofAdd v) ∈ ⁅B,A⁆) hv ?_ ?_ ?_
    · intro b w hw
      obtain ⟨v,hv,rfl⟩ := hw
      change j (Multiplicative.ofAdd (f b • v-v)) ∈ _
      rw [hdisp]
      exact commutator_mem_commutator b.property ((hA v).mpr hv)
    · simp
    · intro v w hv hw
      simpa only [ofAdd_add,map_mul] using (⁅B,A⁆).mul_mem hv hw
  have hWR : W ≤ R := by
    intro v hv
    obtain ⟨w,hw,he⟩ := hle (hW v hv)
    have he' : w.toAdd = v := congrArg Multiplicative.toAdd (hj he)
    exact he' ▸ hw
  by_cases hz : W = ⊥
  · left
    apply le_bot_iff.mp
    apply commutator_le.mpr
    intro b hb a ha
    obtain ⟨v,hv⟩ := hAr ha
    have hvH : v.toAdd ∈ H := (hA v.toAdd).mp (hv ▸ ha)
    have hw : f ⟨b,hb⟩ • v.toAdd-v.toAdd ∈ W :=
      (le_iSup (fun b : B => H.map (symplecticNatural 2 (f b)-LinearMap.id))
        ⟨b,hb⟩) ⟨v.toAdd,hvH,rfl⟩
    have hw0 : f ⟨b,hb⟩ • v.toAdd-v.toAdd = 0 := by simpa only [hz,Submodule.mem_bot] using hw
    have h1 := hdisp ⟨b,hb⟩ v.toAdd
    rw [hw0] at h1
    simpa only [ofAdd_zero,map_one,ofAdd_toAdd,hv,mem_bot] using h1.symm
  · right
    have heq : W = R := by
      apply Submodule.eq_of_le_of_finrank_le hWR
      rw [hd]
      have hh : Module.finrank F W ≠ 0 := fun h => hz (Submodule.finrank_eq_zero.mp h)
      omega
    apply le_antisymm hle
    rintro _ ⟨v,hv,rfl⟩
    exact hW v.toAdd (heq.symm ▸ hv)

end Theory.SpecificGroups.SymplecticFour.RootHyperplaneComparison
