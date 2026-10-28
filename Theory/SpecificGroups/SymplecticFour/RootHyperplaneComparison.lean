module
public import Theory.SpecificGroups.SymplecticFour.RootHyperplane
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.TransvectionProducts
public import Theory.ElementaryAbelian.Basic

/-!
# The quadratic hyperplane comparison at a symplectic root

If a symplectic actor fixes a root line and acts quadratically on its
perpendicular hyperplane, failure of the source displacement comparison
forces hyperplane displacement into that line. The joined fixed displacement
is isotropic; dimension two would force the excluded comparison by
orthogonality, so it has dimension one.

The embedded version retains the actual conjugation map and yields a literal
commutator bound, with equality for an injective embedding: a trivial
hyperplane displacement would force normalization. An elementary subgroup of
transvections supplies its common root line; all field displacements lift into
the original group commutator.
These are the model calculations of MS93 (3.3)(ii), p.867, used in (5.7), p.919.
-/

public noncomputable section
open Subgroup Representation
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.TwoLocalCover

namespace Theory.SpecificGroups.SymplecticFour.RootHyperplaneComparison
variable {F : Type*} [Field F]

private noncomputable def hyperplaneDisplacement (Y : Subgroup (Sp F))
    (A : Submodule F (Vector F)) : Submodule F (Vector F) :=
  ⨆ y : Y, A.map (symplecticNatural 2 y.val - LinearMap.id)

private theorem hyperplaneDisplacement_le (Y : Subgroup (Sp F)) (A : Submodule F (Vector F)) :
    hyperplaneDisplacement Y A ≤ displacementSpace Y := by
  apply iSup_le
  intro y v hv
  obtain ⟨w,hw,rfl⟩ := hv
  exact Coinvariants.sub_mem_ker (ρ := (symplecticNatural 2).comp Y.subtype) y w

private theorem hyperplane_displacement_le_root
    (Y : Subgroup (Sp F)) (R : Submodule F (Vector F))
    (hd : Module.finrank F R = 1)
    (hfix : ∀ y ∈ Y, ∀ v ∈ R, y • v = v)
    (hq : ∀ x ∈ Y, ∀ y ∈ Y, ∀ v ∈ (form F).orthogonal R,
      x • (y • v-v)=y • v-v)
    (hbad : ¬ displacementSpace Y ≤ R ⊔ hyperplaneDisplacement Y ((form F).orthogonal R)) :
    hyperplaneDisplacement Y ((form F).orthogonal R) ≤ R := by
  let A := (form F).orthogonal R
  let W := hyperplaneDisplacement Y A
  let B := R ⊔ W
  have hWP : W ≤ displacementSpace Y := hyperplaneDisplacement_le Y A
  have hRf : R ≤ fixedSpace Y := fun v hv y hy => hfix y hy v hv
  have hWf : W ≤ fixedSpace Y := by
    apply iSup_le
    intro y w hw
    obtain ⟨v,hv,rfl⟩ := hw
    exact fun x hx => hq x hx y.val y.property v hv
  have hBf : B ≤ fixedSpace Y := sup_le hRf hWf
  have hiso : ∀ v ∈ B, ∀ w ∈ B, form F v w = 0 := by
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
    intro v hv w hw
    obtain ⟨r,hr,s,hs,rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨t,ht,u,hu,rfl⟩ := Submodule.mem_sup.mp hw
    simp only [map_add,LinearMap.add_apply,hRR ht r hr,form_alternating.eq_iff.mp (hRW hr u hu),
      hRW ht s hs,hWW hu s hs,add_zero]
  have hBdim := finrank_le_two_of_isotropic B hiso
  have hless : Module.finrank F B < 2 := by
    by_contra! h
    have he : Module.finrank F B = 2 := by omega
    have hBo : (form F).orthogonal B = B := by
      symm
      apply Submodule.eq_of_le_of_finrank_eq
      · exact fun v hv w hw => hiso w hw v hv
      · rw [LinearMap.BilinForm.finrank_orthogonal form_nondegenerate,he]
        simp [Theory.SpecificGroups.SymplecticFour.Vector]
    apply hbad
    intro v hv
    change v ∈ B
    rw [←hBo]
    intro w hw
    exact form_alternating.eq_iff.mp ((orthogonal_displacementSpace Y ▸ hBf hw) v hv)
  have hle : Module.finrank F B ≤ Module.finrank F R := by omega
  have heq : R = B := Submodule.eq_of_le_of_finrank_le le_sup_left hle
  exact (le_sup_right : W ≤ B).trans heq.ge
end Theory.SpecificGroups.SymplecticFour.RootHyperplaneComparison

namespace Theory.SpecificGroups.SymplecticFour.RootHyperplaneComparison
open InvolutionTypes InvolutionCentralizers TransvectionRecognition
open scoped IsMulCommutative
variable {F : Type*} [Field F] [CharP F 2]

theorem elementary_transvection_common_line (A : Subgroup (Sp F))
    [IsElementaryAbelian 2 A] (hne : A ≠ ⊥)
    (hrank : ∀ x ∈ A, Module.finrank F (movedSpace x) ≤ 1) :
    ∃ x ∈ A, displacementSpace A = movedSpace x ∧
      Module.finrank F (displacementSpace A) = 1 := by
  obtain h | ⟨x,hx,hxne⟩ := A.bot_or_exists_ne_one
  · exact (hne h).elim
  have htype (y : Sp F) (hy : y ∈ A) (hyne : y ≠ 1) : IsB1 y := by
    refine ⟨orderOf_eq_prime_iff.mpr ⟨elemPow_eq_one_of_isElementaryAbelian y hy,hyne⟩,?_⟩
    have hp : Module.finrank F (movedSpace y) ≠ 0 :=
      fun h => movedSpace_ne_bot y hyne (Submodule.finrank_eq_zero.mp h)
    have hb := hrank y hy
    omega
  have hxt := htype x hx hxne
  have hsame (y : Sp F) (hy : y ∈ A) (hyne : y ≠ 1) : movedSpace y = movedSpace x := by
    by_contra h
    have hcomm : Commute y x := (show Commute (⟨y,hy⟩ : A) ⟨x,hx⟩ from mul_comm _ _).map A.subtype
    have hh := isC2_product_of_commute_distinct_movedSpace y x (htype y hy hyne) hxt hcomm h
    have hh' := hrank (y*x) (A.mul_mem hy hx)
    have hh'' := hh.2.1
    omega
  have heq : displacementSpace A = movedSpace x := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨y,v⟩,rfl⟩
      by_cases hy : y.val = 1
      · change y.val • v-v ∈ movedSpace x
        rw [hy,one_smul,sub_self]
        exact Submodule.zero_mem _
      · rw [←hsame y.val y.property hy]
        exact ⟨v,rfl⟩
    · rintro v ⟨w,rfl⟩
      exact Coinvariants.sub_mem_ker (ρ := (symplecticNatural 2).comp A.subtype) ⟨x,hx⟩ w
  exact ⟨x,hx,heq,heq.symm ▸ hxt.2⟩
end Theory.SpecificGroups.SymplecticFour.RootHyperplaneComparison

namespace Theory.SpecificGroups.SymplecticFour.RootHyperplaneComparison
open scoped commutatorElement
variable {F G : Type*} [Field F] [Group G]

theorem embedded_hyperplane_commutator_le_root
    (B A : Subgroup G)
    (j : Multiplicative (Theory.SpecificGroups.SymplecticFour.Vector F) →* G)
    (hAr : A ≤ j.range)
    (f : B →* Sp F)
    (hact : ∀ (b : B) v,
      j (Multiplicative.ofAdd (f b • v)) = b.val * j (Multiplicative.ofAdd v) * b.val⁻¹)
    (R : Submodule F (Theory.SpecificGroups.SymplecticFour.Vector F))
    (hd : Module.finrank F R = 1)
    (hfix : ∀ b : B, ∀ v ∈ R, f b • v=v)
    (hquad : ∀ x y : B, ∀ v ∈ (form F).orthogonal R,
      f x • (f y • v-v)=f y • v-v)
    (hA : ∀ v, j (Multiplicative.ofAdd v) ∈ A ↔ v ∈ (form F).orthogonal R)
    (hline : ∀ v ∈ R, j (Multiplicative.ofAdd v) ∈ B)
    (hn : A ≤ normalizer (B : Set G)) (hbad : ¬ j.range ≤ normalizer (B : Set G)) :
    ⁅B,A⁆ ≤ (AddSubgroup.toSubgroup' R.toAddSubgroup).map j := by
  let H := (form F).orthogonal R
  have hdisp (b : B) (v : Theory.SpecificGroups.SymplecticFour.Vector F) :
      j (Multiplicative.ofAdd (f b • v-v)) = ⁅b.val,j (Multiplicative.ofAdd v)⁆ := by
    rw [ofAdd_sub,map_div,div_eq_mul_inv,hact,commutatorElement_def]
  have hW : ∀ v ∈ hyperplaneDisplacement f.range H,
      j (Multiplicative.ofAdd v) ∈ B := by
    intro v hv
    refine Submodule.iSup_induction _ (motive := fun v => j (Multiplicative.ofAdd v) ∈ B) hv ?_ ?_ ?_
    · intro y w hw
      obtain ⟨b,hb⟩ := y.property
      obtain ⟨v,hv,rfl⟩ := hw
      change j (Multiplicative.ofAdd (y.val • v-v)) ∈ B
      rw [←hb,hdisp]
      exact le_normalizer_iff_commutator_le_left.mp hn
        (commutator_mem_commutator b.property ((hA v).mpr hv))
    · simp
    · intro v w hv hw
      simpa only [ofAdd_add,map_mul] using B.mul_mem hv hw
  have hnot : ¬ displacementSpace f.range ≤ R ⊔ hyperplaneDisplacement f.range H := by
    intro hle
    apply hbad
    apply le_normalizer_iff_commutator_le_left.mpr
    apply commutator_le.mpr
    intro b hb u hu
    obtain ⟨v,rfl⟩ := hu
    have hv : f ⟨b,hb⟩ • v.toAdd-v.toAdd ∈ displacementSpace f.range :=
      Coinvariants.sub_mem_ker (ρ := (symplecticNatural 2).comp f.range.subtype)
        ⟨f ⟨b,hb⟩,⟨⟨b,hb⟩,rfl⟩⟩ v.toAdd
    obtain ⟨r,hr,w,hw,he⟩ := Submodule.mem_sup.mp (hle hv)
    have hh := B.mul_mem (hline r hr) (hW w hw)
    rw [←map_mul,←ofAdd_add,he,hdisp] at hh
    exact hh
  have hm := hyperplane_displacement_le_root f.range R hd
    (by rintro y ⟨y,rfl⟩ v hv; exact hfix y v hv)
    (by rintro x ⟨x,rfl⟩ y ⟨y,rfl⟩ v hv; exact hquad x y v hv) hnot
  apply commutator_le.mpr
  intro b hb a ha
  obtain ⟨v,hv⟩ := hAr ha
  have hvA : v.toAdd ∈ (form F).orthogonal R := (hA v.toAdd).mp (hv ▸ ha)
  have hw : f ⟨b,hb⟩ • v.toAdd-v.toAdd ∈ R := by
    apply hm
    exact (le_iSup (fun y : f.range => H.map (symplecticNatural 2 y.val-LinearMap.id))
      ⟨f ⟨b,hb⟩,⟨⟨b,hb⟩,rfl⟩⟩) ⟨v.toAdd,hvA,rfl⟩
  refine ⟨Multiplicative.ofAdd (f ⟨b,hb⟩ • v.toAdd-v.toAdd),hw,?_⟩
  rw [hdisp]
  exact congrArg (fun a => ⁅b,a⁆) hv
end Theory.SpecificGroups.SymplecticFour.RootHyperplaneComparison

namespace Theory.SpecificGroups.SymplecticFour.RootHyperplaneComparison
open scoped commutatorElement
variable {F G : Type*} [Field F] [Group G]

/-- The entire field displacement is present in the literal group commutator. -/
theorem displacement_lifts_to_commutator
    (B N : Subgroup G)
    (j : Multiplicative (Theory.SpecificGroups.SymplecticFour.Vector F) →* G) (hjr : j.range = N)
    (f : B →* Sp F)
    (hact : ∀ (b : B) v,
      j (Multiplicative.ofAdd (f b • v)) = b.val * j (Multiplicative.ofAdd v) * b.val⁻¹) :
    ∀ v ∈ displacementSpace f.range, j (Multiplicative.ofAdd v) ∈ ⁅B,N⁆ := by
  have hP : displacementSpace f.range =
      ⨆ b : B, LinearMap.range (symplecticNatural 2 (f b)-LinearMap.id) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨y,v⟩,rfl⟩
      obtain ⟨b,hb⟩ := y.property
      change y.val • v-v ∈ _
      rw [←hb]
      exact (le_iSup (fun b : B => LinearMap.range (symplecticNatural 2 (f b)-LinearMap.id)) b)
        ⟨v,rfl⟩
    · apply iSup_le
      intro b v hv
      obtain ⟨w,rfl⟩ := hv
      exact Coinvariants.sub_mem_ker (ρ := (symplecticNatural 2).comp f.range.subtype)
        ⟨f b,⟨b,rfl⟩⟩ w
  intro v hv
  rw [hP] at hv
  refine Submodule.iSup_induction _ (motive := fun v => j (Multiplicative.ofAdd v) ∈ ⁅B,N⁆) hv ?_ ?_ ?_
  · intro b v hv
    obtain ⟨w,rfl⟩ := hv
    change j (Multiplicative.ofAdd (f b • w-w)) ∈ _
    rw [ofAdd_sub,map_div,div_eq_mul_inv,hact]
    exact commutator_mem_commutator b.property (hjr ▸ (show j (Multiplicative.ofAdd w) ∈ j.range from ⟨_,rfl⟩))
  · simp
  · intro v w hv hw
    simpa only [ofAdd_add,map_mul] using (⁅B,N⁆).mul_mem hv hw
end Theory.SpecificGroups.SymplecticFour.RootHyperplaneComparison

namespace Theory.SpecificGroups.SymplecticFour.RootHyperplaneComparison
open scoped commutatorElement
variable {F G : Type*} [Field F] [Group G]

/-- The group commutator is exactly the image of the field displacement space. -/
theorem commutator_eq_displacement_image
    (B N : Subgroup G)
    (j : Multiplicative (Vector F) →* G) (hjr : j.range = N)
    (f : B →* Sp F)
    (hact : ∀ (b : B) v,
      j (Multiplicative.ofAdd (f b • v)) = b.val*j (Multiplicative.ofAdd v)*b.val⁻¹) :
    ⁅B,N⁆ = (AddSubgroup.toSubgroup' (displacementSpace f.range).toAddSubgroup).map j := by
  apply le_antisymm
  · apply commutator_le.mpr
    intro x hx u hu
    obtain ⟨v,rfl⟩ := hjr.symm ▸ hu
    refine ⟨Multiplicative.ofAdd (f ⟨x,hx⟩ • v.toAdd-v.toAdd),?_,?_⟩
    · exact Coinvariants.sub_mem_ker
        (ρ := (symplecticNatural 2).comp f.range.subtype) ⟨f ⟨x,hx⟩,⟨_,rfl⟩⟩ v.toAdd
    · rw [ofAdd_sub,map_div,div_eq_mul_inv,hact,commutatorElement_def]
      rfl
  · rintro _ ⟨v,hv,rfl⟩
    exact displacement_lifts_to_commutator B N j hjr f hact v.toAdd hv
end Theory.SpecificGroups.SymplecticFour.RootHyperplaneComparison

namespace Theory.SpecificGroups.SymplecticFour.RootHyperplaneComparison
open scoped commutatorElement
variable {F G : Type*} [Field F] [Group G]

/-- Failure of normalization makes the hyperplane commutator the entire root. -/
theorem embedded_hyperplane_commutator_eq_root
    (B A : Subgroup G)
    (j : Multiplicative (Vector F) →* G) (hj : Function.Injective j)
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
    (hline : ∀ v ∈ R, j (Multiplicative.ofAdd v) ∈ B)
    (hn : A ≤ normalizer (B : Set G)) (hbad : ¬ j.range ≤ normalizer (B : Set G)) :
    ⁅B,A⁆ = (AddSubgroup.toSubgroup' R.toAddSubgroup).map j := by
  have hle := embedded_hyperplane_commutator_le_root B A j hAr f hact R hd hfix hquad
    hA hline hn hbad
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
    apply le_normalizer_iff_commutator_le_left.mpr
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
  apply le_antisymm hle
  rintro _ ⟨v,hv,rfl⟩
  exact hW v.toAdd (heq.symm ▸ hv)
end Theory.SpecificGroups.SymplecticFour.RootHyperplaneComparison
