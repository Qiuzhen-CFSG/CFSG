module
public import Theory.SpecificGroups.SymmetricFourWreath.Core.Geometry
public import Theory.SpecificGroups.SymmetricFourWreath.LocalStructure.Center
public import Theory.Frattini.OmegaProducts
public import Stellmacher.ElementaryAbelianMaxProduct
public import Stellmacher.ElementaryAbelianMaxGlobal
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms
public import Theory.GroupTheory.CharacteristicCentralizerFusion
/-!
# Intrinsic geometry of the dihedral wreath Sylow with a central factor

For the wreath product of D8 by C2 times an elementary central factor, the
Frattini-center intersection is the center of any normal extraspecial
subgroup of order32. The quotient by this line has a unique largest
elementary subgroup; it is the image of that extraspecial subgroup together
with the central factor. Its inverse image is therefore characteristic.
The original extraspecial subgroup need not be marked by the isomorphism.

Source: Aschbacher–Smith 2.4.29, printed pp.544–545, using the same
wreath geometry as 13.9.6, printed p.971.
-/
public section
namespace SymmetricFourWreath
open Subgroup

theorem isPGroup_P : IsPGroup 2 P := IsPGroup.of_card (n:=7) card_P

theorem frattini_inf_center_P : frattini P ⊓ center P = centralLine := by
  rw [center_P]
  apply inf_eq_right.mpr
  let : IsExtraspecial 2 coreInP := coreInP_extraspecial
  let : Fact (IsPGroup 2 P) := ⟨isPGroup_P⟩
  let : Fact (IsPGroup 2 coreInP) := ⟨IsExtraspecial.isPGroup 2 coreInP⟩
  have h := frattini_map_le_of_isPGroup (p:=2) coreInP.subtype
  rw [IsExtraspecial.frattini_eq_center (p:=2), center_coreInP] at h
  exact h

variable {D : Type*} [Group D] [Finite D] [IsElementaryAbelian 2 D]

theorem frattini_inf_center_prod :
    frattini (P × D) ⊓ center (P × D) = centralLine.prod ⊥ := by
  let : Fact (IsPGroup 2 D) := ⟨IsElementaryAbelian.isPGroup 2 D⟩
  rw [frattini_prod isPGroup_P (IsElementaryAbelian.isPGroup 2 D),
    frattini_eq_bot_of_isElementaryAbelian (R:=D) (p:=2), Subgroup.center_prod]
  ext x
  change (x.1 ∈ frattini P ∧ x.2 ∈ (⊥ : Subgroup D)) ∧
    x.1 ∈ center P ∧ x.2 ∈ center D ↔ x.1 ∈ centralLine ∧ x.2 ∈ (⊥ : Subgroup D)
  rw [←frattini_inf_center_P]
  simp only [mem_inf, mem_bot]
  constructor
  · rintro ⟨⟨hp,hd⟩,hz,_⟩; exact ⟨⟨hp,hz⟩,hd⟩
  · rintro ⟨⟨hp,hz⟩,hd⟩; exact ⟨⟨hp,hd⟩,hz,hd ▸ (center D).one_mem⟩

theorem maximum_elementary_centralQuotient_prod (E : Subgroup (CentralQuotient × D)) :
    E ∈ Stellmacher.elementaryAbelianMaxSubgroups ⊤ ↔ E = quotientCore.prod ⊤ := by
  let : IsElementaryAbelian 2 (⊤ : Subgroup D) := IsElementaryAbelian.of_surjective (Subgroup.topEquiv.symm : D ≃* (⊤ : Subgroup D)).toMonoidHom Subgroup.topEquiv.symm.surjective
  rw [← top_prod_top, Stellmacher.maxFamily_prod_iff]
  constructor
  · rintro ⟨A,hA,B,hB,rfl⟩
    have hAeq := (maximum_elementary_centralQuotient A).mp hA
    have hBeq : B = ⊤ := by
      apply eq_of_le_of_card_ge le_top
      exact hB.2.2 ⊤ le_rfl inferInstance
    rw [hAeq,hBeq]
  · rintro rfl
    exact ⟨quotientCore,(maximum_elementary_centralQuotient _).mpr rfl,
      ⊤,⟨le_rfl,inferInstance,fun A _ _=>card_le_of_le le_top⟩,rfl⟩

theorem thompson_centralQuotient_prod :
    Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup (CentralQuotient × D)) =
      quotientCore.prod ⊤ := by
  apply le_antisymm
  · apply sSup_le
    intro E hE
    rw [(maximum_elementary_centralQuotient_prod E).mp hE]
  · exact le_sSup ((maximum_elementary_centralQuotient_prod _).mpr rfl)

/-- A normal extraspecial subgroup has the intrinsic Frattini-center line. -/
theorem center_eq_frattini_inf_center_of_equiv_prod
    {S : Type*} [Group S] [Finite S] (e : S ≃* P × D)
    (Q : Subgroup S) [Q.Normal] [IsExtraspecial 2 Q] :
    (center Q).map Q.subtype = frattini S ⊓ center S := by
  have htwo : IsPGroup 2 S := (isPGroup_prod isPGroup_P
    (IsElementaryAbelian.isPGroup 2 D)).of_injective e.toMonoidHom e.injective
  let : Fact (IsPGroup 2 S) := ⟨htwo⟩
  let : Fact (IsPGroup 2 Q) := ⟨htwo.to_subgroup Q⟩
  have hcard : Nat.card ((center Q).map Q.subtype) = 2 := by
    rw [card_map_of_injective Q.subtype_injective,IsExtraspecial.center_order_p 2 Q]
  have hcenter : (center Q).map Q.subtype ≤ center S := central_of_normal_card_two _ hcard
  have hphi : (center Q).map Q.subtype ≤ frattini S := by
    rw [←IsExtraspecial.frattini_eq_center (p:=2)]
    exact frattini_map_le_of_isPGroup (p:=2) Q.subtype
  apply eq_of_le_of_card_ge (le_inf hphi hcenter)
  rw [hcard,← card_map_of_injective (f:=e.toMonoidHom) e.injective,
    Subgroup.map_inf _ _ e.toMonoidHom e.injective,frattini_map_equiv e,center_map_equiv e,
    frattini_inf_center_prod]
  rw [Nat.card_congr (centralLine.prodEquiv (⊥ : Subgroup D)).toEquiv,
    Nat.card_prod,card_centralLine]
  simp

/-- The marked central quotient recovers the original extraspecial subgroup,
up to the elementary direct factor, as the elementary Thompson subgroup. -/
theorem thompson_image_of_equiv_prod
    {S : Type*} [Group S] [Finite S] (e : S ≃* P × D)
    (Q : Subgroup S) [Q.Normal] [IsExtraspecial 2 Q] (hQ : Nat.card Q = 32) :
    let f := ((centralProjection.comp (MonoidHom.fst P D)).prod
      (MonoidHom.snd P D)).comp e.toMonoidHom
    Function.Surjective f ∧ f.ker = (center Q).map Q.subtype ∧
    Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup (CentralQuotient × D)) =
      (Q ⊔ ((MonoidHom.fst P D).comp e.toMonoidHom).ker).map f := by
  dsimp only
  let a := (MonoidHom.fst P D).comp e.toMonoidHom
  let b := (MonoidHom.snd P D).comp e.toMonoidHom
  let g := centralProjection.comp a
  let f := g.prod b
  let Z := (center Q).map Q.subtype
  have hZ : Z = frattini S ⊓ center S :=
    center_eq_frattini_inf_center_of_equiv_prod e Q
  have heZ : Z.map e.toMonoidHom = centralLine.prod (⊥ : Subgroup D) := by
    rw [hZ,Subgroup.map_inf _ _ _ e.injective,frattini_map_equiv e,
      center_map_equiv e,frattini_inf_center_prod]
  have hZm (x : S) : x ∈ Z ↔ (e x).1 ∈ centralLine ∧ (e x).2 = 1 := by
    rw [←mem_map_iff_mem (f:=e.toMonoidHom) e.injective,heZ]
    rfl
  have hf : Function.Surjective f := by
    rintro ⟨c,d⟩
    obtain ⟨w,hw⟩ := QuotientGroup.mk'_surjective centralLine c
    refine ⟨e.symm (w,d),?_⟩
    change (centralProjection (e (e.symm (w,d))).1,(e (e.symm (w,d))).2)=(c,d)
    rw [e.apply_symm_apply]
    exact Prod.ext hw rfl
  have hk : f.ker = Z := by
    ext x
    change (centralProjection (e x).1,(e x).2)=1 ↔ x∈Z
    rw [hZm,Prod.mk_eq_one]
    exact (QuotientGroup.eq_one_iff (e x).1).and Iff.rfl
  have hgk : (g.comp Q.subtype).ker = center Q := by
    ext x
    change centralProjection (e (x : S)).1 = 1 ↔ x∈center Q
    change (((e (x:S)).1 : P ⧸ centralLine)=1) ↔ x∈center Q
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro hx
      have hc : e (x:S) ∈ center (P × D) := by
        rw [Subgroup.center_prod,center_P,center_eq_top (G:=D)]
        exact ⟨hx,mem_top _⟩
      have hcS : (x:S) ∈ center S := by
        rw [←center_map_equiv e] at hc
        exact (mem_map_iff_mem (f:=e.toMonoidHom) e.injective).mp hc
      exact mem_center_iff.mpr fun y=>Subtype.ext (mem_center_iff.mp hcS y)
    · intro hx
      exact ((hZm x).mp (mem_map_of_mem Q.subtype hx)).1
  let eqg := (QuotientGroup.quotientMulEquivOfEq hgk.symm).trans
    (QuotientGroup.quotientKerEquivRange (g.comp Q.subtype))
  have hr : (g.comp Q.subtype).range = Q.map g := by
    rw [MonoidHom.range_comp,range_subtype]
  let eqE := eqg.trans (MulEquiv.subgroupCongr hr)
  let : IsElementaryAbelian 2 (Q ⧸ center Q) :=
    IsExtraspecial.quotient_elementary_abelian 2 Q
  have hE : IsElementaryAbelian 2 (Q.map g) :=
    IsElementaryAbelian.of_surjective eqE.toMonoidHom eqE.surjective
  have hcardE : Nat.card (Q.map g) = 16 := by
    have hh := (center Q).card_mul_index
    rw [IsExtraspecial.center_order_p 2 Q,index_eq_card,hQ,
      Nat.card_congr eqE.toEquiv] at hh
    omega
  have hEeq : Q.map g = quotientCore := by
    apply (maximum_elementary_centralQuotient _).mp
    refine ⟨le_top,hE,fun E _ hE=>?_⟩
    rw [hcardE,←card_quotientCore]
    exact ((maximum_elementary_centralQuotient quotientCore).mpr rfl).2.2 E le_top hE
  have hm : (Q ⊔ a.ker).map f = quotientCore.prod ⊤ := by
    apply le_antisymm
    · apply map_le_iff_le_comap.mpr
      apply sup_le
      · intro x hx
        refine ⟨?_,mem_top _⟩
        change g x ∈ quotientCore
        rw [←hEeq]
        exact mem_map_of_mem g hx
      · intro x hx
        refine ⟨?_,mem_top _⟩
        change centralProjection (a x) ∈ quotientCore
        rw [show a x=1 from hx,map_one]
        exact quotientCore.one_mem
    · rintro ⟨c,d⟩ ⟨hc,_⟩
      rw [←hEeq] at hc
      obtain ⟨x,hx,hxc⟩ := hc
      let y := e.symm (1,(b x)⁻¹*d)
      have hy : y ∈ a.ker := by
        change (e (e.symm (1,(b x)⁻¹*d))).1=1
        rw [e.apply_symm_apply]
      refine ⟨x*y,(Q⊔a.ker).mul_mem (mem_sup_left hx) (mem_sup_right hy),?_⟩
      rw [map_mul]
      change (g x,b x)*(centralProjection (e y).1,(e y).2)=(c,d)
      dsimp only [y]
      rw [e.apply_symm_apply,map_one]
      apply Prod.ext
      · simpa only [Prod.fst_mul,mul_one] using hxc
      · simp only [Prod.snd_mul,mul_inv_cancel_left]
  exact ⟨hf,hk,(thompson_centralQuotient_prod (D:=D)).trans hm.symm⟩


/-- The actual quotient by the extraspecial center has elementary Thompson
subgroup equal to the image of the extraspecial subgroup and central factor. -/
theorem thompson_quotient_of_equiv_prod
    {S : Type*} [Group S] [Finite S] (e : S ≃* P × D)
    (Q : Subgroup S) [Q.Normal] [IsExtraspecial 2 Q] (hQ : Nat.card Q = 32) :
    Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup (S ⧸ (center Q).map Q.subtype)) =
      (Q ⊔ ((MonoidHom.fst P D).comp e.toMonoidHom).ker).map
        (QuotientGroup.mk' ((center Q).map Q.subtype)) := by
  let f := ((centralProjection.comp (MonoidHom.fst P D)).prod
    (MonoidHom.snd P D)).comp e.toMonoidHom
  obtain ⟨hf,hk,hJ⟩ := thompson_image_of_equiv_prod e Q hQ
  let eq := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)
  apply map_injective (f:=eq.toMonoidHom) eq.injective
  rw [←Stellmacher.elementaryAbelianMaxJ_map_injective eq.toMonoidHom eq.injective,
    map_top_of_surjective eq.toMonoidHom eq.surjective,map_map,hJ]
  rfl

/-- The source extraspecial core together with the elementary direct factor
is characteristic in the whole Sylow subgroup. -/
theorem core_sup_factor_characteristic_of_equiv_prod
    {S : Type*} [Group S] [Finite S] (e : S ≃* P × D)
    (Q : Subgroup S) [Q.Normal] [IsExtraspecial 2 Q] (hQ : Nat.card Q = 32) :
    (Q ⊔ ((MonoidHom.fst P D).comp e.toMonoidHom).ker).Characteristic := by
  let Z := (center Q).map Q.subtype
  let : Z.Characteristic := by
    rw [show Z = frattini S ⊓ center S from center_eq_frattini_inf_center_of_equiv_prod e Q]
    apply characteristic_iff_le_comap.mpr
    intro a x hx
    exact ⟨characteristic_iff_le_comap.mp inferInstance a hx.1,
      characteristic_iff_le_comap.mp inferInstance a hx.2⟩
  let R := Q ⊔ ((MonoidHom.fst P D).comp e.toMonoidHom).ker
  let J := Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup (S ⧸ Z))
  let : J.Characteristic := Stellmacher.elementaryAbelianMaxJ_top_characteristic
  have hr : J.comap (QuotientGroup.mk' Z) = R := by
    rw [show J = R.map (QuotientGroup.mk' Z) from thompson_quotient_of_equiv_prod e Q hQ,
      comap_map_eq,QuotientGroup.ker_mk']
    exact sup_eq_left.mpr ((map_subtype_le (center Q)).trans le_sup_left)
  change R.Characteristic
  rw [←hr]
  apply characteristic_iff_le_comap.mpr
  intro a x hx
  have h := characteristic_iff_le_comap.mp (inferInstance : J.Characteristic)
    (quotientAut Z a) hx
  change quotientAut Z a ((QuotientGroup.mk' Z) x) ∈ J at h
  rw [quotientAut_apply_mk] at h
  exact h

end SymmetricFourWreath
