module
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.MathieuTwentyTwoRadicals
public import Theory.Mathieu.M22.Properties.InvolutionFixedOrders
public import Theory.Mathieu.M22.Properties.TwoRank

/-!
# Elementary radicals with an irreducible large binary displacement in J₄

A perfect actor with a nonsolvable simple section divisible by nine has
no commuting involution in Aut(M₂₂): its inner image would lie in an
involutory fixed subgroup, whose order is not divisible by nine.
An irreducible elementary subgroup of order greater than 128 vanishes in
either involution-centralizer action on M₂₂, by the two-rank bound five.
Its central displacement puts the radical image in the actor centralizer.

A nontrivial radical Frattini subgroup supplies a common fixed central
involution. In the first native centralizer, the resulting large abelian
subgroup contradicts the extraspecial bound 128. In the second, the entire
radical lies in its actual elementary kernel. Thus the radical is elementary.
The original chosen-module consumer uses its full PSL₃(4) two-core quotient;
no surjection onto M₂₂ is assumed.
Source: Aschbacher--Smith 4.2.13 and 4.4.3, printed pp.611--612,623,
as used in 8.2.7, p.718. Imported native certificates retain their attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Sporadic.Mathieu
open scoped IsMulCommutative
namespace Janko4.InvolutionCentralizers
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private theorem nine_actor_two_centralizer
    (B U : Subgroup (MulAut M22)) [Group.IsPerfect B]
    (h9 : 9 ∣ Nat.card B) (hU : IsPGroup 2 U)
    (hUB : U ≤ centralizer (B : Set (MulAut M22))) : U = ⊥ := by
  have hB : B ≤ MulAut.innerSubgroup M22 := by
    let : Group.IsNilpotent (MulAut.Outer M22) :=
      (IsPGroup.of_card_dvd_pow (p := 2) (n := 1)
        (by simpa only [pow_one] using
          M22TripleCover.ScalarAutomorphisms.m22_outer_card_dvd_two)).isNilpotent
    exact (le_solvableResidual_of_isPerfect B).trans
      (solvableResidual_le_of_solvable_quotient _)
  by_contra hn
  have hd : 2 ∣ Nat.card U := hU.card_eq_or_dvd.resolve_left
    (fun hc => hn (card_eq_one.mp hc))
  obtain ⟨r,hr⟩ := exists_prime_orderOf_dvd_card' 2 hd
  let e : M22 ≃* MulAut.innerSubgroup M22 := MonoidHom.ofInjective
    (MulAut.conj_injective_of_center_eq_bot m22_center_eq_bot)
  let b : B →* M22 := e.symm.toMonoidHom.comp (inclusion hB)
  have hb : Function.Injective b := e.symm.injective.comp (inclusion_injective hB)
  have hbf : b.range ≤ (r : MulAut M22).fixedSubgroup := by
    rintro _ ⟨x,rfl⟩
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    apply MulAut.conj_injective_of_center_eq_bot m22_center_eq_bot
    have he : MulAut.conj (b x) = (x : MulAut M22) :=
      congrArg Subtype.val (e.apply_symm_apply (inclusion hB x))
    have hc : MulAut.conj ((r : MulAut M22) (b x)) =
        (r : MulAut M22) * MulAut.conj (b x) * (r : MulAut M22)⁻¹ := by
      ext y
      simp
    rw [hc,he,←hUB r.property x x.property,mul_inv_cancel_right]
  apply m22_involution_not_nine_dvd_fixed_card (r : MulAut M22) ((orderOf_coe r).trans hr)
  have hdB : 9 ∣ Nat.card b.range := by
    rw [←Nat.card_congr (MonoidHom.ofInjective hb).toEquiv]
    exact h9
  exact hdB.trans (card_dvd_of_le hbf)

private theorem large_irreducible_m22_kernel
    {C : Type*} [Group C] [Finite C]
    (a : C →* MulAut M22) (B E : Subgroup C) [IsElementaryAbelian 2 E]
    (hBE : B ≤ normalizer (E : Set C))
    (hirr : ∀ X : Subgroup C, X ≤ E → B ≤ normalizer (X : Set C) → X = ⊥ ∨ X = E)
    (hcard : 32 < Nat.card E) : E ≤ a.ker := by
  have hn : B ≤ normalizer (E ⊓ a.ker : Subgroup C) :=
    (le_inf hBE (by rw [normalizer_eq_top]; exact le_top)).trans inf_normalizer_le_normalizer_inf
  rcases hirr (E ⊓ a.ker) inf_le_left hn with hb | he
  · have hi : Function.Injective (a.comp E.subtype) := by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      ext x
      change a x = 1 ↔ x = 1
      constructor
      · intro hx
        apply Subtype.ext
        change (x : C) = 1
        have hh : (x : C) ∈ E ⊓ a.ker := ⟨x.property,hx⟩
        simpa only [hb,mem_bot] using hh
      · rintro rfl
        exact map_one _
    have hc : Nat.card (E.map a) ≤ 32 := by
      let : IsElementaryAbelian 2 (E.map a) := IsElementaryAbelian.map a
      exact (primeRank_le_iff_elementary_card_le (MulAut M22)).mp
        m22_automorphism_twoRank_le_five _ inferInstance
    have hec : Nat.card (E.map a) = Nat.card E := by
      simpa only [MonoidHom.range_comp,range_subtype] using
        Nat.card_congr (MonoidHom.ofInjective hi).symm.toEquiv
    omega
  · exact he.symm.le.trans inf_le_right

private theorem normalized_twoGroup_kernel_of_nine_section
    {C S : Type*} [Group C] [Finite C] [Group S] [Finite S] [IsSimpleGroup S]
    (hS : ¬ Group.IsSolvable S) (h9 : 9 ∣ Nat.card S)
    (a : C →* MulAut M22) [Group.IsSolvable a.ker]
    (B U E : Subgroup C) [Group.IsPerfect B] [IsElementaryAbelian 2 E]
    (b : B →* S) (hb : Function.Surjective b)
    (hp : IsPGroup 2 U) (hBE : B ≤ normalizer (E : Set C))
    (hirr : ∀ X : Subgroup C, X ≤ E → B ≤ normalizer (X : Set C) → X = ⊥ ∨ X = E)
    (hcard : 32 < Nat.card E) (hdisp : ⁅U,B⁆ ≤ E) : U ≤ a.ker := by
  have hEk := large_irreducible_m22_kernel a B E hBE hirr hcard
  let f := a.comp B.subtype
  let t : f.ker →* a.ker := {
    toFun x := ⟨x.val.val,x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  let : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective
    (f := t) (fun x y he => Subtype.ext (Subtype.ext (congrArg (fun z : a.ker => (z : C)) he)))
  obtain ⟨W,g,hg⟩ := simple_section_quotient_of_solvable_kernel hS f.ker
    (⊤ : Subgroup B) (b.comp (topEquiv : (⊤ : Subgroup B) ≃* B).toMonoidHom)
    (hb.comp topEquiv.surjective)
  have hd : 9 ∣ Nat.card (B.map a) := by
    have hh := (h9.trans (card_dvd_of_surjective g hg)).trans W.card_subgroup_dvd_card
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at hh
    simpa only [f,MonoidHom.range_comp,range_subtype] using hh
  have hc : U.map a ≤ centralizer (B.map a : Set (MulAut M22)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [←map_commutator]
    exact (Subgroup.map_eq_bot_iff _).mpr (hdisp.trans hEk)
  let : Group.IsPerfect (B.map a) := Group.IsPerfect.map a
  exact (Subgroup.map_eq_bot_iff U).mp
    (nine_actor_two_centralizer (B.map a) (U.map a) hd (hp.map a) hc)

private theorem irreducible_equiv {C D : Type*} [Group C] [Group D]
    (e : C ≃* D) (B E : Subgroup C)
    (hirr : ∀ X : Subgroup C, X ≤ E → B ≤ normalizer (X : Set C) → X = ⊥ ∨ X = E) :
    ∀ X : Subgroup D, X ≤ E.map e.toMonoidHom →
      B.map e.toMonoidHom ≤ normalizer (X : Set D) → X = ⊥ ∨ X = E.map e.toMonoidHom := by
  intro X hXE hBX
  have hpre : X.comap e.toMonoidHom ≤ E := by
    have hh := comap_mono (f := e.toMonoidHom) hXE
    rwa [comap_map_eq, (MonoidHom.ker_eq_bot_iff _).mpr e.injective,sup_bot_eq] at hh
  have hn : B ≤ normalizer (X.comap e.toMonoidHom : Set C) :=
    ((show B ≤ (B.map e.toMonoidHom).comap e.toMonoidHom from
      fun _ hx => mem_map_of_mem _ hx).trans (comap_mono hBX)).trans (X.le_normalizer_comap _)
  have hmap : (X.comap e.toMonoidHom).map e.toMonoidHom = X :=
    map_comap_eq_self (by rw [e.toMonoidHom.range_eq_top.mpr e.surjective]; exact le_top)
  rcases hirr _ hpre hn with hh | hh
  · exact .inl (by rw [←hmap,hh,Subgroup.map_bot])
  · exact .inr (by rw [←hmap,hh])

private theorem involution_centralizer_nine_section_radical_elementary
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (hS : ¬ Group.IsSolvable S) (h9 : 9 ∣ Nat.card S)
    (z : Janko4.Model) (hz : orderOf z = 2)
    (B U E : Subgroup (centralizer ({z} : Set Janko4.Model)))
    [Group.IsPerfect B] [IsElementaryAbelian 2 E]
    (b : B →* S) (hb : Function.Surjective b)
    (hp : IsPGroup 2 U) (_hn : B ≤ normalizer (U : Set _))
    (hEU : E ≤ U) (hE : 128 < Nat.card E)
    (hBE : B ≤ normalizer (E : Set _))
    (hirr : ∀ X : Subgroup (centralizer ({z} : Set Janko4.Model)),
      X ≤ E → B ≤ normalizer (X : Set _) → X = ⊥ ∨ X = E)
    (hdisp : ⁅U,B⁆ ≤ E) : IsElementaryAbelian 2 U := by
  rcases centralizer_equiv_first_or_second z hz with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · let a := First.QuotientExtension.centralizerMathieuAction
    let Q := First.QuotientExtension.Q
    let R := First.QuotientExtension.R
    let : Group.IsSolvable a.ker := by
      change Group.IsSolvable First.QuotientExtension.centralizerMathieuAction.ker
      rw [First.QuotientExtension.centralizerMathieuAction_ker]
      let : Group.IsNilpotent (Q.subgroupOf R) :=
        (pCore_isPGroup.comap_subtype (p := 2) (G := First.centralizer)).isNilpotent
      let : Group.IsSolvable (R ⧸ Q.subgroupOf R) :=
        Group.isSolvable_of_isSolvable_injective
          (f := First.QuotientExtension.RQuotientEquivC3.toMonoidHom)
          First.QuotientExtension.RQuotientEquivC3.injective
      exact (Group.isSolvable_iff_subgroup_quotient (Q.subgroupOf R)).mpr
        ⟨inferInstance,inferInstance⟩
    let B' := B.map e.toMonoidHom
    let U' := U.map e.toMonoidHom
    let E' := E.map e.toMonoidHom
    let : Group.IsPerfect B' := Group.IsPerfect.map _
    let : IsElementaryAbelian 2 E' := IsElementaryAbelian.map _
    let d := e.subgroupMap B
    have hUR : U' ≤ R := by
      have hh := normalized_twoGroup_kernel_of_nine_section hS h9 a B' U' E'
        (b.comp d.symm.toMonoidHom) (hb.comp d.symm.surjective)
        (hp.map _) ((map_mono hBE).trans (E.le_normalizer_map _))
        (irreducible_equiv e B E hirr) (by rw [card_map_of_injective e.injective]; omega)
        (by rw [←map_commutator]; exact map_mono hdisp)
      exact hh.trans_eq First.QuotientExtension.centralizerMathieuAction_ker
    let Ur := U'.subgroupOf R
    let q := QuotientGroup.mk' (Q.subgroupOf R)
    have hzero : Ur.map q = ⊥ := by
      apply card_eq_one.mp
      rcases (((hp.map e.toMonoidHom).comap_subtype (K := R)).map q).card_eq_or_dvd
        with hc | hc
      · exact hc
      · have hd := hc.trans (Ur.map q).card_subgroup_dvd_card
        rw [Nat.card_congr First.QuotientExtension.RQuotientEquivC3.toEquiv] at hd
        norm_num at hd
    have hUQ : U' ≤ Q := by
      intro u hu
      have hq := (Subgroup.map_eq_bot_iff Ur).mp hzero (show (⟨u,hUR hu⟩ : R) ∈ Ur from hu)
      have ht : (⟨u,hUR hu⟩ : R) ∈ Q.subgroupOf R := by
        rw [←QuotientGroup.ker_mk' (Q.subgroupOf R)]
        exact hq
      exact ht
    have hEQ : E' ≤ Q := (map_mono hEU).trans hUQ
    let EQ := E'.subgroupOf Q
    let : IsElementaryAbelian 2 EQ := IsElementaryAbelian.subgroupOf hEQ
    let := First.centralizer_twoCore_extraspecial
    have hc := extraspecial_prime_abelian_card_sq_le_any (p := 2) EQ
    have hec : Nat.card EQ = Nat.card E := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hEQ).toEquiv]
      exact card_map_of_injective e.injective
    rw [hec,First.centralizer_twoCore_card] at hc
    exfalso
    nlinarith
  · let a := Second.ambientExtension.rightHom
    let := Second.ambientKernel_elementary
    let : Group.IsNilpotent a.ker :=
      (IsElementaryAbelian.isPGroup 2 Second.ambientKernel).isNilpotent
    let B' := B.map e.toMonoidHom
    let U' := U.map e.toMonoidHom
    let E' := E.map e.toMonoidHom
    let : IsElementaryAbelian 2 E' := IsElementaryAbelian.map _
    let : Group.IsPerfect B' := Group.IsPerfect.map _
    let d := e.subgroupMap B
    have hu := normalized_twoGroup_kernel_of_nine_section hS h9 a B' U' E'
      (b.comp d.symm.toMonoidHom) (hb.comp d.symm.surjective)
      (hp.map _) ((map_mono hBE).trans (E.le_normalizer_map _))
        (irreducible_equiv e B E hirr) (by rw [card_map_of_injective e.injective]; omega)
        (by rw [←map_commutator]; exact map_mono hdisp)
    let : IsElementaryAbelian 2 U' := IsElementaryAbelian.of_injective
      (inclusion hu) (inclusion_injective hu)
    exact @IsElementaryAbelian.of_injective 2 U U' _ _ inferInstance
      (e.subgroupMap U).toMonoidHom (e.subgroupMap U).injective

/-- A large irreducible elementary central displacement, with a nonsolvable
simple section divisible by nine, forces the native radical to be elementary. -/
theorem nine_section_radical_elementary
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (hS : ¬ Group.IsSolvable S) (h9 : 9 ∣ Nat.card S)
    (B U E : Subgroup Janko4.Model) [Group.IsPerfect B] [IsElementaryAbelian 2 E]
    (b : B →* S) (hb : Function.Surjective b)
    (hp : IsPGroup 2 U) (hn : B ≤ normalizer (U : Set _))
    (hEU : E ≤ U) (hE : 128 < Nat.card E)
    (hBE : B ≤ normalizer (E : Set _))
    (hirr : ∀ X : Subgroup Janko4.Model, X ≤ E → B ≤ normalizer (X : Set _) → X = ⊥ ∨ X = E)
    (hcent : U ≤ centralizer (E : Set _)) (hdisp : ⁅U,B⁆ ≤ E) :
    IsElementaryAbelian 2 U := by
  let : Fact (IsPGroup 2 U) := ⟨hp⟩
  by_contra hnon
  have hphi : frattini U ≠ ⊥ := fun hh => hnon
    ((frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hh)
  have hfixed : frattini U ≤ (centralizer (B : Set Janko4.Model)).comap U.subtype := by
    rw [hp.frattini_eq_closure_squares]
    apply (closure_le _).mpr
    rintro _ ⟨u,rfl⟩
    exact sq_mem_centralizer_of_central_commutators U B E hcent hdisp u.property
  let F := center U ⊓ frattini U
  have hF : F ≠ ⊥ := center_inf_ne_bot_of_normal hp (frattini U) hphi
  have hd : 2 ∣ Nat.card F := (hp.to_subgroup F).card_eq_or_dvd.resolve_left
    (fun hc => hF (card_eq_one.mp hc))
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' 2 hd
  let t : Janko4.Model := z.val.val
  have ht : orderOf t = 2 := (orderOf_coe z.val).trans ((orderOf_coe z).trans hz)
  let C := centralizer ({t} : Set Janko4.Model)
  have hBC : B ≤ C := by
    intro b hb
    exact mem_centralizer_singleton_iff.mpr (hfixed z.property.2 b hb)
  have hUC : U ≤ C := by
    intro u hu
    exact mem_centralizer_singleton_iff.mpr
      (congrArg U.subtype (mem_center_iff.mp z.property.1 ⟨u,hu⟩))
  have hEC : E ≤ C := hEU.trans hUC
  let Bc := B.subgroupOf C
  let Uc := U.subgroupOf C
  let Ec := E.subgroupOf C
  let eb := subgroupOfEquivOfLe hBC
  let eu := subgroupOfEquivOfLe hUC
  let : Group.IsPerfect Bc := Group.IsPerfect.ofSurjective
    (f := eb.symm.toMonoidHom) eb.symm.surjective
  let : IsElementaryAbelian 2 Ec := IsElementaryAbelian.subgroupOf hEC
  have hirrc : ∀ X : Subgroup C, X ≤ Ec → Bc ≤ normalizer (X : Set C) →
      X = ⊥ ∨ X = Ec := by
    intro X hXE hBX
    have hXg : X.map C.subtype ≤ E := (map_mono hXE).trans (map_comap_le _ _)
    have hBg : B ≤ normalizer (X.map C.subtype : Set Janko4.Model) := by
      rw [←map_subgroupOf_eq_of_le hBC]
      exact (map_mono hBX).trans (X.le_normalizer_map _)
    rcases hirr _ hXg hBg with hh | hh
    · exact .inl ((X.map_eq_bot_iff_of_injective C.subtype_injective).mp hh)
    · exact .inr (map_injective C.subtype_injective
        (hh.trans (map_subgroupOf_eq_of_le hEC).symm))
  let hh : IsElementaryAbelian 2 Uc := involution_centralizer_nine_section_radical_elementary hS h9 t ht
    Bc Uc Ec (b.comp eb.toMonoidHom) (hb.comp eb.surjective)
    (hp.comap_subtype (K := C))
    ((comap_mono hn).trans (U.le_normalizer_comap C.subtype))
    (comap_mono hEU) (by rw [Nat.card_congr (subgroupOfEquivOfLe hEC).toEquiv]; exact hE)
    ((comap_mono hBE).trans (E.le_normalizer_comap C.subtype)) hirrc
    (by
      apply (map_le_map_iff_of_injective C.subtype_injective).mp
      rw [map_commutator,map_subgroupOf_eq_of_le hUC,map_subgroupOf_eq_of_le hBC,
        map_subgroupOf_eq_of_le hEC]
      exact hdisp)
  let := hh
  exact hnon (IsElementaryAbelian.of_injective eu.symm.toMonoidHom eu.symm.injective)

end Janko4.InvolutionCentralizers
