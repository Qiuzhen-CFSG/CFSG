module
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.LargeAbelianImage
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.MathieuTwelveSections
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupTheory.PerfectSimpleImage
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction
public import Theory.GroupTheory.BinaryCentralCommutatorQuotient
public import Theory.Frattini.BinarySquares

/-!
# Elementary radicals under an M₂₂ section in J₄

A perfect M₂₂ section has full inner image under either native involution
centralizer action. Any normalized two-group therefore lies in that action's
solvable kernel. The first kernel cannot contain an abelian subgroup of order
greater than 128; the second is elementary. Central binary displacement fixes
the Frattini subgroup, so a nonelementary radical would supply a common fixed
central involution and contradict these two alternatives.

Source application: Aschbacher–Smith 4.2.13 and 4.4.14, printed pp.611–612,
624–625. The literal centralizer models and their ATLAS attribution are retained
through the imported modules; no covering kernel is discarded.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Sporadic.Mathieu
open scoped IsMulCommutative
namespace Janko4.InvolutionCentralizers
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private theorem m22_not_solvable : ¬ Group.IsSolvable M22 := by
  let := m22_isSimpleGroup
  intro hs
  let : CommGroup M22 := { (inferInstance : Group M22) with
    mul_comm := IsSimpleGroup.comm_iff_isSolvable.mpr hs }
  have hp := IsSimpleGroup.prime_card (α := M22)
  rw [m22_order] at hp
  norm_num at hp

private theorem m22_section_image_eq_inner {C : Type*} [Group C] [Finite C]
    (a : C →* MulAut M22) [Group.IsSolvable a.ker]
    (B : Subgroup C) [Group.IsPerfect B] (b : B →* M22) (hb : Function.Surjective b) :
    B.map a = MulAut.innerSubgroup M22 := by
  let := m22_isSimpleGroup
  let f := a.comp B.subtype
  let t : f.ker →* a.ker :=
    { toFun x := ⟨x.val.val,x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  let : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective
    (f := t) (fun x y he => Subtype.ext (Subtype.ext (congrArg (fun z : a.ker => (z : C)) he)))
  obtain ⟨W,g,hg⟩ := simple_section_quotient_of_solvable_kernel m22_not_solvable f.ker
    (⊤ : Subgroup B) (b.comp (topEquiv : (⊤ : Subgroup B) ≃* B).toMonoidHom)
    (hb.comp topEquiv.surjective)
  have hlo : Nat.card M22 ≤ Nat.card f.range := by
    rw [←Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
    exact (Nat.card_le_card_of_surjective g hg).trans W.card_le_card_group
  have hn : f.range ≤ MulAut.innerSubgroup M22 := by
    let : Group.IsPerfect f.range := Group.IsPerfect.range f
    let : Group.IsNilpotent (MulAut.Outer M22) :=
      (IsPGroup.of_card_dvd_pow (p := 2) (n := 1)
        (by simpa only [pow_one] using
          M22TripleCover.ScalarAutomorphisms.m22_outer_card_dvd_two)).isNilpotent
    exact (le_solvableResidual_of_isPerfect f.range).trans
      (solvableResidual_le_of_solvable_quotient _)
  have he : Nat.card (MulAut.innerSubgroup M22) = Nat.card M22 :=
    (Nat.card_congr (MonoidHom.ofInjective
      (MulAut.conj_injective_of_center_eq_bot m22_center_eq_bot)).toEquiv).symm
  have hh : f.range = MulAut.innerSubgroup M22 := eq_of_le_of_card_ge hn (he ▸ hlo)
  simpa only [f,MonoidHom.range_comp,range_subtype] using hh

private theorem pgroup_eq_bot_of_inner_normalizes
    (U : Subgroup (MulAut M22)) (hp : IsPGroup 2 U)
    (hn : MulAut.innerSubgroup M22 ≤ normalizer (U : Set (MulAut M22))) : U = ⊥ := by
  let A := MulAut.innerSubgroup M22
  let e : M22 ≃* A := MonoidHom.ofInjective
    (MulAut.conj_injective_of_center_eq_bot m22_center_eq_bot)
  let := m22_isSimpleGroup
  let : IsSimpleGroup A := e.symm.isSimpleGroup
  let : (U.subgroupOf A).Normal := normal_subgroupOf_of_le_normalizer hn
  have hi : U ⊓ A = ⊥ := by
    rcases (inferInstance : (U.subgroupOf A).Normal).eq_bot_or_eq_top with hh | hh
    · have hm := congrArg (map A.subtype) hh
      simpa only [subgroupOf_map_subtype,Subgroup.map_bot,inf_comm] using hm
    · have hAU : A ≤ U := subgroupOf_eq_top.mp hh
      obtain ⟨n,he⟩ := (hp.to_le hAU).exists_card_eq
      have hdiv : 11 ∣ Nat.card A := by rw [←Nat.card_congr e.toEquiv,m22_order]; decide
      rw [he] at hdiv
      have hbad := (show Nat.Prime 11 by decide).dvd_of_dvd_pow hdiv
      norm_num at hbad
  have hcomm : ⁅U,A⁆ = ⊥ := by
    apply bot_unique
    rw [←hi]
    exact le_inf (le_normalizer_iff_commutator_le_left.mp hn)
      (commutator_le_right U A)
  apply bot_unique
  exact (commutator_eq_bot_iff_le_centralizer.mp hcomm).trans_eq
    (MulAut.centralizer_innerSubgroup_eq_bot m22_center_eq_bot)

private theorem normalized_twoGroup_le_mathieu_kernel {C : Type*} [Group C] [Finite C]
    (a : C →* MulAut M22) [Group.IsSolvable a.ker]
    (B U : Subgroup C) [Group.IsPerfect B]
    (b : B →* M22) (hb : Function.Surjective b)
    (hp : IsPGroup 2 U) (hn : B ≤ normalizer (U : Set C)) : U ≤ a.ker := by
  apply (map_eq_bot_iff U).mp
  apply pgroup_eq_bot_of_inner_normalizes _ (hp.map a)
  rw [←m22_section_image_eq_inner a B b hb]
  exact (map_mono hn).trans (U.le_normalizer_map a)

private theorem involution_centralizer_m22_radical_elementary
    (z : Janko4.Model) (hz : orderOf z = 2)
    (B U E : Subgroup (centralizer ({z} : Set Janko4.Model)))
    [Group.IsPerfect B] [IsElementaryAbelian 2 E]
    (b : B →* M22) (hb : Function.Surjective b)
    (hp : IsPGroup 2 U) (hn : B ≤ normalizer (U : Set _))
    (hEU : E ≤ U) (hE : 128 < Nat.card E) : IsElementaryAbelian 2 U := by
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
      have hh := normalized_twoGroup_le_mathieu_kernel a B' U'
        (b.comp d.symm.toMonoidHom) (hb.comp d.symm.surjective)
        (hp.map _) ((map_mono hn).trans (U.le_normalizer_map _))
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
      have hq := (map_eq_bot_iff Ur).mp hzero (show (⟨u,hUR hu⟩ : R) ∈ Ur from hu)
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
    let : Group.IsPerfect B' := Group.IsPerfect.map _
    let d := e.subgroupMap B
    have hu := normalized_twoGroup_le_mathieu_kernel a B' U'
      (b.comp d.symm.toMonoidHom) (hb.comp d.symm.surjective)
      (hp.map _) ((map_mono hn).trans (U.le_normalizer_map _))
    let : IsElementaryAbelian 2 U' := IsElementaryAbelian.of_injective
      (inclusion hu) (inclusion_injective hu)
    exact @IsElementaryAbelian.of_injective 2 U U' _ _ inferInstance
      (e.subgroupMap U).toMonoidHom (e.subgroupMap U).injective

/-- Central elementary displacement by a perfect M22 section forces its
native two-radical to be elementary. -/
theorem m22_radical_elementary
    (B U E : Subgroup Janko4.Model) [Group.IsPerfect B] [IsElementaryAbelian 2 E]
    (b : B →* M22) (hb : Function.Surjective b)
    (hp : IsPGroup 2 U) (hn : B ≤ normalizer (U : Set _))
    (hEU : E ≤ U) (hE : 128 < Nat.card E)
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
  let hh : IsElementaryAbelian 2 Uc := involution_centralizer_m22_radical_elementary t ht
    Bc Uc Ec (b.comp eb.toMonoidHom) (hb.comp eb.surjective)
    (hp.comap_subtype (K := C))
    ((comap_mono hn).trans (U.le_normalizer_comap C.subtype))
    (comap_mono hEU) (by rw [Nat.card_congr (subgroupOfEquivOfLe hEC).toEquiv]; exact hE)
  let := hh
  exact hnon (IsElementaryAbelian.of_injective eu.symm.toMonoidHom eu.symm.injective)
end Janko4.InvolutionCentralizers
