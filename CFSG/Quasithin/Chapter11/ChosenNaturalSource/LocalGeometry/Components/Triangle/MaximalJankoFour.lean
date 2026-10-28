module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.MaximalSieveSp4
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Residual

/-!
# Excluding a J₄ maximal overcomponent of the third vertex

Each of the original normalized local A₅ sections centralizes an involution
in the center of the same full Sylow. That center has order two, so their
join lies in one involution centralizer. The actual maps from both native
centralizers onto Aut(M₂₂) have solvable kernels with no factor seven.

Perfectness puts both images inside inner M₂₂. The normalized local A₅
comparison identifies them, with order 960. Thus their original join has
no factor seven. Of the three triangle quotients, only SL₃(4) has order
dividing |J₄|, and its factor seven survives the original two-core map.
This excludes J₄ while retaining both marked sections and their full Sylow.

MaximalFaithfulSp4 applies the result to the literal I = K₀ ∨ L₂ and closes
its maximality, still conditional on the original common normal Q.
Source: Aschbacher--Smith, 1.2.8(4), A.3.12--14 and 11.1.2,
printed pp.47--50,507,762--764; GLS3 Table 5.3i for the native centralizers.
The imported matrix carriers retain their existing ATLAS attribution.
-/

open Subgroup Theory.GroupTheory Sporadic.Mathieu
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
open FiveLocalFF.SolvableQuotients
public noncomputable section
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private theorem triangle_order {A : Type*} [Group A]
    (hm : Source.IsSL A 3 4 ∨ Source.IsSp A 2 4 ∨ ClassificationModels.IsG2At A 4) :
    Nat.card A = 60480 ∨ Nat.card A = 979200 ∨ Nat.card A = 251596800 := by
  rcases hm with hm | hm | hm
  · left
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [Nat.card_congr e.toEquiv,
      card_eq_card_quotient_mul_card_subgroup (center (Matrix.SpecialLinearGroup (Fin 3) F)),
      Atlas.ExceptionalSupport.card_sl_center]
    change Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) * _ = _
    rw [Matrix.PSL3.LinearThree.card_projective,hF]
    norm_num
  · right; left
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [Nat.card_congr e.toEquiv,Theory.SpecificGroups.SymplecticFour.card_sp,hF]
    norm_num
  · right; right
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [Nat.card_congr e.toEquiv,Atlas.G2.card_Model,hF]
    norm_num

private theorem core_quotient_card_dvd {G : Type*} [Group G] [Finite G]
    {I J : Subgroup G} (hIJ : I ≤ J) :
    Nat.card (I ⧸ pCore 2 I) ∣ Nat.card (J ⧸ pCore 2 J) := by
  let B := I.subgroupOf J
  let q := QuotientGroup.mk' (pCore 2 J)
  let e := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hIJ)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hIJ))
  have hk : IsPGroup 2 (q.subgroupMap B).ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let a := MonoidHom.quotientPCoreEquivOfSurjective
    (q.subgroupMap B) (q.subgroupMap_surjective B) hk
  rw [←Nat.card_congr e.toEquiv,Nat.card_congr a.toEquiv]
  exact (card_quotient_dvd_card _).trans (B.map q).card_subgroup_dvd_card

private theorem dvd_card_map_of_coprime_kernel
    {A H : Type*} [Group A] [Finite A] [Group H]
    (f : A →* H) (B : Subgroup A) {n : ℕ}
    (hc : Nat.Coprime n (Nat.card f.ker)) (hd : n ∣ Nat.card B) :
    n ∣ Nat.card (B.map f) := by
  let g := f.subgroupMap B
  have hcop : Nat.Coprime n (Nat.card g.ker) := by
    rw [ker_subgroupMap]
    exact hc.of_dvd_right (card_comap_dvd_of_injective f.ker B.subtype B.subtype_injective)
  have hh := g.ker.card_mul_index
  rw [index_eq_card,Nat.card_congr
    (QuotientGroup.quotientKerEquivOfSurjective g (f.subgroupMap_surjective B)).toEquiv] at hh
  exact hcop.dvd_of_dvd_mul_left (hh.symm ▸ hd)

private theorem five_equiv_maximal {A : Type*} [Group A]
    (hm : ClassicalGroup.IsPSL A 2 4) : Nonempty (A ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  exact (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).map
    (fun a => e.trans a)


private theorem aut_m22_residual :
    solvableResidual (MulAut M22) = MulAut.innerSubgroup M22 := by
  let : Group.IsPerfect M22 := Group.IsPerfect.ofSurjective
    (f := M22TripleCover.centralQuotientEquiv.toMonoidHom.comp
      (QuotientGroup.mk' (center M22TripleCover)))
    (M22TripleCover.centralQuotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _))
  let : Group.IsPerfect (MulAut.innerSubgroup M22) := Group.IsPerfect.range MulAut.conj
  let : Group.IsNilpotent (MulAut.Outer M22) :=
    (IsPGroup.of_card_dvd_pow (p := 2) (n := 1)
      (by simpa only [pow_one] using
        M22TripleCover.ScalarAutomorphisms.m22_outer_card_dvd_two)).isNilpotent
  exact le_antisymm (solvableResidual_le_of_solvable_quotient _)
    (le_solvableResidual_of_isPerfect _)

private theorem aut_m22_five_pair (S : Sylow 2 (MulAut M22)) (B C : Subgroup (MulAut M22))
    (hB : B ∈ localCComponents S) (hC : C ∈ localCComponents S)
    (hnB : (S : Subgroup (MulAut M22)) ≤ normalizer (B : Set (MulAut M22)))
    (hnC : (S : Subgroup (MulAut M22)) ≤ normalizer (C : Set (MulAut M22)))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (eC : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5)) :
    B = C ∧ Nat.card B = 960 := by
  let N := MulAut.innerSubgroup M22
  let e : N ≃* M22 :=
    (MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot m22_center_eq_bot)).symm
  let := local_perfect hB
  let := local_perfect hC
  have hBN : B ≤ N := (le_solvableResidual_of_isPerfect B).trans_eq aut_m22_residual
  have hCN : C ≤ N := (le_solvableResidual_of_isPerfect C).trans_eq aut_m22_residual
  obtain ⟨P,hP,hBP⟩ := exists_local_sylow_restriction S hB hBN
    (inferInstance : N.Normal).isSubnormal
  have hCP : C.subgroupOf N ∈ localCComponents P := hP.symm ▸ local_restrict hC hCN
  have hPB : (P : Subgroup N) ≤ normalizer (B.subgroupOf N : Set N) := by
    rw [hP,←subgroupOf_normalizer_eq hBN]
    exact comap_mono hnB
  have hPC : (P : Subgroup N) ≤ normalizer (C.subgroupOf N : Set N) := by
    rw [hP,←subgroupOf_normalizer_eq hCN]
    exact comap_mono hnC
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot e.injective]; infer_instance
  let b := subgroupOfEquivOfLe hBN
  let c := subgroupOfEquivOfLe hCN
  obtain ⟨eb⟩ := section_map e.toMonoidHom (B.subgroupOf N) hBP
    ((QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans eB)
  obtain ⟨ec⟩ := section_map e.toMonoidHom (C.subgroupOf N) hCP
    ((QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans eC)
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have he := m22_local_five_eq P' _ _
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hBP e.toMonoidHom)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hCP e.toMonoidHom)
    ((map_mono hPB).trans (le_normalizer_map e.toMonoidHom))
    ((map_mono hPC).trans (le_normalizer_map e.toMonoidHom)) eb ec
  have hh := map_injective e.injective he
  have hBC : B = C := by
    simpa only [map_subgroupOf_eq_of_le hBN,map_subgroupOf_eq_of_le hCN] using
      congrArg (map N.subtype) hh
  refine ⟨hBC,?_⟩
  rw [←Nat.card_congr b.toEquiv,←card_map_of_injective (f := e.toMonoidHom) e.injective]
  rw [←(pCore 2 ((B.subgroupOf N).map e.toMonoidHom)).card_mul_index]
  change Nat.card (pCore 2 ((B.subgroupOf N).map e.toMonoidHom)) *
    Nat.card (((B.subgroupOf N).map e.toMonoidHom) ⧸ pCore 2 ((B.subgroupOf N).map e.toMonoidHom)) = 960
  rw [(M22LocalA5Shape.core_shape_of_normalized P' _
    ((map_mono hPB).trans (le_normalizer_map e.toMonoidHom)) eb).2,
    Nat.card_congr eb.toEquiv,nat_card_alternatingGroup]
  norm_num [Nat.factorial]

private theorem no_seven_pair_mathieuAction
    {A : Type*} [Group A] [Finite A]
    (S : Sylow 2 A) (B C : Subgroup A)
    (hB : B ∈ localCComponents S) (hC : C ∈ localCComponents S)
    (hnB : (S : Subgroup A) ≤ normalizer (B : Set A))
    (hnC : (S : Subgroup A) ≤ normalizer (C : Set A))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (eC : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5))
    (f : A →* MulAut M22) (hf : Function.Surjective f)
    [Group.IsSolvable f.ker] (hc : Nat.Coprime 7 (Nat.card f.ker)) :
    ¬ 7 ∣ Nat.card (B ⊔ C : Subgroup A) := by
  obtain ⟨eb⟩ := section_map f B hB eB
  obtain ⟨ec⟩ := section_map f C hC eC
  obtain ⟨he,hcard⟩ := aut_m22_five_pair (S.mapSurjective (f := f) hf) (B.map f) (C.map f)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hB f)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hC f)
    ((map_mono hnB).trans (le_normalizer_map f))
    ((map_mono hnC).trans (le_normalizer_map f)) eb ec
  intro hd
  let g := f.subgroupMap (B ⊔ C)
  have hcop : Nat.Coprime 7 (Nat.card g.ker) := by
    rw [ker_subgroupMap]
    exact hc.of_dvd_right (card_comap_dvd_of_injective f.ker
      (B ⊔ C).subtype (B ⊔ C).subtype_injective)
  have hh := g.ker.card_mul_index
  rw [index_eq_card,Nat.card_congr
    (QuotientGroup.quotientKerEquivOfSurjective g (f.subgroupMap_surjective _)).toEquiv] at hh
  have hd' := hcop.dvd_of_dvd_mul_left (hh.symm ▸ hd)
  rw [Subgroup.map_sup,←he,sup_idem,hcard] at hd'
  norm_num at hd'

private theorem centralizer_mathieuAction (z : Janko4.Model) (hz : orderOf z = 2) :
    ∃ f : centralizer ({z} : Set Janko4.Model) →* MulAut M22,
      Function.Surjective f ∧ Group.IsSolvable f.ker ∧ Nat.Coprime 7 (Nat.card f.ker) := by
  have transfer {A : Type} [Group A] [Finite A]
      (e : centralizer ({z} : Set Janko4.Model) ≃* A)
      (f : A →* MulAut M22) (hf : Function.Surjective f)
      (hs : Group.IsSolvable f.ker) (hc : Nat.Coprime 7 (Nat.card f.ker)) :
      ∃ g : centralizer ({z} : Set Janko4.Model) →* MulAut M22,
        Function.Surjective g ∧ Group.IsSolvable g.ker ∧ Nat.Coprime 7 (Nat.card g.ker) := by
    let g := f.comp e.toMonoidHom
    let a : g.ker ≃* f.ker := MulEquiv.ofBijective
      (e.toMonoidHom.subgroupComap f.ker)
      ⟨fun x y h => Subtype.ext (e.injective (congrArg Subtype.val h)),
        e.toMonoidHom.subgroupComap_surjective_of_surjective f.ker e.surjective⟩
    let := hs
    exact ⟨g,hf.comp e.surjective,
      Group.isSolvable_of_isSolvable_injective (f := a.toMonoidHom) a.injective,
      (Nat.card_congr a.toEquiv).symm ▸ hc⟩
  rcases Janko4.InvolutionCentralizers.centralizer_equiv_first_or_second z hz with h | h
  · obtain ⟨e⟩ := h
    open Janko4.InvolutionCentralizers.First in
    open QuotientExtension in
    have hc : Nat.Coprime 7 (Nat.card centralizerMathieuAction.ker) := by
      rw [centralizerMathieuAction_ker,
        card_eq_card_quotient_mul_card_subgroup (Q.subgroupOf R),
        Nat.card_congr RQuotientEquivC3.toEquiv]
      have hp : IsPGroup 2 (Q.subgroupOf R) := pCore_isPGroup.comap_subtype
      obtain ⟨n,hn⟩ := hp.exists_card_eq
      rw [hn,show Nat.card (Multiplicative (ZMod 3)) = 3 from Nat.card_zmod 3]
      exact (by decide : Nat.Coprime 7 3).mul_right ((by decide : Nat.Coprime 7 2).pow_right n)
    open Janko4.InvolutionCentralizers.First in
    open QuotientExtension in
    have hs : Group.IsSolvable centralizerMathieuAction.ker := by
      rw [centralizerMathieuAction_ker]
      let : Group.IsNilpotent (Q.subgroupOf R) := pCore_isPGroup.comap_subtype.isNilpotent
      let : Group.IsSolvable (R ⧸ Q.subgroupOf R) :=
        Group.isSolvable_of_isSolvable_injective (f := RQuotientEquivC3.toMonoidHom)
          RQuotientEquivC3.injective
      exact (Group.isSolvable_iff_subgroup_quotient (Q.subgroupOf R)).mpr
        ⟨inferInstance,inferInstance⟩
    open Janko4.InvolutionCentralizers.First in
    exact transfer e QuotientExtension.centralizerMathieuAction
      (QuotientExtension.quotientConjugation_surjective.comp centralizerExtension.rightHom_surjective)
      hs hc
  · obtain ⟨e⟩ := h
    open Janko4.InvolutionCentralizers.Second in
    let : IsElementaryAbelian 2 ambientKernel := ambientKernel_elementary
    open Janko4.InvolutionCentralizers.Second in
    let : Group.IsNilpotent ambientKernel := (IsElementaryAbelian.isPGroup 2 ambientKernel).isNilpotent
    open Janko4.InvolutionCentralizers.Second in
    exact transfer e ambientExtension.rightHom ambientExtension.rightHom_surjective inferInstance
      (show Nat.Coprime 7 (Nat.card ambientKernel) by rw [ambientKernel_card]; decide)

private theorem j4_five_involution (S : Sylow 2 Janko4.Model) (B : Subgroup Janko4.Model)
    (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup Janko4.Model) ≤ normalizer (B : Set Janko4.Model))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    ∃ z : Janko4.Model, orderOf z = 2 ∧
      B ⊔ (S : Subgroup Janko4.Model) ≤ centralizer ({z} : Set Janko4.Model) := by
  by_cases hc : pCore 2 B = ⊥
  · let e : B ≃* alternatingGroup (Fin 5) :=
      ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm.trans eB
    have hne : (S : Subgroup Janko4.Model) ⊓ centralizer (B : Set Janko4.Model) ≠ ⊥ := by
      intro hz
      let f := B.normalizerMonoidHom.comp (inclusion hn)
      have hf : Function.Injective f := by
        apply (MonoidHom.ker_eq_bot_iff _).mp
        apply eq_bot_iff.mpr
        intro a ha
        apply Subtype.ext
        apply mem_bot.mp
        rw [←hz]
        refine ⟨a.property,?_⟩
        change inclusion hn a ∈ B.normalizerMonoidHom.ker at ha
        rwa [normalizerMonoidHom_ker] at ha
      let a : Equiv.Perm (Fin 5) ≃* MulAut (alternatingGroup (Fin 5)) :=
        MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 5)))
          (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by decide) (by decide))
      let j := a.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp f)
      have hj : Function.Injective j := a.symm.injective.comp ((MulAut.congr e).injective.comp hf)
      have hd := card_dvd_of_injective j hj
      rw [Janko4.OuterReduction.OddIndex.ambient_sylow_card S,Nat.card_perm,Nat.card_fin] at hd
      norm_num [Nat.factorial] at hd
    have hp := S.isPGroup'.to_le
      (inf_le_left : (S : Subgroup Janko4.Model) ⊓ centralizer (B : Set Janko4.Model) ≤ S)
    have heven : 2 ∣ Nat.card (centralizer (B : Set Janko4.Model)) := by
      obtain ⟨n,hcard⟩ := hp.exists_card_eq
      have hn0 : n ≠ 0 := by
        intro hn0
        rw [hn0,pow_zero] at hcard
        exact hne (((S : Subgroup Janko4.Model) ⊓ centralizer (B : Set Janko4.Model)).eq_bot_of_card_eq hcard)
      exact (hcard ▸ dvd_pow_self 2 hn0).trans (card_dvd_of_le inf_le_right)
    exact exists_involution_centralizing_normalizing_two_group B (S : Subgroup Janko4.Model)
      S.isPGroup' hn heven
  · exact FiveLocalFF.JankoFour.involution_centralizer_placement_of_core S B hl hn eB hc

private theorem involution_mem_sylow_center {A : Type*} [Group A] [Finite A]
    (S : Sylow 2 A) (z : A) (hz : orderOf z = 2)
    (hc : (S : Subgroup A) ≤ centralizer ({z} : Set A)) :
    ∃ t : center S, (t.val.val : A) = z := by
  have hzn : z ∈ normalizer (S : Set A) := Subgroup.centralizer_le_normalizer _
    (fun x hx => mem_centralizer_singleton_iff.mp (hc hx))
  have hp : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,hz,pow_one])
  have hzs : z ∈ S := ((hp.inf_normalizer_sylow S).le ⟨mem_zpowers z,hzn⟩).2
  refine ⟨⟨⟨z,hzs⟩,?_⟩,rfl⟩
  apply mem_center_iff.mpr
  intro x
  exact Subtype.ext (mem_centralizer_singleton_iff.mp (hc x.property))


private theorem j4_local_five_pair_centralizes_involution (S : Sylow 2 Janko4.Model)
    (B C : Subgroup Janko4.Model)
    (hB : B ∈ localCComponents S) (hC : C ∈ localCComponents S)
    (hnB : (S : Subgroup Janko4.Model) ≤ normalizer (B : Set Janko4.Model))
    (hnC : (S : Subgroup Janko4.Model) ≤ normalizer (C : Set Janko4.Model))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (eC : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5)) : ∃ z : Janko4.Model, orderOf z = 2 ∧
      (B ⊔ C) ⊔ (S : Subgroup Janko4.Model) ≤ centralizer ({z} : Set Janko4.Model) := by
  obtain ⟨z,hz,hBz⟩ := j4_five_involution S B hB hnB eB
  obtain ⟨w,hw,hCw⟩ := j4_five_involution S C hC hnC eC
  obtain ⟨t,ht⟩ := involution_mem_sylow_center S z hz (le_sup_right.trans hBz)
  obtain ⟨u,hu⟩ := involution_mem_sylow_center S w hw (le_sup_right.trans hCw)
  have ht1 : t ≠ 1 := by
    intro he
    have hh : z = 1 := ht.symm.trans (congrArg (fun a : center S => (a.val.val : Janko4.Model)) he)
    rw [hh,orderOf_one] at hz
    norm_num at hz
  have hu1 : u ≠ 1 := by
    intro he
    have hh : w = 1 := hu.symm.trans (congrArg (fun a : center S => (a.val.val : Janko4.Model)) he)
    rw [hh,orderOf_one] at hw
    norm_num at hw
  have he : z = w := ht.symm.trans ((congrArg (fun a : center S => (a.val.val : Janko4.Model))
    (((Nat.card_eq_two_iff' (1 : center S)).mp (Janko4.sylow_center_card_two S)).unique ht1 hu1)).trans hu)
  exact ⟨z,hz,sup_le (sup_le (le_sup_left.trans hBz)
    (he.symm ▸ le_sup_left.trans hCw)) (le_sup_right.trans hBz)⟩

private theorem j4_local_five_pair_no_seven (S : Sylow 2 Janko4.Model)
    (B C : Subgroup Janko4.Model)
    (hB : B ∈ localCComponents S) (hC : C ∈ localCComponents S)
    (hnB : (S : Subgroup Janko4.Model) ≤ normalizer (B : Set Janko4.Model))
    (hnC : (S : Subgroup Janko4.Model) ≤ normalizer (C : Set Janko4.Model))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (eC : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5)) :
    ¬ 7 ∣ Nat.card (B ⊔ C : Subgroup Janko4.Model) := by
  obtain ⟨z,hz,hpair⟩ := j4_local_five_pair_centralizes_involution S B C hB hC hnB hnC eB eC
  let H := centralizer ({z} : Set Janko4.Model)
  have hBH : B ≤ H := le_sup_left.trans (le_sup_left.trans hpair)
  have hCH : C ≤ H := le_sup_right.trans (le_sup_left.trans hpair)
  have hSH : (S : Subgroup Janko4.Model) ≤ H := le_sup_right.trans hpair
  let b := subgroupOfEquivOfLe hBH
  let c := subgroupOfEquivOfLe hCH
  obtain ⟨f,hf,hs,hcop⟩ := centralizer_mathieuAction z hz
  let := hs
  have hno := no_seven_pair_mathieuAction (S.subtype hSH) (B.subgroupOf H) (C.subgroupOf H)
    (local_restrict hB hBH) (local_restrict hC hCH)
    (by rw [Sylow.coe_subtype,←subgroupOf_normalizer_eq hBH]; exact comap_mono hnB)
    (by rw [Sylow.coe_subtype,←subgroupOf_normalizer_eq hCH]; exact comap_mono hnC)
    ((QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans eB)
    ((QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans eC) f hf hcop
  rwa [←subgroupOf_sup hBH hCH,Nat.card_congr (subgroupOfEquivOfLe (sup_le hBH hCH)).toEquiv] at hno

/-- Both original normalized local sections exclude a J₄ overcomponent,
using the same full Sylow and the literal two-core quotient map. -/
theorem triangle_join_overcomponent_not_j4
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G) {B C J : Subgroup G}
    (hB : B ∈ localCComponents T) (hC : C ∈ localCComponents T)
    (hJ : J ∈ localCComponents T) (hBJ : B ≤ J) (hCJ : C ≤ J)
    (hnB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hnC : (T : Subgroup G) ≤ normalizer (C : Set G))
    (hmB : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4)
    (hmC : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 4)
    (hmI : Source.IsSL ((B ⊔ C : Subgroup G) ⧸ pCore 2 (B ⊔ C : Subgroup G)) 3 4 ∨
      Source.IsSp ((B ⊔ C : Subgroup G) ⧸ pCore 2 (B ⊔ C : Subgroup G)) 2 4 ∨
      ClassificationModels.IsG2At ((B ⊔ C : Subgroup G) ⧸ pCore 2 (B ⊔ C : Subgroup G)) 4) :
    ¬ Nonempty ((J ⧸ pCore 2 J) ≃* Janko4.Model) := by
  rintro ⟨e⟩
  have hIJ : B ⊔ C ≤ J := sup_le hBJ hCJ
  have hd := core_quotient_card_dvd hIJ
  rw [Nat.card_congr e.toEquiv,Janko4.Cardinality.model_card] at hd
  have hi : Nat.card ((B ⊔ C : Subgroup G) ⧸ pCore 2 (B ⊔ C : Subgroup G)) = 60480 := by
    rcases triangle_order hmI with hi | hi | hi
    · exact hi
    · rw [hi] at hd; norm_num at hd
    · rw [hi] at hd; norm_num at hd
  obtain ⟨S,hS,hBS⟩ := BinaryIntrinsic.local_in_local_overgroup T hB hJ hBJ
  have hCS : C.subgroupOf J ∈ localCComponents S := hS.symm ▸ local_restrict hC hCJ
  have hsB : (S : Subgroup J) ≤ normalizer (B.subgroupOf J : Set J) := by
    rw [hS,←subgroupOf_normalizer_eq hBJ]; exact comap_mono hnB
  have hsC : (S : Subgroup J) ≤ normalizer (C.subgroupOf J : Set J) := by
    rw [hS,←subgroupOf_normalizer_eq hCJ]; exact comap_mono hnC
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = pCore 2 J := by
    rw [MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective,QuotientGroup.ker_mk']
  let : Group.IsNilpotent q.ker := by rw [hker]; exact pCore_isNilpotent
  let : Group.IsSolvable q.ker := inferInstance
  let b := subgroupOfEquivOfLe hBJ
  let c := subgroupOfEquivOfLe hCJ
  obtain ⟨eb⟩ := section_map q (B.subgroupOf J) hBS
    ((QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans (five_equiv_maximal hmB).some)
  obtain ⟨ec⟩ := section_map q (C.subgroupOf J) hCS
    ((QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans (five_equiv_maximal hmC).some)
  have hn := j4_local_five_pair_no_seven (S.mapSurjective (f := q) hq)
    ((B.subgroupOf J).map q) ((C.subgroupOf J).map q)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hBS q)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hCS q)
    ((map_mono hsB).trans (le_normalizer_map q))
    ((map_mono hsC).trans (le_normalizer_map q)) eb ec
  have h7 : 7 ∣ Nat.card ((B ⊔ C).subgroupOf J) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hIJ).toEquiv]
    exact (hi ▸ (by decide : 7 ∣ 60480)).trans (card_quotient_dvd_card _)
  have h7q : 7 ∣ Nat.card (((B ⊔ C).subgroupOf J).map q) := by
    apply dvd_card_map_of_coprime_kernel q _ ?_ h7
    rw [hker]
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := J)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 7 2).pow_right n
  apply hn
  rwa [subgroupOf_sup hBJ hCJ,Subgroup.map_sup] at h7q

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
