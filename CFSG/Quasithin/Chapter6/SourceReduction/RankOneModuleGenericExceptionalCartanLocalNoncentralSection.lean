module
public import Theory.SpecificGroups.SL2.OddKernelCyclicActor
public import CFSG.Quasithin.ChapterA.Section01.RankActions.PerfectActions.LinearRecognition
public import Theory.GroupTheory.GeneralizedFitting.NilpotentComponentPreimage
public import Theory.GroupTheory.Involution.Counting
public import Theory.SpecificGroups.SL2.ResidualTwoExtension
public import Theory.GroupTheory.OddKernelInvolutionCentralizer
public import Theory.GroupTheory.NormalSylowQuotientAction
public import Theory.GroupTheory.GeneralizedFitting.ComponentFixedInvolution
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.CoreShapes.PrimaryShapes.FixedInvolution
public import Theory.GroupTheory.Fitting.PrimeSubgroups
public import Mathlib.GroupTheory.SpecificGroups.ZGroup
import all Theory.SpecificGroups.SL2.OddKernelCyclicActor

/-!
# The smaller SL₂ residual in a nonquasisimple Cartan container

The original residual embeds with odd solvable kernel in the prime-field
SL₂ quotient. Prime-field perfect-subgroup recognition and the intrinsic
quasisimple two-core quotient make its involution unique. It is the same
involution fixed by the cyclic actor and full Sylow in the containing group.
Their common centralizer is proper because the container has trivial two-core.

The earlier A.3.6 primary fixed-subgroup theorem makes the fixed Fitting
kernel cyclic, retaining every homocyclic exponent. The perfect residual
of the centralizer still surjects onto SL₂(p); its cyclic normal kernel is
central and prime-SL₂ cover rigidity removes it. The equivalence is the
restriction of the original quotient map, and the actual smaller residual
contains the original residual and is normalized by the original actor and
full Sylow. The companion NoncentralExclusion module uses this smaller
residual to exclude both rows; the binary-triality exclusion remains open.

The fixed-kernel assembly adapts the earlier-source argument also used in
Chapter10/SourceA5TensorExclusion/SourceOldResidualCartanNormalizationImage;
only the A.1.29, A.1.31 and A.3.6 ingredients are imported here.
Source: Aschbacher–Smith 5.1.13, printed p.636, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.PFAppendixIII
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve

open ChapterA.Section03.NoncentralFitting

private theorem fixed_centralizer_isCyclic
    {G : Type*} [Group G] [Finite G] {L : Subgroup G}
    {𝒦 : GroupClass} (hG : IsSQTK 𝒦 G) (hO : pCore 2 G = ⊥)
    (hL : L.IsCComponent) (hquot : PrimeSL2FittingQuotient L)
    (t : L) (ht : t ^ 2 = 1) (hnt : t ∉ fittingSubgroup L) :
    IsCyclic (fittingSubgroup L ⊓ centralizer ({t} : Set L) : Subgroup L) := by
  let C := fittingSubgroup L ⊓ centralizer ({t} : Set L)
  let : Group.IsNilpotent C := Subgroup.isNilpotent_of_ker_le_center
    (inclusion (show C ≤ fittingSubgroup L from inf_le_left))
    (by
      intro x hx
      have he : x = 1 := (inclusion_injective (show C ≤ fittingSubgroup L from inf_le_left)) hx
      rw [he]
      exact one_mem _)
  let : IsZGroup C := ⟨fun p hp S => by
    let : Fact p.Prime := ⟨hp⟩
    let P := (S : Subgroup C).map C.subtype
    have hPF : P ≤ fittingSubgroup L := (map_subtype_le _).trans inf_le_left
    have hPc : P ≤ centralizer ({t} : Set L) := (map_subtype_le _).trans inf_le_right
    have hP : IsPGroup p P := S.isPGroup'.map C.subtype
    have hcore : P ≤ pCore p L := hP.le_pCore_of_le_fitting hPF
    by_cases hd : p ∣ Nat.card (fittingSubgroup L)
    · let : IsCyclic (MulAut.conjNormal t : MulAut (pCore p L)).fixedSubgroup :=
        ChapterA.Section03.NoncentralFitting.CoreShapes.PrimaryShapes.primary_fixedSubgroup_isCyclic hG hO hL hquot t ht hnt p hd
      let f : P →* (MulAut.conjNormal t : MulAut (pCore p L)).fixedSubgroup :=
        { toFun := fun x => ⟨⟨x,hcore x.property⟩, by
            rw [MulAut.mem_fixedSubgroup]
            apply Subtype.ext
            change t * (x : L) * t⁻¹ = x
            rw [hPc x.property t (by simp), mul_inv_cancel_right]⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      let : IsCyclic P := isCyclic_of_injective f (fun x y h => Subtype.ext
        (congrArg (fun z : (MulAut.conjNormal t : MulAut (pCore p L)).fixedSubgroup => ((z : pCore p L) : L)) h))
      exact isCyclic_of_injective (C.subtype.subgroupMap (S : Subgroup C))
        (fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun z : P => (z : L)) h)))
    · have hbot : P = ⊥ := by
        apply Subgroup.card_eq_one.mp
        obtain ⟨n, hn⟩ := hP.exists_card_eq
        cases n with
        | zero => simpa using hn
        | succ n => exact (hd ((hn ▸ dvd_pow_self p (Nat.succ_ne_zero n)).trans
            (card_dvd_of_le hPF))).elim
      let : IsCyclic P := hbot ▸ inferInstanceAs (IsCyclic (⊥ : Subgroup L))
      exact isCyclic_of_injective (C.subtype.subgroupMap (S : Subgroup C))
        (fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun z : P => (z : L)) h)))⟩
  infer_instance


private theorem odd_sl2_section_quasisimple
    {R : Type*} [Group R] [Finite R] [Group.IsPerfect R]
    [IsQuasisimple (R ⧸ pCore 2 R)]
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (f : R →* SL(2,ZMod p)) [Group.IsSolvable f.ker]
    (ho : Odd (Nat.card f.ker)) :
    IsQuasisimple R ∧ 2 ∣ Nat.card R ∧
      (∀ x y : R, orderOf x = 2 → orderOf y = 2 → x = y) := by
  let : IsSimpleGroup ((R ⧸ pCore 2 R) ⧸ center (R ⧸ pCore 2 R)) := IsQuasisimple.simple
  let : Nontrivial (R ⧸ pCore 2 R) :=
    (QuotientGroup.mk'_surjective (center (R ⧸ pCore 2 R))).nontrivial
  let : Nontrivial R := (QuotientGroup.mk'_surjective (pCore 2 R)).nontrivial
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  let : Group.IsSolvable f.rangeRestrict.ker := by rwa [MonoidHom.ker_rangeRestrict]
  have hne : Nontrivial f.range := by
    by_contra! hn
    let : Subsingleton f.range := hn
    have he : f.ker = ⊤ := by
      apply top_unique
      intro x _
      exact congrArg (fun y : f.range => (y : SL(2,ZMod p)))
        (Subsingleton.elim (f.rangeRestrict x) 1)
    let : Group.IsSolvable (⊤ : Subgroup R) := he ▸ inferInstanceAs (Group.IsSolvable f.ker)
    exact Group.IsPerfect.not_isSolvable R
      (Group.isSolvable_of_surjective (f := (topEquiv (G := R)).toMonoidHom) topEquiv.surjective)
  let := hne
  obtain ⟨r,hr,hr3,⟨er⟩⟩ : ∃ r : ℕ, r.Prime ∧ 3 < r ∧ Nonempty (f.range ≃* SL(2,ZMod r)) := by
    rcases ChapterA.RankActions.primePerfectSL2Recognition p hp f.range inferInstance inferInstance
      with hh | ⟨_,hh⟩
    · exact ⟨p,Fact.out,hp,hh⟩
    · exact ⟨5,by decide,by decide,hh⟩
  let : Fact r.Prime := ⟨hr⟩
  let : IsQuasisimple f.range :=
    Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv (by simpa using hr3) er
  have hc : pCore 2 R ≤ center R := twoCore_central_of_odd_kernel f.rangeRestrict
    f.rangeRestrict_surjective (by rwa [MonoidHom.ker_rangeRestrict])
  let : IsQuasisimple R := (show PerfectCentralCovering.Cover R (R ⧸ pCore 2 R) from
    { toMonoidHom := QuotientGroup.mk' _, surjective := QuotientGroup.mk'_surjective _,
      isPerfect := inferInstance, ker_le_center := by rwa [QuotientGroup.ker_mk'] }).isQuasisimple
  have hk : f.ker ≤ center R :=
    (le_solvableRadical f.ker inferInstance inferInstance).trans IsQuasisimple.solvableRadical_le_center
  have heven : 2 ∣ Nat.card f.range := by
    rw [Nat.card_congr er.toEquiv]
    have hh := (GorensteinWalter.sl2ProjectiveProjection (ZMod r)).ker.card_subgroup_dvd_card
    rw [GorensteinWalter.sl2ProjectiveProjection_ker_card _
      (by simpa using hr.odd_of_ne_two (by omega))] at hh
    exact hh
  refine ⟨inferInstance,heven.trans (Subgroup.card_dvd_of_surjective f.rangeRestrict f.rangeRestrict_surjective),?_⟩
  intro x y hx hy
  have hxI : BenderSuzuki.PFAppendixIII.IsInvolution x := ⟨(orderOf_eq_prime_iff.mp hx).2,(orderOf_eq_prime_iff.mp hx).1⟩
  have hyI : BenderSuzuki.PFAppendixIII.IsInvolution y := ⟨(orderOf_eq_prime_iff.mp hy).2,(orderOf_eq_prime_iff.mp hy).1⟩
  have h2 := GorensteinWalter.two_ne_zero_of_odd_card (ZMod p)
    (by simpa using (Fact.out : p.Prime).odd_of_ne_two (by omega))
  apply involution_eq_of_central_odd_kernel f ho hk hxI hyI
  exact (Theory.SpecificGroups.SL2.OddKernel.sl2_involution_eq h2 (f x)
    (orderOf_eq_prime (involution_map_of_odd_kernel f ho hxI).2
      (involution_map_of_odd_kernel f ho hxI).1)).trans
    (Theory.SpecificGroups.SL2.OddKernel.sl2_involution_eq h2 (f y)
      (orderOf_eq_prime (involution_map_of_odd_kernel f ho hyI).2
        (involution_map_of_odd_kernel f ho hyI).1)).symm

/-- The original local residual and cyclic actor lie in a proper involution
centralizer of an odd-by-prime-SL₂ normal container. -/
theorem odd_sl2_normal_container_centralizer
    {Y : Type*} [Group Y] [Finite Y]
    (C R D : Subgroup Y) [C.Normal] [Group.IsPerfect C] [Group.IsPerfect R]
    [IsQuasisimple (R ⧸ pCore 2 R)] [IsCyclic D]
    (hRC : R ≤ C) (P : Sylow 2 Y)
    (hPR : (P : Subgroup Y) ≤ normalizer (R : Set Y))
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (f : C →* SL(2,ZMod p)) (hf : Function.Surjective f)
    [Group.IsSolvable f.ker] (hk : Odd (Nat.card f.ker))
    (hzero : pCore 2 C = ⊥) (hD : Odd (Nat.card D))
    (hperm : (D : Set Y) * (P : Set Y) = (P : Set Y) * (D : Set Y))
    (hs : Group.IsSolvable (D ⊔ (P : Subgroup Y) : Subgroup Y)) :
    ∃ z : C, orderOf z = 2 ∧ f z = -1 ∧
      (z : Y) ∈ R ∧ (z : Y) ∈ P ∧
      R ⊔ (D ⊔ (P : Subgroup Y)) ≤ centralizer ({(z : Y)} : Set Y) ∧
      C ⊓ centralizer ({(z : Y)} : Set Y) < C ∧
      Function.Surjective (f.comp (centralizer ({z} : Set C)).subtype) := by
  let j := inclusion hRC
  let r := f.comp j
  let : Group.IsSolvable r.ker := by
    change Group.IsSolvable (f.ker.comap j)
    apply Group.isSolvable_of_isSolvable_injective (f := j.subgroupComap f.ker)
    intro x y he
    exact Subtype.ext ((inclusion_injective hRC) (congrArg Subtype.val he))
  have hrOdd : Odd (Nat.card r.ker) :=
    hk.of_dvd_nat (card_comap_dvd_of_injective f.ker j (inclusion_injective hRC))
  obtain ⟨_,hrEven,huR⟩ := odd_sl2_section_quasisimple hp r hrOdd
  have ho : Odd (Nat.card (ZMod p)) := by
    simpa using (Fact.out : p.Prime).odd_of_ne_two (by omega)
  obtain ⟨z,hzP,hz,hfz,hfix⟩ := Theory.SpecificGroups.SL2.OddKernel.exists_actor_fixed_involution
    C D P f hf hk.coprime_two_left ho hD hperm hs
  obtain ⟨Q,hQ⟩ := NormalSylowQuotientAction.intersection_sylow P R hPR
  obtain ⟨w,hw⟩ := exists_prime_orderOf_dvd_card' (G := Q) 2 (Q.dvd_card_of_dvd_card hrEven)
  have hwY : orderOf (w.val : Y) = 2 := (orderOf_coe w.val).trans ((orderOf_coe w).trans hw)
  have hwP : (w.val : Y) ∈ P :=
    (congrArg (fun U : Subgroup R => w.val ∈ U) hQ).mp w.property
  obtain ⟨S,hS⟩ := P.exists_subgroupOf_eq_of_normal C
  have hzS : z ∈ S := (congrArg (fun U : Subgroup C => z ∈ U) hS).mpr hzP
  have hwS : j w.val ∈ S := (congrArg (fun U : Subgroup C => j w.val ∈ U) hS).mpr hwP
  have hu := (Theory.SpecificGroups.SL2.OddKernel.odd_sl2_sylow f hf hk.coprime_two_left ho S).2
  have he : (w.val : Y) = z := congrArg (fun v : S => (v.val : Y))
    (hu ⟨j w.val,hwS⟩ ⟨z,hzS⟩
      ((orderOf_coe _).symm.trans ((orderOf_injective j (inclusion_injective hRC) w.val).trans
        ((orderOf_coe w).trans hw))) ((orderOf_coe _).symm.trans hz))
  have hzR : (z : Y) ∈ R := he ▸ w.val.property
  have hzY : orderOf (z : Y) = 2 := (orderOf_coe z).trans hz
  have hRfix : R ≤ centralizer ({(z : Y)} : Set Y) := by
    intro x hx
    have hc : x * (z : Y) * x⁻¹ ∈ R := R.mul_mem (R.mul_mem hx hzR) (R.inv_mem hx)
    have hh := huR ⟨_,hc⟩ ⟨z,hzR⟩
      ((orderOf_coe _).symm.trans (((MulAut.conj x).orderOf_eq (z : Y)).trans hzY))
      ((orderOf_coe _).symm.trans hzY)
    exact mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hh))
  have hproper : C ⊓ centralizer ({(z : Y)} : Set Y) < C := by
    apply lt_of_le_of_ne inf_le_left
    intro heq
    have hzc : z ∈ center C := by
      apply mem_center_iff.mpr
      intro x
      apply Subtype.ext
      have hx : (x : Y) ∈ C ⊓ centralizer ({(z : Y)} : Set Y) := heq.symm ▸ x.property
      exact mem_centralizer_singleton_iff.mp hx.2
    let Z := zpowers z
    let : Z.Normal := ⟨by
      intro a ha b
      have hc := mem_center_iff.mp ((zpowers_le.mpr hzc) ha) b
      simpa only [hc, mul_inv_cancel_right] using ha⟩
    have hZp : IsPGroup 2 Z := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers,hz,pow_one])
    have hZ : Z ≤ pCore 2 C := le_sSup ⟨inferInstance,hZp⟩
    have hz1 : z = 1 := mem_bot.mp (hzero ▸ hZ (mem_zpowers z))
    simp [hz1] at hz
  refine ⟨z,hz,hfz,hzR,hzP,sup_le hRfix hfix,hproper,?_⟩
  intro x
  have hx : x ∈ centralizer ({f z} : Set SL(2,ZMod p)) := by
    rw [hfz,mem_centralizer_singleton_iff]
    simp
  obtain ⟨a,ha⟩ := f.elementCentralizerMap_surjective_of_odd_kernel hf hk.coprime_two_left z hz ⟨x,hx⟩
  exact ⟨a,congrArg Subtype.val ha⟩


/-- The smaller centralizer residual is identified by the original map,
and is normalized by the original actor and full Sylow subgroup. -/
theorem odd_sl2_normal_container_residual
    {Y : Type*} [Group Y] [Finite Y]
    {𝒦 : GroupClass} (hY : IsSQTK 𝒦 Y) (hYtwo : pCore 2 Y = ⊥)
    (C R D : Subgroup Y) [C.Normal] (hC : C.IsCComponent) [Group.IsPerfect R]
    [IsQuasisimple (R ⧸ pCore 2 R)] [IsCyclic D]
    (hRC : R ≤ C) (P : Sylow 2 Y)
    (hPR : (P : Subgroup Y) ≤ normalizer (R : Set Y))
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (f : C →* SL(2,ZMod p)) (hf : Function.Surjective f)
    (hk : f.ker = fittingSubgroup C) (ho : Odd (Nat.card f.ker))
    (hzero : pCore 2 C = ⊥) (hD : Odd (Nat.card D))
    (hperm : (D : Set Y) * (P : Set Y) = (P : Set Y) * (D : Set Y))
    (hs : Group.IsSolvable (D ⊔ (P : Subgroup Y) : Subgroup Y)) :
    ∃ z : C, orderOf z = 2 ∧ f z = -1 ∧ (z : Y) ∈ R ∧ (z : Y) ∈ P ∧
      R ⊔ (D ⊔ (P : Subgroup Y)) ≤ centralizer ({(z : Y)} : Set Y) ∧
      let J := centralizer ({z} : Set C)
      let K := (solvableResidual J).map J.subtype
      R ≤ K.map C.subtype ∧ K.map C.subtype < C ∧
      D ⊔ (P : Subgroup Y) ≤ normalizer (K.map C.subtype : Set Y) ∧
      ∃ e : K ≃* SL(2,ZMod p), ∀ x : K, e x = f x := by
  let : Group.IsPerfect C := hC.perfect
  let : Group.IsSolvable f.ker := by rw [hk]; infer_instance
  obtain ⟨z,hz,hfz,hzR,hzP,hfix,hproper,honto⟩ :=
    odd_sl2_normal_container_centralizer C R D hRC P hPR hp f hf ho hzero hD hperm hs
  let J := centralizer ({z} : Set C)
  let K := (solvableResidual J).map J.subtype
  let : Group.IsPerfect K := Group.IsPerfect.map J.subtype
  let : Group.IsPerfect SL(2,ZMod p) :=
    GorensteinWalter.sl2_isPerfect_of_card_gt_three (ZMod p) (by simpa using hp)
  have hquot : PrimeSL2FittingQuotient C :=
    ⟨p,Fact.out,hp,⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩⟩
  have hcyc : IsCyclic (f.ker ⊓ J : Subgroup C) := by
    rw [hk]
    apply fixed_centralizer_isCyclic hY hYtwo hC hquot z
      (hz ▸ pow_orderOf_eq_one z)
    intro hmem
    have hd := orderOf_dvd_natCard (⟨z,hk.symm ▸ hmem⟩ : f.ker)
    rw [←orderOf_coe (⟨z,hk.symm ▸ hmem⟩ : f.ker),hz] at hd
    exact ho.not_two_dvd_nat hd
  have hcent : (f.comp K.subtype).ker ≤ center K := by
    let := hcyc
    let i : (f.comp K.subtype).ker →* (f.ker ⊓ J : Subgroup C) :=
      { toFun x := ⟨x.val.val,x.property,map_subtype_le _ x.val.property⟩
        map_one' := rfl
        map_mul' _ _ := rfl }
    let : IsCyclic (f.comp K.subtype).ker := isCyclic_of_injective i (by
      intro x y he
      exact Subtype.ext (Subtype.ext
        (congrArg (fun v : (f.ker ⊓ J : Subgroup C) => (v : C)) he)))
    have hc := commutator_le_centralizer_of_isCyclic_normal (f.comp K.subtype).ker
    rw [Group.IsPerfect.commutator_eq_top] at hc
    intro x hx
    exact mem_center_iff.mpr (fun y => (hc (mem_top y) x hx).symm)
  have hsurj : Function.Surjective (f.comp K.subtype) := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp,range_subtype,map_map,
      map_solvableResidual_eq _ honto,solvableResidual_eq_top]
  have hbij : Function.Bijective (f.comp K.subtype) :=
    ⟨ChapterA.RankActions.primeSL2CoverRigidity p hp K (f.comp K.subtype) hsurj hcent,hsurj⟩
  have hRfix : R ≤ centralizer ({(z : Y)} : Set Y) := le_sup_left.trans hfix
  have hRJ : R.subgroupOf C ≤ J := by
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hRfix hx))
  let a := (subgroupOfEquivOfLe hRC).symm
  let : Group.IsPerfect (R.subgroupOf C) :=
    Group.IsPerfect.ofSurjective (f := a.toMonoidHom) a.surjective
  have hRK : R ≤ K.map C.subtype := by
    have hh := map_mono (f := C.subtype) (le_map_solvableResidual_of_isPerfect (R.subgroupOf C) J hRJ)
    rwa [map_subgroupOf_eq_of_le hRC] at hh
  have hKC : K.map C.subtype ≤ C ⊓ centralizer ({(z : Y)} : Set Y) := by
    rintro _ ⟨x,hx,rfl⟩
    refine ⟨x.property,mem_centralizer_singleton_iff.mpr ?_⟩
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp (map_subtype_le _ hx))
  have hn : D ⊔ (P : Subgroup Y) ≤ normalizer (K.map C.subtype : Set Y) := by
    have hh := centralizer_residual_image_normalized C.subtype C.subtype_injective z
    rw [range_subtype,←map_map] at hh
    exact (le_inf le_normalizer_of_normal (le_sup_right.trans hfix)).trans hh
  exact ⟨z,hz,hfz,hzR,hzP,hfix,hRK,lt_of_le_of_lt hKC hproper,hn,
    MulEquiv.ofBijective (f.comp K.subtype) hbij,fun _ => rfl⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
