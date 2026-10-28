module

public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.CubicIdentification
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.CubicResidual.LocalControl
public import Theory.GroupTheory.GeneralizedFitting.ComponentCenterPrimeCore
public import Theory.GroupTheory.PerfectCentralQuotientNormalizer

/-!
# The full cubic residual on the original J₄ covering component

The simultaneous-centralizer M₂₂ seed supplements the two-core of its
normal component. The central two-core of its involution centralizer lets
Thompson's A×B lemma remove that supplement. The small centralizer of the
seed and its solvable outer action then identify the entire cubic
centralizer residual with the seed.

The identity lifts through the specified central covering map by prime-free
centralizer lifting and perfect-subgroup recovery across a central kernel.
In the original pushing-up configuration, the odd-core hypothesis supplies
the required coprimality. Thus the full residual in C_K(x) is quasisimple
with central quotient M₂₂ and is its only C-component. The literal Hall
application retains the full K, the original quotient map and both source
branches. Placement of x in the original intersection residual and the
ambient argument in C_G(x) remain separate source steps.

Source: Aschbacher--Smith 4.2.13, printed pp.611--612, used in 4.4.14,
printed pp.624--625. The distinct involution and fixed-line comparison is
4.4.3, printed p.623.
-/

public noncomputable section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter1.Section02.LocalModels Chapter4.Section02.RankOneReciprocalEscape
open Janko4 Janko4.InvolutionCentralizers
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares
open TwoCoreLinearModel First.QuotientExtension Sporadic.Mathieu
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
  involutionCentralizer involutionTwoCore
  actionGroup derivedGroup scalarUnit

private theorem outer_solvable_m22 {X : Type*} [Group X] [Group.IsPerfect X]
    (e : (X ⧸ center X) ≃* M22) : Group.IsSolvable (MulAut.Outer X) := by
  have hd := M22TripleCover.ScalarAutomorphisms.m22_outer_card_dvd_two
  have hp : IsPGroup 2 (MulAut.Outer M22) := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with he | he
    · exact IsPGroup.of_card (n := 0) he
    · exact IsPGroup.of_card (n := 1) he
  let : Group.IsNilpotent (MulAut.Outer M22) := hp.isNilpotent
  exact Group.isSolvable_of_isSolvable_injective (MulAut.centralQuotientOuter_injective e)

private def swapCentralizer (x : First.centralizer) :
    Subgroup.centralizer ({x} : Set First.centralizer) ≃*
      Subgroup.centralizer ({(⟨Janko4.a,mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp x.property).symm⟩ :
          Subgroup.centralizer ({(x : Janko4.Model)} : Set Janko4.Model))} :
            Set (Subgroup.centralizer ({(x : Janko4.Model)} : Set Janko4.Model))) where
  toFun y := ⟨⟨y.val.val,mem_centralizer_singleton_iff.mpr
    (congrArg First.centralizer.subtype (mem_centralizer_singleton_iff.mp y.property))⟩,
      mem_centralizer_singleton_iff.mpr (Subtype.ext (mem_centralizer_singleton_iff.mp y.val.property))⟩
  invFun y := ⟨⟨y.val.val,mem_centralizer_singleton_iff.mpr
    (congrArg (Subgroup.centralizer ({(x : Janko4.Model)} : Set Janko4.Model)).subtype
      (mem_centralizer_singleton_iff.mp y.property))⟩,
    mem_centralizer_singleton_iff.mpr (Subtype.ext (mem_centralizer_singleton_iff.mp y.val.property))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem cubic_threeCover {C : Type*} [Group C] [Finite C]
    (hC : IsSQTK KnownSimple.IsKnownSimple C)
    (Q : Subgroup C) [IsQuasisimple (Q ⧸ pCore 2 Q)]
    (c : Q) (hc : orderOf c = 3) (hz : c ∈ center Q) :
    ThreeCoverModel (Q ⧸ pCore 2 Q) := by
  let π := QuotientGroup.mk' (pCore 2 Q)
  have hπc : π c ∈ center (Q ⧸ pCore 2 Q) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 Q) y
    simpa only [map_mul] using congrArg π (mem_center_iff.mp hz y)
  have hcop : Nat.Coprime 3 (Nat.card π.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := Q)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hp : IsPGroup 3 (zpowers c) := IsPGroup.of_card (n := 1)
    (by simpa only [Nat.card_zpowers,pow_one] using hc)
  have hi := injective_comp_subtype_of_coprime_ker π hcop (zpowers c) hp
  have hπo : orderOf (π c) = 3 :=
    (orderOf_injective (π.comp (zpowers c).subtype) hi ⟨c,mem_zpowers c⟩).trans
      ((orderOf_coe (⟨c,mem_zpowers c⟩ : zpowers c)).symm.trans hc)
  have hc3 : orderOf (⟨π c,hπc⟩ : center (Q ⧸ pCore 2 Q)) = 3 :=
    (orderOf_coe _).symm.trans hπo
  have hsQ := hC.subgroup Q
  have hQsq : IsSQTK KnownSimple.IsKnownSimple (Q ⧸ pCore 2 Q) := by
    refine ⟨?_,hsQ.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hsQ.stronglyQuasithin p hp ho)
  exact threeCover_of_cubic_center hQsq (pCore_quotient_pCore_eq_bot 2) _ hc3

/-- The full cubic residual is the image of the simultaneous-centralizer seed. -/
theorem native_cubic_full_residual (x : First.centralizer) (hx : orderOf x = 3)
    (hxq : First.centralizerExtension.rightHom x = scalarElement)
    (hC : IsSQTK KnownSimple.IsKnownSimple
      (Subgroup.centralizer ({(x : Janko4.Model)} : Set Janko4.Model))) :
    solvableResidual (Subgroup.centralizer ({(x : Janko4.Model)} : Set Janko4.Model)) =
      (solvableResidual (Subgroup.centralizer ({x} : Set First.centralizer))).map
        (First.centralizer.subtype.elementCentralizerMap x) := by
  let D := Subgroup.centralizer ({x} : Set First.centralizer)
  let C := Subgroup.centralizer ({(x : Janko4.Model)} : Set Janko4.Model)
  let i : D →* C := First.centralizer.subtype.elementCentralizerMap x
  have hi : Function.Injective i := by
    intro a b hh
    exact Subtype.ext (Subtype.ext (congrArg (fun y : C => (y : Janko4.Model)) hh))
  let S := (solvableResidual D).map i
  obtain ⟨hS,⟨es⟩⟩ := First.CubicResidual.scalar_lift_residual_quasisimple x hx hxq
  let := hS
  let eS : (solvableResidual D) ≃* S := (solvableResidual D).equivMapOfInjective i hi
  let : IsQuasisimple S := IsQuasisimple.of_mulEquiv eS
  let es' : (S ⧸ center S) ≃* M22 := (centerQuotientCongr eS.symm).trans es
  obtain ⟨Q,⟨hQ,hSQ,hnQ,hqQ⟩,_⟩ :=
    quasisimple_seed_component hC es' S.subtype S.subtype_injective
  rw [range_subtype] at hSQ
  let := hnQ
  let := hqQ
  let := hQ.perfect
  let cx : C := ⟨x,mem_centralizer_singleton_iff.mpr rfl⟩
  have hcx : cx ∈ S := mem_map_of_mem i (First.CubicResidual.scalar_lift_mem_residual x hx hxq)
  let c : Q := ⟨cx,hSQ hcx⟩
  have hc : orderOf c = 3 := by
    rw [←orderOf_coe c,←orderOf_coe cx]
    exact (orderOf_coe x).trans hx
  have hz : c ∈ center Q := mem_center_iff.mpr (fun y =>
    Subtype.ext (Subtype.ext (mem_centralizer_singleton_iff.mp y.val.property)))
  have hmodel := cubic_threeCover hC Q c hc hz
  let j := inclusion hSQ
  have hm := cubic_component_twoCore_m22 es' j (inclusion_injective hSQ)
    (C.subtype.comp Q.subtype) (C.subtype_injective.comp Q.subtype_injective)
    ((QuotientGroup.quotientMulEquivOfEq Janko4.model_center_eq_bot).trans QuotientGroup.quotientBot)
    hmodel
  have hgen0 := m22_seed_covers_twoCore es' j (inclusion_injective hSQ) hm.2.2.some
  have hj : j.range.map Q.subtype = S := by
    rw [MonoidHom.map_range]
    change S.subtype.range = S
    exact range_subtype S
  have hgen := congrArg (map Q.subtype) hgen0
  rw [Subgroup.map_sup,hj,←MonoidHom.range_eq_map,range_subtype] at hgen
  let t : C := ⟨Janko4.a,mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp x.property).symm⟩
  let E := Subgroup.centralizer ({t} : Set C)
  let e : D ≃* E := swapCentralizer x
  have ht : orderOf t = 2 := (orderOf_coe t).symm.trans Janko4.orderOf_a
  have hSE : S ≤ E := by
    rintro y ⟨d,hd,rfl⟩
    exact (e d).property
  have hcore : pCore 2 E ≤ center E := by
    rw [←pCore_map_iso 2 e]
    rintro y ⟨d,hd,rfl⟩
    apply mem_center_iff.mpr
    intro z
    obtain ⟨z,rfl⟩ := e.surjective z
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using congrArg e
      (mem_center_iff.mp (First.CubicResidual.scalar_centralizer_core_central x hx hxq hd) z)
  let : Group.IsSolvable (MulAut.Outer S) := outer_solvable_m22 es'
  apply solvableResidual_eq_of_involution_seed t ht S Q hSE hgen hcore
  let Z := (Subgroup.centralizer (S : Set C)).subgroupOf E
  let f : Z →* Subgroup.centralizer (solvableResidual D : Set D) := {
    toFun y := ⟨e.symm y.val,by
      intro s hs
      apply hi
      exact y.property (i s) (mem_map_of_mem i hs)⟩
    map_one' := Subtype.ext (map_one e.symm)
    map_mul' a b := Subtype.ext (map_mul e.symm a.val b.val) }
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (e.symm.injective (congrArg Subtype.val hab))
  have hd := (card_dvd_of_injective f hf).trans
    (First.CubicResidual.scalar_centralizer_residual_centralizer_card x hx hxq)
  exact fun hfour => (by decide : ¬ 4 ∣ 6) (hfour.trans hd)


private theorem primeLift {U Y : Type*} [Group U] [Finite U] [Group Y]
    (f : U →* Y) (hf : Function.Surjective f)
    (hk : Nat.Coprime 3 (Nat.card f.ker)) (t : Y) (ht : orderOf t = 3) :
    ∃ x : U, orderOf x = 3 ∧ f x = t := by
  have hp : IsPGroup 3 (zpowers t) := IsPGroup.of_card (n := 1)
    (by simpa only [Nat.card_zpowers,pow_one] using ht)
  obtain ⟨A,hA,⟨e⟩⟩ := exists_prime_subgroup_equiv_of_surjective_coprime f hf hk (zpowers t) hp
  have hAp : IsPGroup 3 A := hp.of_equiv e.symm
  have hi := injective_comp_subtype_of_coprime_ker f hk A hAp
  obtain ⟨x,hx,hxt⟩ := hA.symm ▸ mem_zpowers t
  exact ⟨x,(orderOf_coe (⟨x,hx⟩ : A)).trans
    ((orderOf_injective (f.comp A.subtype) hi ⟨x,hx⟩).symm.trans (hxt ▸ ht)),hxt⟩

private theorem centralizerSurjective {U Y : Type*} [Group U] [Finite U] [Group Y]
    (f : U →* Y) (hf : Function.Surjective f)
    (hk : Nat.Coprime 3 (Nat.card f.ker)) (x : U) (hx : orderOf x = 3) :
    Function.Surjective (f.elementCentralizerMap x) := by
  have hp : IsPGroup 3 (zpowers x) := IsPGroup.of_card (n := 1)
    (by simpa only [Nat.card_zpowers,pow_one] using hx)
  have hh := centralizer_map_of_prime_free_kernel f hf
    (Nat.prime_three.coprime_iff_not_dvd.mp hk) (zpowers x) hp
  rw [MonoidHom.map_zpowers,zpowers_eq_closure,centralizer_closure,
    zpowers_eq_closure,centralizer_closure] at hh
  intro y
  have hy : (y : Y) ∈ (Subgroup.centralizer ({x} : Set U)).map f := by
    rw [hh]
    exact y.property
  obtain ⟨z,hz,hzy⟩ := hy
  exact ⟨⟨z,hz⟩,Subtype.ext hzy⟩

private def residualCover {U Y : Type*} [Group U] [Finite U] [Group Y]
    (f : U →* Y) (hf : Function.Surjective f) (hk : f.ker ≤ center U) :
    PerfectCentralCovering.Cover (solvableResidual U) (solvableResidual Y) where
  toMonoidHom := (MulEquiv.subgroupCongr (map_solvableResidual_eq f hf)).toMonoidHom.comp
    (f.subgroupMap (solvableResidual U))
  surjective := (MulEquiv.subgroupCongr (map_solvableResidual_eq f hf)).surjective.comp
    (f.subgroupMap_surjective _)
  isPerfect := inferInstance
  ker_le_center := by
    intro x hx
    have hfx : f (x : U) = 1 := congrArg (fun y : solvableResidual Y => (y : Y)) hx
    exact mem_center_iff.mpr (fun y => Subtype.ext (mem_center_iff.mp (hk hfx) y))

/-- Lift the full residual identity through the specified central covering map. -/
theorem cubic_full_residual_of_cover {U : Type*} [Group U] [Finite U]
    (f : U →* Janko4.Model) (hf : Function.Surjective f) (hk : f.ker ≤ center U)
    (hthree : Nat.Coprime 3 (Nat.card f.ker))
    (hmodel : IsSQTK KnownSimple.IsKnownSimple Janko4.Model) :
    let R := First.centralizer.comap f
    ∃ x : R, orderOf x = 3 ∧ orderOf (f (x : U)) = 3 ∧
      (⟨x,mem_centralizer_singleton_iff.mpr rfl⟩ : Subgroup.centralizer ({x} : Set R)) ∈
        solvableResidual (Subgroup.centralizer ({x} : Set R)) ∧
      solvableResidual (Subgroup.centralizer ({(x : U)} : Set U)) =
        (solvableResidual (Subgroup.centralizer ({x} : Set R))).map
          (R.subtype.elementCentralizerMap x) ∧
      IsQuasisimple (solvableResidual (Subgroup.centralizer ({(x : U)} : Set U))) ∧
      Nonempty (((solvableResidual (Subgroup.centralizer ({(x : U)} : Set U))) ⧸
        center (solvableResidual (Subgroup.centralizer ({(x : U)} : Set U)))) ≃* M22) := by
  let R := First.centralizer.comap f
  let q : R →* First.centralizer := f.subgroupComap First.centralizer
  have hq : Function.Surjective q := f.subgroupComap_surjective_of_surjective _ hf
  have hqker : Nat.Coprime 3 (Nat.card q.ker) := by
    let j : q.ker →* f.ker := {
      toFun x := ⟨x.val.val,congrArg First.centralizer.subtype x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    exact hthree.of_dvd_right (card_dvd_of_injective j
      (fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : f.ker => (z : U)) h))))
  obtain ⟨t,ht,hts⟩ := First.CubicResidual.exists_scalar_lift
  obtain ⟨x,hx,hxt⟩ := primeLift q hq hqker t ht
  let t' := q x
  have ht' : orderOf t' = 3 := (congrArg orderOf hxt).trans ht
  have hts' : First.centralizerExtension.rightHom t' = scalarElement :=
    (congrArg First.centralizerExtension.rightHom hxt).trans hts
  let C := Subgroup.centralizer ({(x : U)} : Set U)
  let D := Subgroup.centralizer ({x} : Set R)
  let C' := Subgroup.centralizer ({(t' : Janko4.Model)} : Set Janko4.Model)
  let D' := Subgroup.centralizer ({t'} : Set First.centralizer)
  let fc : C →* C' := f.elementCentralizerMap (x : U)
  let fd : D →* D' := q.elementCentralizerMap x
  have hfc : Function.Surjective fc := centralizerSurjective f hf hthree (x : U)
    ((orderOf_coe x).trans hx)
  have hfd : Function.Surjective fd := centralizerSurjective q hq hqker x hx
  have hkc : fc.ker ≤ center C := by
    intro y hy
    have hh : f (y : U) = 1 := congrArg C'.subtype hy
    exact mem_center_iff.mpr (fun z => Subtype.ext (mem_center_iff.mp (hk hh) z))
  have hkd : fd.ker ≤ center D := by
    intro y hy
    have hh : f (y.val : U) = 1 := congrArg (fun z : D' => (z.val : Janko4.Model)) hy
    exact mem_center_iff.mpr (fun z => Subtype.ext (Subtype.ext (mem_center_iff.mp (hk hh) z.val)))
  let i : D →* C := R.subtype.elementCentralizerMap x
  let i' : D' →* C' := First.centralizer.subtype.elementCentralizerMap t'
  have square : fc.comp i = i'.comp fd := by
    apply MonoidHom.ext
    intro y
    exact Subtype.ext rfl
  have he : solvableResidual C' = (solvableResidual D').map i' :=
    native_cubic_full_residual t' ht' hts' (hmodel.subgroup C')
  have hmap : ((solvableResidual D).map i).map fc = solvableResidual C' := by
    rw [map_map,square,←map_map,map_solvableResidual_eq fd hfd]
    exact he.symm
  let : Group.IsPerfect ((solvableResidual D).map i) := Group.IsPerfect.map i
  have hres : solvableResidual C = (solvableResidual D).map i := by
    apply le_antisymm _ (map_solvableResidual_le i)
    apply perfect_le_of_map_le_of_central_kernel fc hkc
    rw [map_solvableResidual_eq fc hfc,hmap]
  obtain ⟨hD',⟨eD'⟩⟩ := First.CubicResidual.scalar_lift_residual_quasisimple t' ht' hts'
  let := hD'
  have hC' : IsQuasisimple (solvableResidual C') := by
    rw [he]
    exact IsQuasisimple.of_mulEquiv ((solvableResidual D').equivMapOfInjective i'
      (fun a b hab => Subtype.ext (Subtype.ext
        (congrArg (fun y : C' => (y : Janko4.Model)) hab))))
  let := hC'
  let ec' : (solvableResidual C') ≃* (solvableResidual D') :=
    (MulEquiv.subgroupCongr he).trans
      ((solvableResidual D').equivMapOfInjective i'
        (fun a b hab => Subtype.ext (Subtype.ext
          (congrArg (fun y : C' => (y : Janko4.Model)) hab)))).symm
  let covC := residualCover fc hfc hkc
  have hdk : Nat.Coprime 3 (Nat.card fd.ker) := by
    let j : fd.ker →* q.ker := {
      toFun c := ⟨c.val.val,congrArg D'.subtype c.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    exact hqker.of_dvd_right (card_dvd_of_injective j
      (fun a b h => Subtype.ext (Subtype.ext (congrArg (fun z : q.ker => (z : R)) h))))
  have hxres := mem_solvableResidual_of_image_of_coprime_order fd hfd hdk
    (⟨x,mem_centralizer_singleton_iff.mpr rfl⟩ : D)
    ((orderOf_coe (⟨x,mem_centralizer_singleton_iff.mpr rfl⟩ : D)).symm.trans hx)
    (First.CubicResidual.scalar_lift_mem_residual t' ht' hts')
  exact ⟨x,hx,(orderOf_coe t').trans ht',hxres,hres,covC.isQuasisimple,
    ⟨covC.quotientCenterEquiv.trans ((centerQuotientCongr ec').trans eD')⟩⟩

private theorem sqtk_model_of_cover {K : Type*} [Group K] [Finite K]
    (hK : IsSQTK KnownSimple.IsKnownSimple K)
    (e : (K ⧸ center K) ≃* Janko4.Model) (hZ : IsPGroup 2 (center K)) :
    IsSQTK KnownSimple.IsKnownSimple Janko4.Model := by
  refine ⟨?_,?_⟩
  · intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    rw [←primeRank_equiv p e]
    exact (primeRank_quotient_le_of_isTwoGroup p ho (center K) hZ).trans
      (hK.stronglyQuasithin p hp ho)
  · intro Y _ hY U g hg
    let := hY
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let W := U.comap f
    let r := g.comp (f.subgroupComap U)
    have hr : Function.Surjective r := hg.comp (f.subgroupComap_surjective_of_surjective U
      (e.surjective.comp (QuotientGroup.mk'_surjective _)))
    let a := QuotientGroup.quotientKerEquivOfSurjective r hr
    let : IsSimpleGroup (W ⧸ r.ker) := a.isSimpleGroup
    exact (hK.isKGroup (W ⧸ r.ker) inferInstance W (QuotientGroup.mk' r.ker)
      (QuotientGroup.mk'_surjective _)).of_mulEquiv a.symm

open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape

/-- Identify the full cubic residual on the original full covering component,
with the literal simultaneous-centralizer inclusion. -/
theorem pushingUp_full_cubic_residual {G : Type*} [Group G] [Finite G]
    {L V A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hn : K.Normal) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model) :
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let R := First.centralizer.comap q
    ∃ x : R, orderOf x = 3 ∧ orderOf (q (x : K)) = 3 ∧
      (⟨x,mem_centralizer_singleton_iff.mpr rfl⟩ : Subgroup.centralizer ({x} : Set R)) ∈
        solvableResidual (Subgroup.centralizer ({x} : Set R)) ∧
      solvableResidual (Subgroup.centralizer ({(x : K)} : Set K)) =
        (solvableResidual (Subgroup.centralizer ({x} : Set R))).map
          (R.subtype.elementCentralizerMap x) ∧
      IsQuasisimple (solvableResidual (Subgroup.centralizer ({(x : K)} : Set K))) ∧
      Nonempty (((solvableResidual (Subgroup.centralizer ({(x : K)} : Set K))) ⧸
        center (solvableResidual (Subgroup.centralizer ({(x : K)} : Set K)))) ≃* M22) ∧
      ∀ Q : Subgroup (Subgroup.centralizer ({(x : K)} : Set K)), Q.IsCComponent →
        Q = solvableResidual (Subgroup.centralizer ({(x : K)} : Set K)) := by
  let := hn
  let := hK.2
  have hodd : pPrimeCore 2 H = ⊥ := hw.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hoddK := Subgroup.IsSubnormal.pPrimeCore_eq_bot hodd K hn.isSubnormal
  have hZ : IsPGroup 2 (center K) := by
    rw [IsQuasisimple.center_eq_pCore hoddK]
    exact pCore_isPGroup
  have hs := sqtk_model_of_cover (hw.2.2.2.2.2.2.1.sqtk.subgroup K) e hZ
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hk : q.ker = center K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  obtain ⟨x,hx,hqx,hmem,he,hquasi,heq⟩ := cubic_full_residual_of_cover q
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) hk.le
    (hk.symm ▸ pushingUp_component_center_three_coprime hw K) hs
  refine ⟨x,hx,hqx,hmem,he,hquasi,heq,?_⟩
  intro Q hQ
  let := hQ.perfect
  have hr : (solvableResidual (Subgroup.centralizer ({(x : K)} : Set K))).IsCComponent :=
    (show IsComponent _ _ from ⟨(inferInstance :
      (solvableResidual (Subgroup.centralizer ({(x : K)} : Set K))).Normal).isSubnormal,
      hquasi⟩).isCComponent
  exact hQ.eq_of_le hr (le_solvableResidual_of_isPerfect Q)

/-- The original pushing-up witnesses with the full cubic residual identified.
This does not yet place the cubic in the original intersection residual. -/
@[expose] def MathieuPushingUpFullCubicCase {G : Type*} [Group G] [Finite G]
    (L V A : Subgroup G) : Prop :=
  ∃ J H W : Subgroup G, Witness L V A J H W ∧
    ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ (normalizer (L : Set G)).subgroupOf H ∧
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
      ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
      F.subgroupOf H ≤ K ∧ W.subgroupOf H ≤ K ∧
      H = K.map H.subtype ⊔ (H ⊓ centralizer (K.map H.subtype : Set G)) ∧
      ∃ e : (K ⧸ center K) ≃* Janko4.Model,
        let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
        let R := First.centralizer.comap q
        ∃ x : R, orderOf x = 3 ∧ orderOf (q (x : K)) = 3 ∧
          (⟨x,mem_centralizer_singleton_iff.mpr rfl⟩ : Subgroup.centralizer ({x} : Set R)) ∈
            solvableResidual (Subgroup.centralizer ({x} : Set R)) ∧
          solvableResidual (Subgroup.centralizer ({(x : K)} : Set K)) =
            (solvableResidual (Subgroup.centralizer ({x} : Set R))).map
              (R.subtype.elementCentralizerMap x) ∧
          IsQuasisimple (solvableResidual (Subgroup.centralizer ({(x : K)} : Set K))) ∧
          Nonempty (((solvableResidual (Subgroup.centralizer ({(x : K)} : Set K))) ⧸
            center (solvableResidual (Subgroup.centralizer ({(x : K)} : Set K)))) ≃* M22) ∧
          ∀ Q : Subgroup (Subgroup.centralizer ({(x : K)} : Set K)), Q.IsCComponent →
            Q = solvableResidual (Subgroup.centralizer ({(x : K)} : Set K))

/-- The full centralizer identity uses the same cover and ambient factorization. -/
theorem mathieu_pushingUp_full_cubic {G : Type*} [Group G] [Finite G]
    {L V A : Subgroup G} (h : MathieuPushingUpJankoInnerCase L V A) :
    MathieuPushingUpFullCubicCase L V A := by
  obtain ⟨J,H,W,hw,hf,K,hK,hn,hout,hF,hW,⟨e⟩,hprod⟩ := h
  exact ⟨J,H,W,hw,hf,K,hK,hn,hout,hF,hW,hprod,e,pushingUp_full_cubic_residual hw K hn hK e⟩

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Representation.BinaryOffender
open scoped Pointwise
universe u
variable {G : Type u} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

set_option maxHeartbeats 400000 in
/-- The literal Hall obstruction identifies the entire cubic centralizer
residual on the original full J₄ cover and proves uniqueness of its
C-component. The original intersection placement and ambient pushing-up
exclusion remain to be proved. -/
theorem sourceOrbit_mathieu_hall_full_cubic_obstruction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G))) (hlarge : 1 < ChapterE.generationParameter H)
    (B : Subgroup H) (hBN : B ≤ (normalizer (L : Set G)).subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes
      (B.subgroupOf ((normalizer (L : Set G)).subgroupOf H)))
    (hker : B.map H.subtype ⊓ sectionCentralizer L ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧ A ≤ H ∧ A ≤ sectionCentralizer L ∧
      A ≤ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ normalizer (L : Set G)) ∧
      (∀ Q : Subgroup G, (T : Subgroup G) ≤ normalizer (Q : Set G) →
        A ≤ sectionCentralizer Q → Q ≤ normalizer (L : Set G)) ∧
      (MathieuPushingUpFullCubicCase L V A ∨
        (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
          MathieuJankoSeedResidualCase (T : Subgroup G) L V A
            (D.orbitComponent ⧸ center D.orbitComponent))) := by
  obtain ⟨p,A,hp,ho,hne,he,hAH,hAC,hAV,hAT,hout,hclosure,hcompare,hcase⟩ :=
    @sourceOrbit_mathieu_hall_seed_obstruction G instG finG T L V D
      h hmany hV hm hnon H hH hlarge B hBN hHall hker
  exact ⟨p,A,hp,ho,hne,he,hAH,hAC,hAV,hAT,hout,hclosure,hcompare,
    hcase.imp mathieu_pushingUp_full_cubic id⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
