module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry.SL3Core.Comparison
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoTerminal.Displacement

/-!
# Both original SL₃ flag radicals

The projective-action kernel on each local residual is a two-group: its
PSL₂ quotient is centerless. The native outer-extension calculation therefore
lifts to Rᵢ = O₂(Lᵢ)O₂(LT) at both flag indices, retaining the full SL₃ center.
In the actual J₁ escape configuration, the inner Sylow action on the local
PSL₂ quotient then gives T = T ∩ LO₂(LT). Every source Cartan consequently
normalizes T. These identities feed the terminal Cartan and displacement
arguments in SL3Cartan and SL3Terminal.

Source: Aschbacher--Smith 3.3.16, printed p.591; applied to 11.2.3,
printed pp.768--769.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Matrix Matrix.PSL3
open scoped MatrixGroups commutatorElement Pointwise
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.SL3Terminal
open PointCohomology.PointGeometry.SL3Core
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
  (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
  (a : SL(3, S.field.Carrier))

private theorem coreQuotient_center_eq_bot (flag : InvariantFlag (Coordinates.sl3 m)) (i : Fin 2) :
    center ((flag.Li i) ⧸ pCore 2 (flag.Li i)) = ⊥ := by
  apply (center _).eq_bot_iff_forall.mpr
  intro z hz
  apply (SL3.flagLocalCoreEquiv S m flag i).injective
  rw [map_one]
  apply mem_bot.mp
  rw [← Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot]
  apply mem_center_iff.mpr
  intro b
  obtain ⟨c,rfl⟩ := (SL3.flagLocalCoreEquiv S m flag i).surjective b
  simpa only [map_mul] using congrArg (SL3.flagLocalCoreEquiv S m flag i) (mem_center_iff.mp hz c)

/-- The projective kernel on the original Lᵢ is a two-group, since its
proved PSL₂ quotient is centerless. No centerlessness of the full SL₃ quotient is used. -/
private theorem component_kernel_le_core (flag : InvariantFlag (Coordinates.sl3 m)) (i : Fin 2)
    (k : (flag.Li i)) (hk : projectiveAction D S m a (inclusion (((localResidual_le _).trans inf_le_left).trans le_sup_left) k) = 1) :
    k ∈ pCore 2 (flag.Li i) := by
  apply (QuotientGroup.eq_one_iff k).mp
  apply mem_bot.mp
  rw [← coreQuotient_center_eq_bot D S m flag i]
  apply mem_center_iff.mpr
  intro x
  obtain ⟨j,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (flag.Li i)) x
  have hcomm : ⁅k,j⁆ ∈ pCore 2 (flag.Li i) := by
    have ha : (⁅k,j⁆ : (flag.Li i)).val ∈ (flag.Li i).pCoreIn 2 :=
      inf_pCoreIn_le_of_le 2 ((localResidual_le _).trans inf_le_left)
        ⟨(⁅k,j⁆ : (flag.Li i)).property,projectiveAction_kernel_commutator D S m a _ hk
          ⟨j,((localResidual_le _).trans inf_le_left) j.property⟩⟩
    obtain ⟨u,hu,he⟩ := ha
    exact (Subtype.ext he : u = ⁅k,j⁆) ▸ hu
  have he := (QuotientGroup.eq_one_iff (N := pCore 2 (flag.Li i)) ⁅k,j⁆).mpr hcomm
  change QuotientGroup.mk' (pCore 2 (flag.Li i)) ⁅k,j⁆ = 1 at he
  rw [map_commutatorElement] at he
  exact (commutatorElement_eq_one_iff_mul_comm.mp he).symm

/-- The original O₂(Lᵢ) maps onto the full core of the actual projective Lᵢ image. -/
private theorem closure_image_core (flag : InvariantFlag (Coordinates.sl3 m)) (i : Fin 2) :
    image D S m a ((flag.Li i).pCoreIn 2) = (image D S m a (flag.Li i)).pCoreIn 2 := by
  let M := L ⊔ (T : Subgroup G)
  let B := (flag.Li i).subgroupOf M
  let f := (projectiveAction D S m a).subgroupMap B
  have hk : f.ker ≤ pCore 2 B := by
    let e : B ≃* (flag.Li i) := subgroupOfEquivOfLe (((localResidual_le _).trans inf_le_left).trans le_sup_left)
    rw [← pCore_map_iso 2 e.symm]
    intro x hx
    refine ⟨e x,component_kernel_le_core D S m a flag i (e x) ?_,?_⟩
    · exact congrArg Subtype.val hx
    · exact e.symm_apply_apply x
  have he := f.comap_pCore_of_ker_isPGroup
    ((projectiveAction D S m a).subgroupMap_surjective B) (pCore_isPGroup.to_le hk)
  have hm : (pCore 2 B).map f = pCore 2 (image D S m a (flag.Li i)) := by
    rw [← he,map_comap_eq_self_of_surjective ((projectiveAction D S m a).subgroupMap_surjective B)]
    rfl
  have hh := congrArg (Subgroup.map (image D S m a (flag.Li i)).subtype) hm
  change ((pCore 2 B).map f).map (B.map (projectiveAction D S m a)).subtype =
    (B.map (projectiveAction D S m a)).pCoreIn 2 at hh
  rw [Subgroup.map_map] at hh
  change (pCore 2 B).map ((projectiveAction D S m a).comp B.subtype) = _ at hh
  rw [← Subgroup.map_map] at hh
  change ((((flag.Li i).pCoreIn 2).subgroupOf M).map (projectiveAction D S m a)) = _
  rw [← pCoreIn_subgroupOf 2 (flag.Li i) M (((localResidual_le _).trans inf_le_left).trans le_sup_left)]
  exact hh

private theorem image_residual (i : Fin 2) :
    image D S m (SL3.alignment D S m)⁻¹ ((SL3.flag D S m).Li i) =
      (LinearThree.OuterExtensions.localFactor S.field.Carrier (i == 0)).map MulAut.conj := by
  have hL : (SL3.flag D S m).Li i ≤ L := (localResidual_le _).trans inf_le_left
  rw [image_component D S m (SL3.alignment D S m)⁻¹ _ hL]
  have he : ((componentImage D S m ((SL3.flag D S m).Li i)).map
      (MulAut.conj (SL3.alignment D S m)⁻¹).toMonoidHom) =
        SL3.PlaneAction.localGroup (F := S.field.Carrier) i := by
    rw [componentImage, Subgroup.map_map]
    exact SL3.PlaneAction.local_image D S m i
  rw [he, ← Subgroup.map_map]
  congr 1
  fin_cases i <;> rfl

private theorem image_sup (A B : Subgroup G)
    (hA : A ≤ L ⊔ (T : Subgroup G)) (hB : B ≤ L ⊔ (T : Subgroup G)) :
    image D S m a (A ⊔ B) = image D S m a A ⊔ image D S m a B := by
  unfold image
  rw [subgroupOf_sup hA hB,Subgroup.map_sup]

private theorem preserves_of_normalizes_inner
    (U : Subgroup PSL(3,S.field.Carrier))
    (b : MulAut PSL(3,S.field.Carrier))
    (hb : b ∈ normalizer (U.map MulAut.conj : Set _)) : U.map b.toMonoidHom = U := by
  rw [mem_normalizer_iff_map_conj_eq] at hb
  have he : (MulAut.conj b : MulAut PSL(3,S.field.Carrier) →* _).comp MulAut.conj =
      MulAut.conj.comp b.toMonoidHom := by
    ext x y
    simp
  rw [Subgroup.map_map,he,←Subgroup.map_map] at hb
  exact map_injective (Matrix.PSL3.ExtensionBorel.inner_injective S.field.Carrier) hb

/-- The native outer-extension core calculation now applies to the original Rᵢ. -/
private theorem radical_image_le_closure (i : Fin 2) :
    image D S m (SL3.alignment D S m)⁻¹ ((SL3.flag D S m).Ri i) ≤ image D S m (SL3.alignment D S m)⁻¹ (((SL3.flag D S m).Li i).pCoreIn 2) := by
  have hKL' : ((SL3.flag D S m).Li i) ≤ L := (localResidual_le _).trans inf_le_left
  have hlocal : image D S m (SL3.alignment D S m)⁻¹ ((SL3.flag D S m).Li i) =
      (LinearThree.OuterExtensions.localFactor S.field.Carrier (i == 0)).map MulAut.conj := by
    exact image_residual D S m i
  have hn := image_normalizes D S m (SL3.alignment D S m)⁻¹ ((SL3.flag D S m).Li i) (T : Subgroup G) ((SL3.flag D S m).sylow_normalizes_Li i)
  rw [hlocal] at hn
  have hc := LinearThree.OuterExtensions.AmbientLocalCores.local_join_core_in_aut
    S.field.Carrier S.field.degree_pos S.field.card_eq (i == 0)
    (image D S m (SL3.alignment D S m)⁻¹ (T : Subgroup G)) (fun b hb => preserves_of_normalizes_inner D S _ b (hn hb))
  rw [closure_image_core D S m (SL3.alignment D S m)⁻¹ (SL3.flag D S m) i,hlocal]
  have hr : ((SL3.flag D S m).Ri i) = (((SL3.flag D S m).Li i) ⊔ (T : Subgroup G)).pCoreIn 2 := by rfl
  rw [hr]
  have hh := core_image_le D S m (SL3.alignment D S m)⁻¹ (((SL3.flag D S m).Li i) ⊔ (T : Subgroup G))
    (sup_le (hKL'.trans le_sup_left) le_sup_right)
  rw [image_sup D S m (SL3.alignment D S m)⁻¹ ((SL3.flag D S m).Li i) (T : Subgroup G) (hKL'.trans le_sup_left) le_sup_right,
    hlocal,hc] at hh
  exact hh

/-- Lift the actual projective image comparison through the original quotient kernel. -/
private theorem radical_le_closure_join_core (i : Fin 2) :
    ((SL3.flag D S m).Ri i) ≤ (((SL3.flag D S m).Li i).pCoreIn 2) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hi := radical_image_le_closure D S m i
  have hRT : ((SL3.flag D S m).Ri i) ≤ (T : Subgroup G) := by
    change ((SL3.flag D S m).Li i ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (((SL3.flag D S m).Li i) ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hWR : (((SL3.flag D S m).Li i).pCoreIn 2) ≤ ((SL3.flag D S m).Ri i) := by
    change ((SL3.flag D S m).Li i).pCoreIn 2 ≤ ((SL3.flag D S m).Li i ⊔ (T : Subgroup G)).pCoreIn 2
    exact pCoreIn_mono_of_normalizes le_sup_left
      (sup_le ((SL3.flag D S m).Li i).le_normalizer ((SL3.flag D S m).sylow_normalizes_Li i))
  intro r hr
  let r' : (L ⊔ (T : Subgroup G) : Subgroup G) := ⟨r,mem_sup_right (hRT hr)⟩
  obtain ⟨w,hw,he⟩ := hi ⟨r',hr,rfl⟩
  have hk : r' * w⁻¹ ∈ (projectiveAction D S m (SL3.alignment D S m)⁻¹).ker := by
    change projectiveAction D S m (SL3.alignment D S m)⁻¹ (r' * w⁻¹) = 1
    rw [map_mul,map_inv,he,mul_inv_cancel]
  have hd : r * (w : G)⁻¹ ∈ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    sylow_inf_projective_kernel_le_core D S m (SL3.alignment D S m)⁻¹
      ⟨(T : Subgroup G).mul_mem (hRT hr) ((T : Subgroup G).inv_mem (hRT (hWR hw))),
        r' * w⁻¹,hk,rfl⟩
  have hh := ((((SL3.flag D S m).Li i).pCoreIn 2) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2).mul_mem
    (mem_sup_right hd) (mem_sup_left hw)
  change r * (w : G)⁻¹ * (w : G) ∈ _ at hh
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh

/-- The original flag radical is the product of the local core and the global core,
including the full outer Sylow action. -/
theorem core_product (i : Fin 2) :
    (SL3.flag D S m).Ri i = ((SL3.flag D S m).Li i).pCoreIn 2 ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  apply le_antisymm (radical_le_closure_join_core D S m i)
  apply sup_le
  · exact pCoreIn_mono_of_normalizes le_sup_left
      (sup_le ((SL3.flag D S m).Li i).le_normalizer ((SL3.flag D S m).sylow_normalizes_Li i))
  · have hQT : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
      simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
        pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
    intro q hq
    exact inf_pCoreIn_le_of_le 2
      (sup_le (((localResidual_le _).trans inf_le_left).trans le_sup_left) le_sup_right)
      ⟨mem_sup_right (hQT hq),hq⟩

/-- The same equality for the literal supplied flag, at both indices. -/
theorem flag_core_product (f : InvariantFlag (Coordinates.sl3 m)) (i : Fin 2) :
    f.Ri i = (f.Li i).pCoreIn 2 ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hs : f.space = (SL3.flag D S m).space := funext fun j =>
    SL3.flag_unique D S m j (f.space j) (f.dimension j) (f.invariant j)
  have hinj : Function.Injective (InvariantFlag.space (c := Coordinates.sl3 m)) := by
    rintro ⟨s,ds,ns,is⟩ ⟨t,dt,nt,it⟩ h
    cases h
    rfl
  have he : f = SL3.flag D S m := hinj hs
  rw [he]
  exact core_product D S m i

/-- The inner local action in the J₁ configuration eliminates the outer Sylow factor. -/
theorem sourceTL_eq_sylow {f : InvariantFlag (Coordinates.sl3 m)}
    {A : OddSupplement T} (E : JankoConfiguration S f A) :
    sourceTL T L = (T : Subgroup G) := by
  apply le_antisymm inf_le_left
  have hL : f.Li E.index ≤ L := (localResidual_le _).trans inf_le_left
  have hR : f.Ri E.index ≤ L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
    rw [flag_core_product D S m f E.index]
    exact sup_le (((pCoreIn_le 2 (f.Li E.index)).trans hL).trans le_sup_left) le_sup_right
  exact le_inf le_rfl (E.sylow_eq_intersection_sup_radical.le.trans
    (sup_le ((inf_le_right.trans hL).trans le_sup_left) hR))

/-- Every original Cartan normalizes the full Sylow in this exceptional configuration. -/
theorem cartan_normalizes_sylow {f : InvariantFlag (Coordinates.sl3 m)}
    {A : OddSupplement T} (E : JankoConfiguration S f A)
    {X : Subgroup G} (hX : IsCartan T L X) :
    X ≤ normalizer (T : Set G) := by
  have h := hX.1.trans inf_le_right
  change X ≤ normalizer (sourceTL T L : Set G) at h
  rwa [sourceTL_eq_sylow D S m E] at h

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.SL3Terminal
