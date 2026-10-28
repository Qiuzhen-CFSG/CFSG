module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.CubicSylowQuotient
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.LargeAbelianImage
public import Theory.ElementaryAbelian.PrimeRankCard
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction

/-!
# The original module survives in the cubic native action

Restrict the containing component's actual action to the original full
involution centralizer. Its full residual has the already identified
quasisimple cubic image. The first-centralizer extraspecial bound then
prevents the original Mathieu module, of binary rank at least ten, from
vanishing under that action.

The module image is a nontrivial normal subgroup of the original native
Sylow and is centralized by the actor. It therefore meets the Sylow center,
whose order is two, in an involution fixed by both groups. This uses the
ambient source module and avoids the false implication from cubic--Sylow
permutation alone.

The Hall consumer preserves both full covering components, the original
involution and seed maps, the replacement product and its inclusion-induced
quotient marking. The new common fixed involution is not yet identified
with the replacement's selected involution. That comparison, the M₁₂/M₂₂
pushing-up branches, M₂₄ fixed line, seed generation and separate odd-normalizer
assembly remain required for SourceMathieuHallFaithfulAt.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 4.4.3,
printed p.623, used in 4.4.14, pp.624--625; GLS3 Table 5.3i.
The imported native certificates retain their ATLAS attribution and licenses.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4.Section04.OddLocalMathieu
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private theorem cubic_fixed_seed_isQuasisimple
    {S : Type*} [Group S] [Finite S]
    (hS : IsSQTK KnownSimple.IsKnownSimple S)
    (e : S ≃* Janko4.Model) (b : MulAut S)
    (U : Subgroup S)
    (hU : U = (solvableResidual b.fixedSubgroup).map b.fixedSubgroup.subtype)
    (y : center U) (hy : orderOf y = 3)
    (he : MulAut.conj ((y : U) : S) = b) : IsQuasisimple U := by
  let v : S := y.val.val
  have hv : orderOf (e v) = 3 := by
    rw [e.orderOf_eq]
    exact (orderOf_coe y.val).trans ((orderOf_coe y).trans hy)
  have hJ : IsSQTK KnownSimple.IsKnownSimple Janko4.Model := by
    refine ⟨?_,?_⟩
    · intro p hp ho
      rw [←primeRank_equiv p e]
      exact hS.stronglyQuasithin p hp ho
    · intro Y _ hY W g hg
      let := hY
      let W' := W.comap e.toMonoidHom
      let r := g.comp (e.toMonoidHom.subgroupComap W)
      have hr : Function.Surjective r := hg.comp
        (e.toMonoidHom.subgroupComap_surjective_of_surjective W e.surjective)
      let a := QuotientGroup.quotientKerEquivOfSurjective r hr
      let : IsSimpleGroup (W' ⧸ r.ker) := a.isSimpleGroup
      exact (hS.isKGroup (W' ⧸ r.ker) inferInstance W' (QuotientGroup.mk' r.ker)
        (QuotientGroup.mk'_surjective _)).of_mulEquiv a.symm
  let := (janko_cubic_residual_at hJ (e v) hv).1
  have hm : b.fixedSubgroup.map e.toMonoidHom = centralizer ({e v} : Set Janko4.Model) := by
    rw [←he,MulAut.fixedSubgroup_conj,map_centralizer_equiv,Set.image_singleton]
  let c := (e.subgroupMap b.fixedSubgroup).trans (MulEquiv.subgroupCongr hm)
  let r := c.solvableResidualEquiv.symm
  let d := ((solvableResidual b.fixedSubgroup).equivMapOfInjective
    b.fixedSubgroup.subtype b.fixedSubgroup.subtype_injective).trans
      (MulEquiv.subgroupCongr hU.symm)
  exact IsQuasisimple.of_mulEquiv (r.trans d)

namespace JankoNormalizerAction
variable {N : Type*} [Group N] [Finite N] {K : Subgroup N}
    (a : JankoNormalizerAction K) [IsQuasisimple K]

include a in
/-- Transport the native large-subgroup bound through the original covering component. -/
theorem large_first_centralizer_image
    (z : K) (hz : orderOf z = 2)
    (e : (centralizer ({z} : Set K) ⧸ pPrimeCore 2 (centralizer ({z} : Set K))) ≃*
      Janko4.InvolutionCentralizers.First.centralizer)
    {Y : Type*} [Group Y] (f : centralizer ({z} : Set K) →* Y)
    [IsQuasisimple ((solvableResidual (centralizer ({z} : Set K))).map f)]
    (W : Subgroup (centralizer ({z} : Set K))) [IsElementaryAbelian 2 W]
    (hW : 256 < Nat.card W) : W.map f ≠ ⊥ := by
  let C := centralizer ({z} : Set K)
  let d : C ≃* Janko4.InvolutionCentralizers.First.centralizer :=
    QuotientGroup.quotientBot.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (a.involution_oddCore_eq_bot z hz).symm).trans e)
  let g := f.comp d.symm.toMonoidHom
  have hm : (solvableResidual Janko4.InvolutionCentralizers.First.centralizer).map g =
      (solvableResidual C).map f := by
    rw [←map_map,map_solvableResidual_eq d.symm.toMonoidHom d.symm.surjective]
  let : IsQuasisimple ((solvableResidual Janko4.InvolutionCentralizers.First.centralizer).map g) :=
    hm.symm ▸ inferInstance
  let E := W.map d.toMonoidHom
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map d.toMonoidHom
  have hE : 256 < Nat.card E := by rwa [card_map_of_injective d.injective]
  have hh := Janko4.InvolutionCentralizers.First.large_abelian_image_ne_bot_of_quasisimple_residual
    g E (IsElementaryAbelian.isPGroup 2 E) hE
  have he : E.map g = W.map f := by
    rw [map_map]
    congr 1
    ext w
    exact congrArg f (d.symm_apply_apply w)
  rwa [he] at hh
end JankoNormalizerAction
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 OddLocalMathieu
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V A : Subgroup G}
    (D : ChosenModule T L V)
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- The literal containing-component action cannot kill the original Mathieu module. -/
theorem original_cubic_module_image_ne_bot
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : V = D.sourceOrbit) (hm : HasMathieuCentralQuotient D.orbitComponent)
    (K : Subgroup (normalizer (A : Set G))) [IsQuasisimple K]
    (a : JankoNormalizerAction K)
    (hVK : V ≤ K.map (normalizer (A : Set G)).subtype)
    (z : K) (hzV : ((z : normalizer (A : Set G)) : G) ∈ V) (hz : orderOf z = 2)
    (ef : (centralizer ({z} : Set K) ⧸ pPrimeCore 2 (centralizer ({z} : Set K))) ≃*
      Janko4.InvolutionCentralizers.First.centralizer)
    (P : Subgroup (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) ⊓
      centralizer (A : Set G) : Subgroup G))
    (hPm : P.map (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) ⊓
      centralizer (A : Set G)).subtype =
        ((solvableResidual (centralizer ({z} : Set K))).map
          (centralizer ({z} : Set K)).subtype).map
            ((normalizer (A : Set G)).subtype.comp K.subtype))
    (Q : Subgroup (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G))) [Q.Normal] [IsQuasisimple (Q ⧸ pCore 2 Q)]
    (hPQ : P.map (inclusion inf_le_left) ≤ Q)
    (e : SimpleSection Q ≃* Janko4.Model)
    (b : MulAut (SimpleSection Q))
    (hU : ((projection Q).comp (seedInclusion inf_le_left hPQ)).range =
      (solvableResidual b.fixedSubgroup).map b.fixedSubgroup.subtype)
    (y : center (((projection Q).comp (seedInclusion inf_le_left hPQ)).range))
    (hy : orderOf y = 3)
    (he : MulAut.conj ((y : ((projection Q).comp (seedInclusion inf_le_left hPQ)).range) :
      SimpleSection Q) = b) :
    (V.subgroupOf (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G))).map
      (cubicNativeAction Q e) ≠ ⊥ := by
  let := D.elementary
  let zG : G := ((z : normalizer (A : Set G)) : G)
  let C := centralizer ({zG} : Set G)
  let Ck := centralizer ({z} : Set K)
  let E := C ⊓ centralizer (A : Set G)
  let j := (normalizer (A : Set G)).subtype.comp K.subtype
  have hj : Function.Injective j := (normalizer (A : Set G)).subtype_injective.comp K.subtype_injective
  let i : Ck →* C :=
    { toFun := fun c => ⟨j c,mem_centralizer_singleton_iff.mpr
        (congrArg j (mem_centralizer_singleton_iff.mp c.property))⟩
      map_one' := Subtype.ext (map_one j)
      map_mul' := fun _ _ => Subtype.ext (map_mul j _ _) }
  let k := C.subtype.comp i
  have hki : Function.Injective k := hj.comp Ck.subtype_injective
  have hVr : V ≤ k.range := by
    intro v hv
    obtain ⟨u,hu,rfl⟩ := hVK hv
    let w : K := ⟨u,hu⟩
    have hw : w ∈ Ck := by
      apply mem_centralizer_singleton_iff.mpr
      apply hj
      change (u : G) * zG = zG * (u : G)
      exact setLike_mul_comm hv hzV
    exact ⟨⟨w,hw⟩,rfl⟩
  let W := V.comap k
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_injective
    (k.subgroupComap V) (fun x y he => Subtype.ext (hki (congrArg (fun v : V => (v : G)) he)))
  have hWcard : Nat.card W = Nat.card V := by
    let d := (W.equivMapOfInjective k hki).trans (MulEquiv.subgroupCongr (map_comap_eq_self hVr))
    exact Nat.card_congr d.toEquiv
  have hWlarge : 256 < Nat.card W := by
    rw [hWcard,IsElementaryAbelian.card_eq_pow_primeRank (p := 2) V]
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (D.sourceOrbit_mathieu_twoRank_ge_ten hV hm)
    norm_num at hh
    omega
  have hzG : orderOf zG = 2 := by rw [orderOf_coe,orderOf_coe]; exact hz
  have hz1 : zG ≠ 1 := by intro he; rw [he,orderOf_one] at hzG; omega
  have hC : IsSQTK KnownSimple.IsKnownSimple C := by
    apply h.simpleQTKE.twoLocal_sqtk
    refine ⟨zpowers zG,fun hb => hz1 (mem_bot.mp (hb ▸ mem_zpowers _)),?_,
      (normalizer_zpowers_eq_centralizer_of_order_two _ hzG).symm⟩
    exact IsPGroup.of_card (show Nat.card (zpowers zG) = 2^1 by
      rw [Nat.card_zpowers,hzG]; rfl)
  let f := (projection Q).comp (seedInclusion inf_le_left hPQ)
  let := cubic_fixed_seed_isQuasisimple (simpleSection_sqtk (hC.subgroup Q)) e b f.range hU y hy he
  let q := cubicNativeAction Q e
  have hres : (solvableResidual Ck).map i = P.map (inclusion inf_le_left) := by
    apply (map_injective (f := C.subtype) C.subtype_injective)
    rw [map_map,map_map]
    have hi : C.subtype.comp i = j.comp Ck.subtype := by ext c; rfl
    have hjP : C.subtype.comp (inclusion (show E ≤ C from inf_le_left)) = E.subtype := by
      ext p; rfl
    rw [hi,hjP]
    simpa only [map_map] using hPm.symm
  have hcomp : (q.comp (inclusion inf_le_left)).comp P.subtype = e.toMonoidHom.comp f := by
    ext p
    exact DFunLike.congr_fun (cubicNativeAction_component Q e) (seedInclusion inf_le_left hPQ p)
  have hresq : (solvableResidual Ck).map (q.comp i) = f.range.map e.toMonoidHom := by
    rw [←map_map,hres,map_map,←MonoidHom.range_comp,←hcomp]
    rw [MonoidHom.range_comp,range_subtype]
  let : IsQuasisimple (f.range.map e.toMonoidHom) :=
    IsQuasisimple.of_mulEquiv (e.subgroupMap f.range)
  let : IsQuasisimple ((solvableResidual Ck).map (q.comp i)) := hresq.symm ▸ inferInstance
  have hn := a.large_first_centralizer_image z hz ef (q.comp i) W hWlarge
  intro hzero
  apply hn
  apply bot_unique
  rw [←map_map]
  have hW : W.map i ≤ V.subgroupOf C := by
    rintro _ ⟨w,hw,rfl⟩
    exact hw
  exact (map_mono hW).trans_eq hzero
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4.Section04.OddLocalMathieu
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- The same marked quotient, with nontrivial original module image and a common fixed involution. -/
@[expose] def CubicModuleImageAt {G : Type*} [Group G]
    (T C V A : Subgroup G) (Q : Subgroup C) [Q.Normal]
    (e : SimpleSection Q ≃* Janko4.Model) : Prop :=
  CubicSylowQuotientAt T C A Q e ∧
    let q := cubicNativeAction Q e
    let W := (V.subgroupOf C).map q
    let S := (T.subgroupOf C).map q
    let B := (A.subgroupOf C).map q
    W ≠ ⊥ ∧ W ≤ S ∧ S ≤ normalizer (W : Set Janko4.Model) ∧
      B ≤ centralizer (W : Set Janko4.Model) ∧
      ∃ s : Janko4.Model, orderOf s = 2 ∧ s ∈ W ∧
        S ⊔ B ≤ centralizer ({s} : Set Janko4.Model)

/-- Normality of the surviving module forces a Sylow-central involution fixed by the actor. -/
theorem cubic_module_image_of_nonzero {G : Type*} [Group G]
    {T C V A : Subgroup G} {Q : Subgroup C} [Q.Normal]
    {e : SimpleSection Q ≃* Janko4.Model}
    (h : CubicSylowQuotientAt T C A Q e)
    (hnon : (V.subgroupOf C).map (cubicNativeAction Q e) ≠ ⊥)
    (hVT : V ≤ T) (hTV : T ≤ normalizer (V : Set G))
    (hAV : A ≤ centralizer (V : Set G)) : CubicModuleImageAt T C V A Q e := by
  let q := cubicNativeAction Q e
  let W := (V.subgroupOf C).map q
  let B := (A.subgroupOf C).map q
  have hsave := h
  obtain ⟨S,hS,_,_,_,_,hZ,_⟩ := h
  have hWS : W ≤ (S : Subgroup Janko4.Model) := by
    rw [hS]
    exact map_mono (comap_mono hVT)
  have hSW : (S : Subgroup Janko4.Model) ≤ normalizer (W : Set Janko4.Model) := by
    rw [hS]
    exact (map_mono ((comap_mono hTV).trans (V.le_normalizer_comap C.subtype))).trans
      ((V.subgroupOf C).le_normalizer_map q)
  have hBW : B ≤ centralizer (W : Set Janko4.Model) := by
    rintro _ ⟨a,ha,rfl⟩ _ ⟨v,hv,rfl⟩
    exact (map_mul q v a).symm.trans
      ((congrArg q (Subtype.ext (hAV ha v hv))).trans (map_mul q a v))
  let U := W.subgroupOf (S : Subgroup Janko4.Model)
  let : U.Normal := (normal_subgroupOf_iff_le_normalizer hWS).mpr hSW
  have hUn : U ≠ ⊥ := by
    intro he
    apply hnon
    have hh := congrArg (map (S : Subgroup Janko4.Model).subtype) he
    rwa [map_subgroupOf_eq_of_le hWS,Subgroup.map_bot] at hh
  have hmeet := center_inf_ne_bot_of_normal S.isPGroup' U hUn
  let : Nontrivial (center S ⊓ U : Subgroup S) := (nontrivial_iff_ne_bot _).mpr hmeet
  obtain ⟨v,hv⟩ := exists_ne (1 : (center S ⊓ U : Subgroup S))
  let s : S := v.val
  have hs : s ∈ center S ⊓ U := v.property
  have hsne : s ≠ 1 := fun hh => hv (Subtype.ext hh)
  let z : center S := ⟨s,hs.1⟩
  have hz : orderOf z = 2 := by
    have hd := orderOf_dvd_natCard z
    rw [hZ] at hd
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with hh | hh
    · exact (hsne (congrArg Subtype.val (orderOf_eq_one_iff.mp hh))).elim
    · exact hh
  have hsc : (S : Subgroup Janko4.Model) ≤ centralizer ({(s : Janko4.Model)} : Set Janko4.Model) := by
    intro u hu
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mem_center_iff.mp hs.1 (⟨u,hu⟩ : S))
  have hbc : B ≤ centralizer ({(s : Janko4.Model)} : Set Janko4.Model) := by
    intro u hu
    exact mem_centralizer_singleton_iff.mpr ((hBW hu) s hs.2).symm
  refine ⟨hsave,hnon,?_,?_,hBW,s,?_,hs.2,?_⟩
  · rwa [←hS]
  · rwa [←hS]
  · exact (orderOf_coe s).trans ((orderOf_coe z).trans hz)
  · rw [←hS]
    exact sup_le hsc hbc
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Sporadic.Mathieu
/-- All original cubic witnesses, with nontrivial module image and a native central involution fixed by the actor and Sylow. -/
@[expose] def MathieuJankoCubicModuleCase {G : Type*} [Group G]
    (T L V A : Subgroup G) : Prop :=
  ∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
    V ≤ K.map (normalizer (A : Set G)).subtype ∧
    oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
    ∃ a : JankoNormalizerAction K,
      a.ResidualSeedFamily ∧ center K = ⊥ ∧
      ∃ z : K, ((z : normalizer (A : Set G)) : G) ∈ V ∧ orderOf z = 2 ∧
        Nonempty ((centralizer ({z} : Set K) ⧸
          pPrimeCore 2 (centralizer ({z} : Set K))) ≃*
            Janko4.InvolutionCentralizers.First.centralizer) ∧
        T ≤ centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) ∧
        ∃ P : Subgroup (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) ⊓
            centralizer (A : Set G) : Subgroup G),
          P.IsCComponent ∧ P.Normal ∧ Nonempty ((P ⧸ solvableRadical P) ≃* M22) ∧
          P.map (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) ⊓
            centralizer (A : Set G)).subtype =
              ((solvableResidual (centralizer ({z} : Set K))).map
                (centralizer ({z} : Set K)).subtype).map
                  ((normalizer (A : Set G)).subtype.comp K.subtype) ∧
          ∃ Q : Subgroup (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G)),
            Q.IsCComponent ∧ ∃ hPQ : P.map (inclusion inf_le_left) ≤ Q,
              ∃ hn : Q.Normal, letI := hn
              IsQuasisimple (Q ⧸ pCore 2 Q) ∧
              Nonempty (OddLocalMathieu.SimpleSection Q ≃* Janko4.Model) ∧
              ∃ hAz : A ≤ centralizer ({((z : normalizer (A : Set G)) : G)} : Set G),
                ∃ x : A, orderOf (OddLocalMathieu.simpleAction Q ⟨x,hAz x.property⟩) = 3 ∧
                  Nat.card ((OddLocalMathieu.simpleAction Q).comp (inclusion hAz)).range = 3 ∧
                  (let f := (OddLocalMathieu.projection Q).comp
                      (OddLocalMathieu.seedInclusion inf_le_left hPQ)
                   let b := (OddLocalMathieu.simpleAction Q).comp (inclusion hAz)
                   f.range = (solvableResidual (b x).fixedSubgroup).map
                     (b x).fixedSubgroup.subtype ∧
                   ∃ y : center f.range, orderOf y = 3 ∧
                     MulAut.conj ((y : f.range) : OddLocalMathieu.SimpleSection Q) = b x ∧
                     b.range = (zpowers ((y : f.range) : OddLocalMathieu.SimpleSection Q)).map
                       MulAut.conj) ∧
                  ((pCore 2 P).map (OddLocalMathieu.seedInclusion inf_le_left hPQ) ≤
                      pCore 2 Q) ∧
                  ∃ I : Subgroup G,
                    ∃ hPI : P.map (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) ⊓
                      centralizer (A : Set G)).subtype ≤ I,
                    ((I : Set G) =
                      (((solvableResidual (centralizer ({z} : Set K))).map
                        (centralizer ({z} : Set K)).subtype).map
                          ((normalizer (A : Set G)).subtype.comp K.subtype) : Set G) *
                        (I.pCoreIn 2 : Set G)) ∧
                    (∃ e : (P ⧸ pCore 2 P) ≃* (I ⧸ pCore 2 I),
                      ∀ p : P, e (QuotientGroup.mk' (pCore 2 P) p) =
                        QuotientGroup.mk' (pCore 2 I)
                          ⟨(p.val : G),hPI (mem_map_of_mem _ p.property)⟩) ∧
                    I ≤ Q.map (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G)).subtype ∧
                    A ≤ sectionCentralizer I ∧ Group.IsPerfect I ∧
                    IsQuasisimple (I ⧸ pCore 2 I) ∧
                    Nonempty ((I ⧸ solvableRadical I) ≃* M22) ∧
                    ∃ R : Subgroup (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G)),
                      I = R.map (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G)).subtype ∧
                      R ≤ Q ∧ ∃ (e : OddLocalMathieu.SimpleSection Q ≃* Janko4.Model)
                        (t : Janko4.Model),
                        CubicModuleImageAt T
                          (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G))
                          V A Q e ∧ orderOf t = 2 ∧
                        (∀ c : centralizer ({((z : normalizer (A : Set G)) : G)} : Set G),
                          MulAut.congr e (OddLocalMathieu.simpleAction Q c) t = t →
                            (c : G) ∈ normalizer (I : Set G)) ∧
                        (R.subgroupOf Q).map (e.toMonoidHom.comp (OddLocalMathieu.projection Q)) =
                          (solvableResidual (centralizer ({t} : Set Janko4.Model))).map
                            (centralizer ({t} : Set Janko4.Model)).subtype

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 OddLocalMathieu
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V A : Subgroup G}
    (D : ChosenModule T L V)

/-- Apply the large-module obstruction to the original containing-component map. -/
theorem mathieu_janko_cubic_module_image
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : V = D.sourceOrbit) (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hAV : A ≤ centralizer (V : Set G))
    (hc : MathieuJankoCubicQuotientCase (T : Subgroup G) L V A) :
    MathieuJankoCubicModuleCase (T : Subgroup G) L V A := by
  obtain ⟨K,hK,hn,hout,hVK,hF,a,hseed,hZ,z,hzV,hz,hfirst,hTz,
    P,hP,hPn,eP,hPm,Q,hQ,hPQ,hnQ,hqs,hmodel,hAz,x,hx,hcard,hdata,hcore,
    I,hPI,hfull,heI,hIQ,hAI,hperf,hqI,eI,R,hIR,hRQ,e,t,hSylow,ht,hnorm,himage⟩ := hc
  let := hnQ
  let := hqs
  let := hK.2
  obtain ⟨y,hy,he,hbr⟩ := hdata.2
  have hW := D.original_cubic_module_image_ne_bot h hV hm K a hVK z hzV hz
    hfirst.some P hPm Q hPQ e _ hdata.1 y hy he
  have hTV : (T : Subgroup G) ≤ normalizer (V : Set G) := by
    rw [hV]
    exact D.sourceOrbit_weakClosure_setup.normalizes
  exact ⟨K,hK,hn,hout,hVK,hF,a,hseed,hZ,z,hzV,hz,hfirst,hTz,
    P,hP,hPn,eP,hPm,Q,hQ,hPQ,hnQ,hqs,hmodel,hAz,x,hx,hcard,hdata,hcore,
    I,hPI,hfull,heI,hIQ,hAI,hperf,hqI,eI,R,hIR,hRQ,e,t,
    cubic_module_image_of_nonzero hSylow hW D.le_sylow hTV hAV,ht,hnorm,himage⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Representation.BinaryOffender
universe u
variable {G : Type u} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The literal Hall obstruction retains its full seed and replacement while the original module forces a common central involution of the native Sylow and actor. -/
theorem sourceOrbit_mathieu_hall_cubic_module_image
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
      (((Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M12) ∨
          Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M22)) ∧
          MathieuPushingUpFactoredCase T L V A ∧ MathieuPushingUpFactorGap T L V A) ∨
        (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
          MathieuJankoSeedResidualCase (T : Subgroup G) L V A
            (D.orbitComponent ⧸ center D.orbitComponent) ∧
          (MathieuJankoComparedResidualCase (T : Subgroup G) L V A ∨
            (p = 3 ∧ MathieuJankoCubicModuleCase (T : Subgroup G) L V A)))) := by
  have hsource :=
    @sourceOrbit_mathieu_hall_cubic_quotient G instG finG T L V D
      h hmany hV hm hnon H hH hlarge B hBN hHall hker
  refine hsource.imp fun p hpA => hpA.imp fun A hA => ?_
  obtain ⟨hp,ho,hne,he,hAH,hAL,hAV,hAT,hN,hX,hcontrol,hcases⟩ := hA
  refine ⟨hp,ho,hne,he,hAH,hAL,hAV,hAT,hN,hX,hcontrol,?_⟩
  apply Or.imp id _ hcases
  intro hc
  exact ⟨hc.1,hc.2.1,hc.2.2.imp id (fun ht =>
    ⟨ht.1,D.mathieu_janko_cubic_module_image h.toHypothesis1221 hV hm hAV ht.2⟩)⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
