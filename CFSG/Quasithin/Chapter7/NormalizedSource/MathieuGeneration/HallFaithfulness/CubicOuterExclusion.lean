module
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.ResidualCubicInversion
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.CubicSylowImage
public import Theory.GroupTheory.GeneralizedFitting.SemisimpleCenter

/-!
# Excluding the exceptional cubic with the full original centralizer

The original component K of N_G(A) centralizes the abelian normal actor A.
Restrict the containing component's literal native action to C_K(z). The
full residual equality identifies its residual image with the original
seed image. Full seed-core placement and the inclusion-induced isomorphism
P/O₂(P) ≃ I/O₂(I) make that image quasisimple. The marked central cubic is
exactly the native image of the original actor element, so the image of
all of C_K(z) centralizes it.

The original centralizer is in the first native row. Its outer coset
inverts every surviving central cubic in the residual image, contradicting
that centralization. This excludes the entire original cubic alternative;
no change of the replacement, seed, component cover or marking is made.
In particular the proof does not require identifying the common fixed
involution with the replacement's marking. Every premise of the native
inversion obstruction is discharged by the retained source data.

The Hall application now leaves only the M₁₂/M₂₂ pushing-up alternatives
and the odd-normalizer comparison with K_Z already inside N_G(L). The
M₂₄ fixed-line and L_A/seed generation comparisons and final assembly of
SourceMathieuHallFaithfulAt remain open.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 4.4.3,
printed p.623, applied in 4.4.14, pp.624–625; GLS3 Table 5.3i for the
full first centralizer. Imported native certificates retain their source
attribution and licenses.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 OddLocalMathieu
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

namespace JankoNormalizerAction
variable {N : Type*} [Group N] [Finite N] {K : Subgroup N}
    (a : JankoNormalizerAction K) [IsQuasisimple K]
include a in
/-- The inversion obstruction uses the whole original involution centralizer. -/
theorem no_fixed_first_residual_cubic
    (z : K) (hz : orderOf z = 2)
    (e : (centralizer ({z} : Set K) ⧸ pPrimeCore 2 (centralizer ({z} : Set K))) ≃*
      Janko4.InvolutionCentralizers.First.centralizer)
    {Y : Type*} [Group Y] (f : centralizer ({z} : Set K) →* Y)
    [IsQuasisimple ((solvableResidual (centralizer ({z} : Set K))).map f)]
    (y : Y) (hy : orderOf y = 3)
    (hmem : y ∈ (solvableResidual (centralizer ({z} : Set K))).map f)
    (hfix : ∀ c, f c * y = y * f c) : False := by
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
  exact Janko4.InvolutionCentralizers.First.no_fixed_residual_cubic g y hy
    (hm.symm ▸ hmem) (fun c => hfix (d.symm c))
end JankoNormalizerAction

/-- The original full centralizer excludes the exceptional cubic branch. -/
theorem mathieu_janko_cubic_first_row_impossible
    {G : Type*} [Group G] [Finite G] {T L V A : Subgroup G}
    [IsMulCommutative A]
    (hc : MathieuJankoCubicFirstRowCase T L V A) : False := by
  obtain ⟨K,hK,hn,hout,hVK,hF,a,hseed,hZ,z,hzV,hz,hfirst,hTz,
    P,hP,hPn,eP,hPm,Q,hQ,hPQ,hnQ,hqs,hmodel,hAz,x,hx,hcard,hdata,hcore,
    I,hPI,hfull,heI,hIQ,hAI,hperf,hqI,eI,htail⟩ := hc
  let := hnQ
  let := hqs
  let := hK.2
  let := hqI
  obtain ⟨ePI,_⟩ := heI
  let : IsQuasisimple (P ⧸ pCore 2 P) := IsQuasisimple.of_mulEquiv ePI.symm
  let zG : G := ((z : normalizer (A : Set G)) : G)
  let C := centralizer ({zG} : Set G)
  let Ck := centralizer ({z} : Set K)
  let E := C ⊓ centralizer (A : Set G)
  let j := (normalizer (A : Set G)).subtype.comp K.subtype
  let i : Ck →* C :=
    { toFun := fun c => ⟨j c,mem_centralizer_singleton_iff.mpr
        (congrArg j (mem_centralizer_singleton_iff.mp c.property))⟩
      map_one' := Subtype.ext (map_one j)
      map_mul' := fun _ _ => Subtype.ext (map_mul j _ _) }
  let f := (projection Q).comp (seedInclusion inf_le_left hPQ)
  obtain ⟨y,hy,he,hbr⟩ := hdata.2
  have hyn : (y : f.range) ≠ 1 := by
    intro hh
    have hy' : orderOf (y : f.range) = 3 := (orderOf_coe y).trans hy
    rw [hh,orderOf_one] at hy'
    omega
  have hfn : f.range ≠ ⊥ := fun hh => hyn (Subtype.ext (mem_bot.mp (hh ▸ y.val.property)))
  let : Nontrivial f.range := (nontrivial_iff_ne_bot _).mpr hfn
  have hk : pCore 2 P ≤ f.rangeRestrict.ker := by
    intro p hp
    apply Subtype.ext
    change projection Q (seedInclusion inf_le_left hPQ p) = 1
    change QuotientGroup.mk' (center (Q ⧸ pCore 2 Q))
      (QuotientGroup.mk' (pCore 2 Q) (seedInclusion inf_le_left hPQ p)) = 1
    have hzero : QuotientGroup.mk' (pCore 2 Q) (seedInclusion inf_le_left hPQ p) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (hcore (mem_map_of_mem _ hp))
    rw [hzero,map_one]
  let r := QuotientGroup.lift (pCore 2 P) f.rangeRestrict hk
  let : IsQuasisimple f.range := IsQuasisimple.of_surjective r
    (QuotientGroup.lift_surjective_of_surjective _ _ f.rangeRestrict_surjective _)
  let e := hmodel.some
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
  let v : Janko4.Model := e y.val.val
  have hv : orderOf v = 3 := (e.orderOf_eq _).trans
    ((orderOf_coe y.val).trans ((orderOf_coe y).trans hy))
  have hvm : v ∈ (solvableResidual Ck).map (q.comp i) := by
    rw [hresq]
    exact mem_map_of_mem e.toMonoidHom y.val.property
  let xC : C := ⟨x,hAz x.property⟩
  have hqx : q xC = v := by
    apply MulAut.conj_injective_of_center_eq_bot Janko4.model_center_eq_bot
    rw [cubicNativeAction_conj]
    change MulAut.congr e (simpleAction Q xC) = MulAut.conj (e y.val.val)
    rw [←MulAut.congr_conj]
    exact congrArg (MulAut.congr e) he.symm
  let N := normalizer (A : Set G)
  let A' := A.subgroupOf N
  let dA := subgroupOfEquivOfLe A.le_normalizer
  let : IsMulCommutative A' := ⟨⟨fun u v => dA.injective (by
    simp only [map_mul]
    exact mul_comm _ _)⟩⟩
  let : Group.IsSolvable A' := Group.isSolvable_of_comm (fun u v => mul_comm u v)
  have hKA : K ≤ centralizer (A' : Set N) := hK.le_centralizer_of_solvable_normal A'
  apply a.no_fixed_first_residual_cubic z hz hfirst.some (q.comp i) v hv hvm
  intro c
  rw [←hqx]
  change q (i c) * q xC = q xC * q (i c)
  rw [←map_mul,←map_mul]
  apply congrArg q
  apply Subtype.ext
  exact (congrArg N.subtype
    (hKA c.val.property (⟨x,A.le_normalizer x.property⟩ : N) x.property)).symm
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Representation.BinaryOffender
universe u
variable {G : Type u} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The exceptional cubic alternative is excluded on the original Hall data.
The full involution-centralizer residual therefore lies in N_G(L) in the
odd-normalizer branch. The separate pushing-up and generation arguments remain. -/
theorem sourceOrbit_mathieu_hall_cubic_excluded
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
          MathieuJankoComparedResidualCase (T : Subgroup G) L V A)) := by
  have hsource :=
    @sourceOrbit_mathieu_hall_cubic_first_row G instG finG T L V D
      h hmany hV hm hnon H hH hlarge B hBN hHall hker
  refine hsource.imp fun p hpA => hpA.imp fun A hA => ?_
  obtain ⟨hp,ho,hne,he,hAH,hAL,hAV,hAT,hN,hX,hcontrol,hcases⟩ := hA
  let := he
  refine ⟨hp,ho,hne,he,hAH,hAL,hAV,hAT,hN,hX,hcontrol,?_⟩
  apply Or.imp id _ hcases
  intro hc
  exact ⟨hc.1,hc.2.1,hc.2.2.resolve_right (fun hbad =>
    mathieu_janko_cubic_first_row_impossible hbad.2)⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
