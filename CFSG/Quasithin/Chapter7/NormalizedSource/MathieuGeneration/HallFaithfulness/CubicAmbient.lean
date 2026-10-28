module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.CubicPlacement
public import Theory.GroupTheory.GeneralizedFitting.NormalCentralizerResidual
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent

/-!
# Ambient local control of the placed cubic residual

The full M₂₂ covering residual, mapped through the original J₄ component
inclusions, is a normal ordinary component of C_H(x). An involution r in
the original O₂(H) centralizes the full component. The simultaneous
centralizer C_G(x) intersect C_G(r) is SQTK, so the M₂₂ rank argument
places the same residual in a unique normal C-component there. The cubic
belongs to the residual and remains central of order three modulo the
containing component's two-core; A.3.6 gives its actual three-cover model.

C_G(x) itself is only asserted to be a proper quasithin K-group. Promoting
the residual to that whole centralizer and deriving the pushing-up
contradiction still require the source's additional argument. The literal
Hall consumer constructs all the local data without new hypotheses.

Source: Aschbacher--Smith 4.2.13, printed pp.611--612, and its application
in 4.4.14, printed pp.624--625. The involution and odd-actor comparison
in 4.4.3, printed p.623, remains a separate branch.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
variable {G : Type*} [Group G] [Finite G]

private theorem conjugate_mem (K : Type*) [Group K] [Finite K] (x g : K)
    (hm : (⟨x,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({x} : Set K)) ∈
      solvableResidual (centralizer ({x} : Set K))) :
    (⟨g*x*g⁻¹,mem_centralizer_singleton_iff.mpr rfl⟩ :
      centralizer ({g*x*g⁻¹} : Set K)) ∈
      solvableResidual (centralizer ({g*x*g⁻¹} : Set K)) := by
  let f := (MulAut.conj g).toMonoidHom.elementCentralizerMap x
  exact map_solvableResidual_le f (mem_map_of_mem f hm)


@[expose] def cubicResidualImage (H : Subgroup G) (K : Subgroup H) (x : K) : Subgroup G :=
  ((solvableResidual (centralizer ({x} : Set K))).map
    (centralizer ({x} : Set K)).subtype).map (H.subtype.comp K.subtype)

omit [Finite G] in
private theorem cubicResidualImage_le (H : Subgroup G) (K : Subgroup H) (x : K) :
    cubicResidualImage H K x ≤ H ⊓ centralizer ({((x : H) : G)} : Set G) := by
  rintro y ⟨d,⟨s,hs,rfl⟩,rfl⟩
  exact ⟨s.val.val.property,mem_centralizer_singleton_iff.mpr
    (congrArg (H.subtype.comp K.subtype) (mem_centralizer_singleton_iff.mp s.property))⟩

private theorem cubicResidualImage_normalizer (H : Subgroup G) (K : Subgroup H) [K.Normal] (x : K) :
    H ⊓ centralizer ({((x : H) : G)} : Set G) ≤
      normalizer (cubicResidualImage H K x : Set G) := by
  let C := centralizer ({K.subtype x} : Set H)
  let R : Subgroup C := (solvableResidual (centralizer ({x} : Set K))).map
    (K.subtype.elementCentralizerMap x)
  let : R.Normal := centralizer_residual_normal K x
  have he : R.map (H.subtype.comp C.subtype) = cubicResidualImage H K x := by
    change ((solvableResidual (centralizer ({x} : Set K))).map
      (K.subtype.elementCentralizerMap x)).map (H.subtype.comp C.subtype) = _
    rw [map_map]
    rw [cubicResidualImage,map_map]
    rfl
  have hh := R.le_normalizer_map (H.subtype.comp C.subtype)
  rw [he,normalizer_eq_top] at hh
  intro a ha
  apply hh
  refine ⟨⟨⟨a,ha.1⟩,?_⟩,mem_top _,rfl⟩
  exact mem_centralizer_singleton_iff.mpr
    (Subtype.ext (mem_centralizer_singleton_iff.mp ha.2))

omit [Finite G] in
private theorem cubicResidualImage_quasisimple (H : Subgroup G) (K : Subgroup H) (x : K)
    [IsQuasisimple (solvableResidual (centralizer ({x} : Set K)))] :
    IsQuasisimple (cubicResidualImage H K x) := by
  let f := (H.subtype.comp K.subtype).comp (centralizer ({x} : Set K)).subtype
  have hi : Function.Injective f := H.subtype_injective.comp
    (K.subtype_injective.comp (centralizer ({x} : Set K)).subtype_injective)
  have he : (solvableResidual (centralizer ({x} : Set K))).map f =
      cubicResidualImage H K x := (map_map _ _ _).symm
  exact he ▸ IsQuasisimple.of_mulEquiv
    ((solvableResidual (centralizer ({x} : Set K))).equivMapOfInjective f hi)

private theorem cubicResidualImage_component (H : Subgroup G) (K : Subgroup H) [K.Normal] (x : K)
    [IsQuasisimple (solvableResidual (centralizer ({x} : Set K)))] :
    IsComponentIn (cubicResidualImage H K x)
      (H ⊓ centralizer ({((x : H) : G)} : Set G)) := by
  have hle := cubicResidualImage_le H K x
  let := cubicResidualImage_quasisimple H K x
  exact ⟨hle,(normal_subgroupOf_of_le_normalizer
    (cubicResidualImage_normalizer H K x)).isSubnormal,
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hle).symm⟩


private def cubicResidualImageEquiv (H : Subgroup G) (K : Subgroup H) (x : K) :
    (solvableResidual (centralizer ({x} : Set K))) ≃* cubicResidualImage H K x :=
  ((solvableResidual (centralizer ({x} : Set K))).equivMapOfInjective
    (centralizer ({x} : Set K)).subtype
    (centralizer ({x} : Set K)).subtype_injective).trans
    (((solvableResidual (centralizer ({x} : Set K))).map
      (centralizer ({x} : Set K)).subtype).equivMapOfInjective
        (H.subtype.comp K.subtype) (H.subtype_injective.comp K.subtype_injective))

open CFSG.Quasithin
open CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Sporadic.Mathieu
open CFSG.Quasithin.Chapter1.Section02.LocalModels
open CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape
private theorem cubic_threeCover {C : Type*} [Group C] [Finite C]
    (hC : IsSQTK CFSG.KnownSimple.IsKnownSimple C)
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
  have hQsq : IsSQTK CFSG.KnownSimple.IsKnownSimple (Q ⧸ pCore 2 Q) := by
    refine ⟨?_,hsQ.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hsQ.stronglyQuasithin p hp ho)
  exact threeCover_of_cubic_center hQsq (pCore_quotient_pCore_eq_bot 2) _ hc3



private theorem cubicResidualImage_simultaneous_component
    (hG : IsSimpleQTKE CFSG.KnownSimple.IsKnownSimple G)
    (H : Subgroup G) (hne : H.pCoreIn 2 ≠ ⊥)
    (K : Subgroup H) (hK : IsComponent H K) (x : K)
    [IsQuasisimple (solvableResidual (centralizer ({x} : Set K)))]
    (hx : orderOf x = 3)
    (hmem : (⟨x,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({x} : Set K)) ∈
      solvableResidual (centralizer ({x} : Set K)))
    (e : (solvableResidual (centralizer ({x} : Set K)) ⧸
      center (solvableResidual (centralizer ({x} : Set K)))) ≃* M22) :
    ∃ r : H.pCoreIn 2, orderOf r = 2 ∧
      K.map H.subtype ≤ centralizer ({(r : G)} : Set G) ∧
      let C := centralizer ({((x : H) : G)} : Set G) ⊓ centralizer ({(r : G)} : Set G)
      cubicResidualImage H K x ≤ C ∧
      ∃! Q : Subgroup C, Q.IsCComponent ∧
        (cubicResidualImage H K x).subgroupOf C ≤ Q ∧ Q.Normal ∧
        IsQuasisimple (Q ⧸ pCore 2 Q) ∧
        ThreeCoverModel (Q ⧸ pCore 2 Q) := by
  obtain ⟨r,hr,hKr⟩ := component_core_involution H hne K hK
  let C := centralizer ({((x : H) : G)} : Set G) ⊓ centralizer ({(r : G)} : Set G)
  let S := cubicResidualImage H K x
  have hSK : S ≤ K.map H.subtype := by
    rintro y ⟨s,⟨d,hd,rfl⟩,rfl⟩
    exact ⟨d.val.val,d.val.property,rfl⟩
  have hSC : S ≤ C := le_inf ((cubicResidualImage_le H K x).trans inf_le_right) (hSK.trans hKr)
  have hrG : orderOf (r : G) = 2 := (orderOf_coe r).trans hr
  have hCr : IsSQTK CFSG.KnownSimple.IsKnownSimple (centralizer ({(r : G)} : Set G)) :=
    hG.twoLocal_sqtk (isTwoLocal_involution_centralizer hrG)
  let i : C →* centralizer ({(r : G)} : Set G) := inclusion inf_le_right
  have hC : IsSQTK CFSG.KnownSimple.IsKnownSimple C :=
    ⟨hCr.stronglyQuasithin.of_injective i (inclusion_injective inf_le_right),
      hCr.isKGroup.of_injective i (inclusion_injective inf_le_right)⟩
  let := cubicResidualImage_quasisimple H K x
  let es := (centerQuotientCongr (cubicResidualImageEquiv H K x).symm).trans e
  obtain ⟨Q,⟨hQ,hSQ,hn,hq⟩,hu⟩ :=
    quasisimple_seed_component hC es (inclusion hSC) (inclusion_injective hSC)
  have hf : (inclusion hSC).range = S.subgroupOf C := by
    ext c
    constructor
    · rintro ⟨s,rfl⟩
      exact s.property
    · intro hc
      exact ⟨⟨c,hc⟩,Subtype.ext rfl⟩
  have hxS : ((x : H) : G) ∈ S :=
    mem_map_of_mem (H.subtype.comp K.subtype)
      (mem_map_of_mem (centralizer ({x} : Set K)).subtype hmem)
  let cx : C := ⟨x,hSC hxS⟩
  let c : Q := ⟨cx,hSQ ⟨⟨x,hxS⟩,rfl⟩⟩
  have hc : orderOf c = 3 := by
    exact (orderOf_coe c).symm.trans ((orderOf_coe cx).symm.trans
      ((orderOf_coe (x : H)).trans ((orderOf_coe x).trans hx)))
  have hz : c ∈ center Q := mem_center_iff.mpr (fun y =>
    Subtype.ext (Subtype.ext (mem_centralizer_singleton_iff.mp y.val.property.1)))
  let := hq
  refine ⟨r,hr,hKr,hSC,Q,⟨hQ,hf ▸ hSQ,hn,hq,cubic_threeCover hC Q c hc hz⟩,?_⟩
  intro Q' hQ'
  exact hu Q' ⟨hQ'.1,hf.symm ▸ hQ'.2.1,hQ'.2.2.1,hQ'.2.2.2.1⟩


open CFSG.Quasithin
open CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open CFSG.Quasithin.Chapter1.Section02.LocalModels

/-- The literal local residual and simultaneous centralizer at the marked cubic.
This records no promotion to the whole odd-element centralizer. -/
@[expose] def CubicAmbientData (H : Subgroup G) (K : Subgroup H) (x : K) : Prop :=
  let S := cubicResidualImage H K x
  let Cx := centralizer ({((x : H) : G)} : Set G)
  IsComponentIn S (H ⊓ Cx) ∧ (S.subgroupOf (H ⊓ Cx)).Normal ∧
    ((x : H) : G) ∈ S ∧ Cx ≠ ⊤ ∧ IsQuasithin Cx ∧
    IsKGroup CFSG.KnownSimple.IsKnownSimple Cx ∧
    ∃ r : H.pCoreIn 2, orderOf r = 2 ∧
      K.map H.subtype ≤ centralizer ({(r : G)} : Set G) ∧
      let C := Cx ⊓ centralizer ({(r : G)} : Set G)
      S ≤ C ∧ ∃! Q : Subgroup C, Q.IsCComponent ∧ S.subgroupOf C ≤ Q ∧
        Q.Normal ∧ IsQuasisimple (Q ⧸ pCore 2 Q) ∧ ThreeCoverModel (Q ⧸ pCore 2 Q)

/-- The full original residual is normal in C_H(x), and its simultaneous
centralizer contains it in a unique normal C-component with a three-cover
two-core quotient. No assertion that C_G(x) is SQTK is used. -/
theorem cubic_ambient_data
    (hG : IsSimpleQTKE CFSG.KnownSimple.IsKnownSimple G)
    (H : Subgroup G) (hne : H.pCoreIn 2 ≠ ⊥)
    (K : Subgroup H) [K.Normal] (hK : IsComponent H K) (x : K)
    (hx : orderOf x = 3)
    (hmem : (⟨x,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({x} : Set K)) ∈
      solvableResidual (centralizer ({x} : Set K)))
    [IsQuasisimple (solvableResidual (centralizer ({x} : Set K)))]
    (e : (solvableResidual (centralizer ({x} : Set K)) ⧸
      center (solvableResidual (centralizer ({x} : Set K)))) ≃* Sporadic.Mathieu.M22) :
    CubicAmbientData H K x := by
  have hxG : orderOf ((x : H) : G) = 3 :=
    (orderOf_coe (x : H)).trans ((orderOf_coe x).trans hx)
  have hneX : zpowers (((x : H) : G)) ≠ ⊥ := by
    intro he
    have hx1 := mem_bot.mp (he ▸ mem_zpowers (((x : H) : G)))
    rw [hx1,orderOf_one] at hxG
    omega
  have hN := Chapter4.Section04.oddNormalizer_properQTK hG
    (zpowers (((x : H) : G))) hneX
  have hCN : centralizer ({((x : H) : G)} : Set G) ≤
      normalizer (zpowers (((x : H) : G)) : Set G) := by
    have hc : centralizer (zpowers (((x : H) : G)) : Set G) =
        centralizer ({((x : H) : G)} : Set G) := by
      rw [zpowers_eq_closure,centralizer_closure]
    exact hc ▸ Subgroup.centralizer_le_normalizer _
  have hproper : centralizer ({((x : H) : G)} : Set G) ≠ ⊤ :=
    fun he => hN.1 (top_unique (he ▸ hCN))
  refine ⟨cubicResidualImage_component H K x,
    normal_subgroupOf_of_le_normalizer (cubicResidualImage_normalizer H K x),
    mem_map_of_mem (H.subtype.comp K.subtype)
      (mem_map_of_mem (centralizer ({x} : Set K)).subtype hmem),
    hproper,hG.quasithin.subgroup _,hG.properK _ hproper,?_⟩
  exact cubicResidualImage_simultaneous_component hG H hne K hK x hx hmem e

open Janko4.InvolutionCentralizers
open CFSG.Quasithin.Chapter4 CFSG.Quasithin.Chapter4.Section04
open CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape

/-- The original cubic placement, with ambient local centralizer control on the same full component. -/
@[expose] def MathieuPushingUpAmbientCubicCase {G : Type*} [Group G] [Finite G]
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
          (∃ g : K, ((g * (x : K) * g⁻¹ : K) : H) ∈ F.subgroupOf H ∧
            let y := g * (x : K) * g⁻¹
            IsQuasisimple (solvableResidual (centralizer ({y} : Set K))) ∧
              Nonempty ((solvableResidual (centralizer ({y} : Set K)) ⧸
                center (solvableResidual (centralizer ({y} : Set K)))) ≃* M22) ∧
              CubicAmbientData H K y ∧
              ∀ Q : Subgroup (centralizer ({y} : Set K)), Q.IsCComponent →
                Q = solvableResidual (centralizer ({y} : Set K))) ∧
          ∀ Q : Subgroup (Subgroup.centralizer ({(x : K)} : Set K)), Q.IsCComponent →
            Q = solvableResidual (Subgroup.centralizer ({(x : K)} : Set K))

/-- Construct ambient local control for the cubic already placed in the
original intersection residual, retaining the full cover and all maps. -/
theorem pushingUp_cubic_ambient
    (hG : IsSimpleQTKE CFSG.KnownSimple.IsKnownSimple G)
    {L V A : Subgroup G} (hc : MathieuPushingUpPlacedCubicCase L V A) :
    MathieuPushingUpAmbientCubicCase L V A := by
  obtain ⟨J,H,W,hw,hesc,K,hK,hn,hout,hFK,hWK,hprod,e,x,hx,hqx,hmem,he,hquasi,heq,
    ⟨g,hg,hqy,hey,huy⟩,hux⟩ := hc
  let := hn
  let := hqy
  have hxfull : (⟨(x : K),mem_centralizer_singleton_iff.mpr rfl⟩ :
      centralizer ({(x : K)} : Set K)) ∈ solvableResidual (centralizer ({(x : K)} : Set K)) := by
    rw [he]
    exact mem_map_of_mem _ hmem
  have hy : orderOf (g * (x : K) * g⁻¹) = 3 :=
    ((MulAut.conj g).orderOf_eq (x : K)).trans ((orderOf_coe x).trans hx)
  have hdata := cubic_ambient_data hG H hw.2.2.2.2.2.2.1.core_nontrivial K hK
    (g * (x : K) * g⁻¹) hy (conjugate_mem K (x : K) g hxfull) hey.some
  exact ⟨J,H,W,hw,hesc,K,hK,hn,hout,hFK,hWK,hprod,e,x,hx,hqx,hmem,he,hquasi,heq,
    ⟨g,hg,hqy,hey,hdata,huy⟩,hux⟩


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
/-- The literal Hall obstruction supplies ambient local normality of the placed
cubic residual and its unique normal containing component in a simultaneous
centralizer, with a genuine three-cover quotient. The final ambient
pushing-up exclusion remains to be proved. -/
theorem sourceOrbit_mathieu_hall_ambient_cubic_obstruction
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
      (MathieuPushingUpAmbientCubicCase L V A ∨
        (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
          MathieuJankoSeedResidualCase (T : Subgroup G) L V A
            (D.orbitComponent ⧸ center D.orbitComponent))) := by
  obtain ⟨p,A,hp,ho,hne,he,hAH,hAC,hAV,hAT,hout,hclosure,hcompare,hcase⟩ :=
    @sourceOrbit_mathieu_hall_placed_cubic_obstruction G instG finG T L V D
      h hmany hV hm hnon H hH hlarge B hBN hHall hker
  exact ⟨p,A,hp,ho,hne,he,hAH,hAC,hAV,hAT,hout,hclosure,hcompare,
    hcase.imp (pushingUp_cubic_ambient h.simpleQTKE) id⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
