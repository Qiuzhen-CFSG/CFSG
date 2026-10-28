module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.CentralizerSelection
public import CFSG.Quasithin.ChapterA.Section03.QTComponents.MathieuSections
public import CFSG.Quasithin.ChapterI.Section03.InvolutionSource

/-!
# The original cubic residual in its full ambient centralizer

Apply I.3.2 to the original M₂₂ covering residual in the simultaneous
centralizer. The transposed-pair branch would give a forbidden M₂₂ × M₂₂
section. Its literal odd-E closure is therefore a two-component of C_G(x).
The same section obstruction proves normality and unique containment, and
the full Theorem B catalogue identifies its actual simple core quotient.

The literal Hall obstruction supplies all inputs on the original full J₄
cover, placed cubic and reselected involution. This constructs the containing
two-component; equality with the original residual, the final pushing-up
contradiction and the M₂₄ fixed-line comparison remain to be proved.

Source: Aschbacher--Smith 4.2.13, printed p.612, and its application in
4.4.14, printed pp.623--625.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin CFSG.Quasithin.ChapterA.Section02
open CFSG.Quasithin.ChapterA.QTComponents
open CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape
open Sporadic.Mathieu

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
/-- The odd-E closure of an M₂₂ covering component in an involution centralizer
is one invariant two-component; the transposed-pair branch is impossible. -/
theorem m22_involution_twoComponent
    {G : Type*} [Group G] [Finite G]
    (hG : IsQuasithin G) (hκ : IsKGroup KnownSimple.IsKnownSimple G)
    (t : G) (ht : orderOf t = 2)
    (L : Subgroup (centralizer ({t} : Set G)))
    (hL : IsComponent (centralizer ({t} : Set G)) L)
    (e : (L ⧸ center L) ≃* M22) :
    let X := componentOrbit (L.map (centralizer ({t} : Set G)).subtype) (oddELayer G)
    X.IsTwoComponent ∧ X.map (MulAut.conj t).toMonoidHom = X := by
  let hl := ChapterI.Balance.ordinary_isTwoComponent hL
  rcases ChapterI.lemma_I_3_2 t ht L hl with h | ⟨J,hJ,hne,_,⟨eq⟩⟩
  · exact h
  let : Group.IsSolvable (pPrimeCore 2 L) := odd_order_theorem _
    (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
  let : IsSimpleGroup M22 := m22_isSimpleGroup
  let eL := hl.quotientOddTwoCoreEquivOfSurjectiveSimple
    (e.toMonoidHom.comp (QuotientGroup.mk' (center L)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  let a := eq.trans eL
  let J' := J.map (MulAut.conj t).toMonoidHom
  let ej : J ≃* J' := (MulAut.conj t).subgroupMap J
  let b := (QuotientGroup.congr _ _ ej (oddTwoCore_map_equiv ej)).symm.trans a
  obtain ⟨f,_,_⟩ := ChapterI.ComponentQuotients.pair_quotient_equiv hJ
    (hJ.map_equiv (MulAut.conj t)) hne
  exact (no_m22_pair_section hG hκ a b ⟨J ⊔ J',
    f.toMonoidHom.comp (QuotientGroup.mk' (oddTwoCore ↥(J ⊔ J'))),
    f.surjective.comp (QuotientGroup.mk'_surjective _)⟩).elim
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
/-- An actual M₂₂ covering component of the simultaneous centralizer has
an invariant two-component as its literal odd-E closure in C_G(x). -/
theorem m22_simultaneous_twoComponent
    {G : Type*} [Group G] [Finite G]
    (x r : G) (hr : orderOf r = 2) (S : Subgroup G)
    (hx : x ∈ S)
    (hS : IsComponentIn S (centralizer ({x} : Set G) ⊓ centralizer ({r} : Set G)))
    (e : (S ⧸ center S) ≃* M22)
    (hqt : IsQuasithin (centralizer ({x} : Set G)))
    (hκ : IsKGroup KnownSimple.IsKnownSimple (centralizer ({x} : Set G))) :
    ∃ hrx : r ∈ centralizer ({x} : Set G),
      let Cx := centralizer ({x} : Set G)
      let X := componentOrbit (S.subgroupOf Cx) (oddELayer Cx)
      X.IsTwoComponent ∧
        X.map (MulAut.conj (⟨r,hrx⟩ : Cx)).toMonoidHom = X ∧
        S.subgroupOf Cx ≤ X := by
  let Cx := centralizer ({x} : Set G)
  have hrx : r ∈ Cx := mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp (hS.1 hx).2).symm
  let rX : Cx := ⟨r,hrx⟩
  let C := centralizer ({rX} : Set Cx)
  let Cr := centralizer ({x} : Set G) ⊓ centralizer ({r} : Set G)
  let D := S.subgroupOf Cx
  have hSCx : S ≤ Cx := hS.1.trans inf_le_left
  have hDC : D ≤ C := by
    intro s hs
    exact mem_centralizer_singleton_iff.mpr
      (Subtype.ext (mem_centralizer_singleton_iff.mp (hS.1 hs).2))
  let f : C →* Cr := (Cx.subtype.comp C.subtype).codRestrict Cr (fun c =>
    ⟨c.val.property,mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp c.property))⟩)
  let L := D.subgroupOf C
  let a : L ≃* S := (subgroupOfEquivOfLe hDC).trans (subgroupOfEquivOfLe hSCx)
  let := hS.quasisimple
  have hL : IsComponent C L := ⟨hS.2.1.comap f,IsQuasisimple.of_mulEquiv a.symm⟩
  have h := m22_involution_twoComponent hqt hκ rX ((orderOf_coe rX).symm.trans hr)
    L hL ((centerQuotientCongr a).trans e)
  have hm : L.map C.subtype = D := map_subgroupOf_eq_of_le hDC
  change (componentOrbit (L.map C.subtype) (oddELayer Cx)).IsTwoComponent ∧
    (componentOrbit (L.map C.subtype) (oddELayer Cx)).map
      (MulAut.conj rX).toMonoidHom = componentOrbit (L.map C.subtype) (oddELayer Cx) at h
  rw [hm] at h
  exact ⟨hrx,h.1,h.2,le_componentOrbit D (oddELayer Cx)⟩
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
/-- The original odd-E closure is the unique containing two-component of
the full cubic centralizer, and is normal there with an actual simple model. -/
theorem m22_simultaneous_normal_twoComponent
    {G : Type*} [Group G] [Finite G]
    (x r : G) (hr : orderOf r = 2) (S : Subgroup G)
    (hx : x ∈ S)
    (hS : IsComponentIn S (centralizer ({x} : Set G) ⊓ centralizer ({r} : Set G)))
    (e : (S ⧸ center S) ≃* M22)
    (hqt : IsQuasithin (centralizer ({x} : Set G)))
    (hκ : IsKGroup KnownSimple.IsKnownSimple (centralizer ({x} : Set G))) :
    ∃ hrx : r ∈ centralizer ({x} : Set G),
      let Cx := centralizer ({x} : Set G)
      let X := componentOrbit (S.subgroupOf Cx) (oddELayer Cx)
      X.IsTwoComponent ∧ X.Normal ∧
        X.map (MulAut.conj (⟨r,hrx⟩ : Cx)).toMonoidHom = X ∧
        S.subgroupOf Cx ≤ X ∧
        IsTheoremBModel (X ⧸ oddTwoCore X) ∧
        ∀ Q : Subgroup Cx, Q.IsTwoComponent → S.subgroupOf Cx ≤ Q → Q = X := by
  obtain ⟨hrx,hX,hinv,hDX⟩ := m22_simultaneous_twoComponent x r hr S hx hS e hqt hκ
  let Cx := centralizer ({x} : Set G)
  let D := S.subgroupOf Cx
  let X := componentOrbit D (oddELayer Cx)
  have hSCx : S ≤ Cx := hS.1.trans inf_le_left
  have hsection (Q : Subgroup Cx) (hDQ : D ≤ Q) : IsSectionOf (S ⧸ center S) Q := by
    let f := (inclusion hDQ).comp (subgroupOfEquivOfLe hSCx).symm.toMonoidHom
    exact (IsSectionOf.of_surjective (QuotientGroup.mk' (center S))
      (QuotientGroup.mk'_surjective _)).ambient_injective f
      ((inclusion_injective hDQ).comp (subgroupOfEquivOfLe hSCx).symm.injective)
  have hn := twoComponent_normal_of_m22_section hqt hκ X hX e (hsection X hDX)
  refine ⟨hrx,hX,hn,hinv,hDX,twoComponent_simple_quotient_model hqt hκ X hX,?_⟩
  intro Q hQ hDQ
  let := twoComponent_normal_of_m22_section hqt hκ Q hQ e (hsection Q hDQ)
  have hXQ : X ≤ Q := iSup_conjugates_le_of_le_normalizer D (oddELayer Cx) Q hDQ
    (by rw [normalizer_eq_top]; exact le_top)
  exact (hX.1.eq_of_le hQ.1 hXQ).symm
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Subgroup Theory.GroupTheory
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterA.Section02 Sporadic.Mathieu Janko4.InvolutionCentralizers

/-- The literal odd-E closure of the original residual in the full cubic
centralizer, with relative normality, unique containment, and actual quotient model. -/
@[expose] def CubicPumpupData {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (K : Subgroup H) (x : K) (r : G) : Prop :=
  ∃ hrx : r ∈ centralizer ({((x : H) : G)} : Set G),
    let Cx := centralizer ({((x : H) : G)} : Set G)
    let S := cubicResidualImage H K x
    let X := componentOrbit (S.subgroupOf Cx) (oddELayer Cx)
    X.IsTwoComponent ∧ X.Normal ∧
      X.map (MulAut.conj (⟨r,hrx⟩ : Cx)).toMonoidHom = X ∧
      S.subgroupOf Cx ≤ X ∧ IsTheoremBModel (X ⧸ oddTwoCore X) ∧
      ∀ Q : Subgroup Cx, Q.IsTwoComponent → S.subgroupOf Cx ≤ Q → Q = X

/-- Apply I.3.2 and the M₂₂ pair exclusion to the original full-cover residual. -/
theorem cubic_residual_ambient_component {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (K : Subgroup H) (x : K) (r : G) (hr : orderOf r = 2)
    (hdata : CubicAmbientData H K x)
    (hcomp : IsComponentIn (cubicResidualImage H K x)
      (centralizer ({((x : H) : G)} : Set G) ⊓ centralizer ({r} : Set G)))
    (e : (solvableResidual (centralizer ({x} : Set K)) ⧸
      center (solvableResidual (centralizer ({x} : Set K)))) ≃* M22) :
    CubicPumpupData H K x r := by
  let f := H.subtype.comp K.subtype
  let a : solvableResidual (centralizer ({x} : Set K)) ≃* cubicResidualImage H K x :=
    ((solvableResidual (centralizer ({x} : Set K))).equivMapOfInjective
      (centralizer ({x} : Set K)).subtype
      (centralizer ({x} : Set K)).subtype_injective).trans
      (((solvableResidual (centralizer ({x} : Set K))).map
        (centralizer ({x} : Set K)).subtype).equivMapOfInjective f
          (H.subtype_injective.comp K.subtype_injective))
  obtain ⟨_,_,hx,_,hqt,hκ,_⟩ := hdata
  exact m22_simultaneous_normal_twoComponent ((x : H) : G) r hr _ hx hcomp
    ((centerQuotientCongr a.symm).trans e) hqt hκ

/-- The original full J₄ cover and placed cubic, with its unique normal
containing two-component in the full cubic centralizer. -/
@[expose] def MathieuPushingUpAmbientComponentCase {G : Type*} [Group G] [Finite G]
    (L V A : Subgroup G) : Prop :=
  ∃ J H W : Subgroup G, Witness L V A J H W ∧
    ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ (normalizer (L : Set G)).subgroupOf H ∧
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
      ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
      F.subgroupOf H ≤ K ∧ W.subgroupOf H ≤ K ∧
      H = K.map H.subtype ⊔ (H ⊓ centralizer (K.map H.subtype : Set G)) ∧
      ∃ (r : H.pCoreIn 2) (H₁ : Subgroup G), orderOf r = 2 ∧
        centralizer ({(r : G)} : Set G) ≤ H₁ ∧
        IsComponentIn (K.map H.subtype) H₁ ∧
        ((K.map H.subtype).subgroupOf H₁).Normal ∧
        IsComponentIn (K.map H.subtype) (centralizer ({(r : G)} : Set G)) ∧
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
              (let C := centralizer ({((y : H) : G)} : Set G) ⊓ centralizer ({(r : G)} : Set G)
               IsComponentIn (cubicResidualImage H K y) C ∧
                 ((cubicResidualImage H K y).subgroupOf C).Normal) ∧
              CubicPumpupData H K y (r : G) ∧
              ∀ Q : Subgroup (centralizer ({y} : Set K)), Q.IsCComponent →
                Q = solvableResidual (centralizer ({y} : Set K))) ∧
          ∀ Q : Subgroup (Subgroup.centralizer ({(x : K)} : Set K)), Q.IsCComponent →
            Q = solvableResidual (Subgroup.centralizer ({(x : K)} : Set K))


/-- Construct the actual unique normal containing two-component in C_G(x),
preserving the full cover, placed conjugate, involution and every quotient map. -/
theorem pushingUp_cubic_ambient_component {G : Type*} [Group G] [Finite G]
    {L V A : Subgroup G} (hc : MathieuPushingUpCentralizedCubicCase L V A) :
    MathieuPushingUpAmbientComponentCase L V A := by
  obtain ⟨J,H,W,hw,hesc,K,hK,hn,hout,hFK,hWK,hprod,r,H₁,hr,hCH,hrel,hn₁,hKr,
    e,x,hx,hqx,hmem,he,hquasi,heq,⟨g,hg,hqy,hey,hdata,hs,huy⟩,hux⟩ := hc
  have hp := cubic_residual_ambient_component H K (g * (x : K) * g⁻¹) (r : G)
    ((orderOf_coe r).trans hr) hdata hs.1 hey.some
  exact ⟨J,H,W,hw,hesc,K,hK,hn,hout,hFK,hWK,hprod,r,H₁,hr,hCH,hrel,hn₁,hKr,
    e,x,hx,hqx,hmem,he,hquasi,heq,⟨g,hg,hqy,hey,hdata,hs,hp,huy⟩,hux⟩

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
universe u
variable {G : Type u} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

set_option maxHeartbeats 400000 in
/-- The literal Hall obstruction supplies the unique normal containing
two-component of the full cubic centralizer on the original placed residual.
No new source premise or residual-identification callback is assumed. -/
theorem sourceOrbit_mathieu_hall_ambient_component_obstruction
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
      (MathieuPushingUpAmbientComponentCase L V A ∨
        (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
          MathieuJankoSeedResidualCase (T : Subgroup G) L V A
            (D.orbitComponent ⧸ center D.orbitComponent))) := by
  obtain ⟨p,A,hp,ho,hne,he,hAH,hAC,hAV,hAT,hout,hclosure,hcompare,hcase⟩ :=
    @sourceOrbit_mathieu_hall_centralized_cubic_obstruction G instG finG T L V D
      h hmany hV hm hnon H hH hlarge B hBN hHall hker
  exact ⟨p,A,hp,ho,hne,he,hAH,hAC,hAV,hAT,hout,hclosure,hcompare,
    hcase.imp pushingUp_cubic_ambient_component id⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
