module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.FullCubicResidual
public import Theory.GroupTheory.PerfectCentralCubicPlacement

/-!
# Placing the cubic in the original Mathieu intersection residual

The cubic is central in the full perfect M₂₂ residual. Its center and
M₂₂ quotient make that residual's order divisible by 27. Since the original
J₄ cover has three-free center, its Sylow three-subgroups have order 27.
Transfer puts the cubic in the Frattini subgroup of such a Sylow subgroup.
The original intersection residual has order divisible by nine, as follows
from its literal Mathieu quotient. Sylow conjugacy therefore puts a
conjugate of the cubic in that original residual.

The conjugating element lies in the same full covering component. The
centralizer and residual equivalences transport quasisimplicity, the M₂₂
central quotient and uniqueness of the C-component to the placed element.
The original quotient map and simultaneous-centralizer identity remain in
the output. The Hall consumer supplies every placement premise from its
original hypotheses. Ambient normality in C_G(x), the pushing-up
contradiction and the separate M₂₄ fixed-line comparison remain to be proved.

Source: Aschbacher--Smith 4.2.13, printed pp.611--612; application to
4.4.14, printed pp.624--625.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4.Section02.RankOneReciprocalEscape Sporadic.Mathieu Janko4.InvolutionCentralizers
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private theorem cover_sylow_three {K : Type*} [Group K] [Finite K]
    (e : (K ⧸ center K) ≃* Janko4.Model) (hZ : Nat.Coprime 3 (Nat.card (center K)))
    (P : Sylow 3 K) : Nat.card P = 3 ^ 3 := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective (center K))
  have hk : q.ker = center K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hi := injective_comp_subtype_of_coprime_ker q (hk.symm ▸ hZ)
    (P : Subgroup K) P.isPGroup'
  have hc : Nat.card P = Nat.card (P.mapSurjective hq) := by
    have he := Nat.card_congr (MonoidHom.ofInjective hi).toEquiv
    simpa only [MonoidHom.range_comp,range_subtype,Sylow.coe_mapSurjective] using he
  rw [hc,(P.mapSurjective hq).card_eq_multiplicity,Janko4.Cardinality.model_card]
  decide +kernel

private theorem m22_central_cubic_card {S : Type*} [Group S] [Finite S]
    (e : (S ⧸ center S) ≃* M22) (x : center S) (hx : orderOf x = 3) :
    3 ^ 3 ∣ Nat.card S := by
  have hz : 3 ∣ Nat.card (center S) := hx ▸ orderOf_dvd_natCard x
  have hq : 9 ∣ (center S).index := by
    rw [index_eq_card,Nat.card_congr e.toEquiv,m22_order]
    norm_num
  have hh := Nat.mul_dvd_mul hz hq
  rw [(center S).card_mul_index] at hh
  exact hh

/-- The central cubic of the full M₂₂ residual has a conjugate in any
subgroup of order divisible by nine in the same full J₄ cover. -/
theorem cubic_residual_conjugate_mem {K : Type*} [Group K] [Finite K]
    (e : (K ⧸ center K) ≃* Janko4.Model) (hZ : Nat.Coprime 3 (Nat.card (center K)))
    (x : K) (hx : orderOf x = 3)
    (hmem : (⟨x,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({x} : Set K)) ∈
      solvableResidual (centralizer ({x} : Set K)))
    (hm : Nonempty ((solvableResidual (centralizer ({x} : Set K)) ⧸
      center (solvableResidual (centralizer ({x} : Set K)))) ≃* M22))
    (F : Subgroup K) (hF : 9 ∣ Nat.card F) :
    ∃ g : K, g * x * g⁻¹ ∈ F := by
  let C := centralizer ({x} : Set K)
  let S := (solvableResidual C).map C.subtype
  let a : (solvableResidual C) ≃* S :=
    (solvableResidual C).equivMapOfInjective C.subtype C.subtype_injective
  let : Group.IsPerfect S := Group.IsPerfect.map C.subtype
  let s : S := ⟨x,mem_map_of_mem C.subtype hmem⟩
  have hs : orderOf s = 3 := (orderOf_coe s).symm.trans hx
  have hsc : s ∈ center S := by
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp ((map_subtype_le _) y.property)
  let b : (S ⧸ center S) ≃* M22 := (centerQuotientCongr a.symm).trans hm.some
  have hd := m22_central_cubic_card b ⟨s,hsc⟩ ((orderOf_coe _).symm.trans hs)
  let P : Sylow 3 K := default
  exact perfect_central_cubic_conjugate_mem P (cover_sylow_three e hZ P) S hd s hs hsc F hF

private theorem mathieu_nine {X : Type*} [Group X] [Finite X]
    (hm : HasMathieuCentralQuotient X) : 9 ∣ Nat.card X := by
  have hd : 9 ∣ Nat.card (X ⧸ center X) := by
    rcases hm with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · rw [Nat.card_congr e.toEquiv,m12_order]; norm_num
    · rw [Nat.card_congr e.toEquiv,m22_order]; norm_num
    · rw [Nat.card_congr e.toEquiv,m23_order]; norm_num
    · rw [Nat.card_congr e.toEquiv,m24_order]; norm_num
  exact hd.trans (card_dvd_of_surjective (QuotientGroup.mk' (center X))
    (QuotientGroup.mk'_surjective _))


private def cubicCentralizerEquiv {K : Type*} [Group K] (a : K ≃* K) (x : K) :
    centralizer ({x} : Set K) ≃* centralizer ({a x} : Set K) where
  toFun := a.toMonoidHom.elementCentralizerMap x
  invFun y := ⟨a.symm y,by
    apply mem_centralizer_singleton_iff.mpr
    apply a.injective
    simpa only [map_mul,a.apply_symm_apply] using mem_centralizer_singleton_iff.mp y.property⟩
  left_inv y := Subtype.ext (a.symm_apply_apply y)
  right_inv y := Subtype.ext (a.apply_symm_apply y)
  map_mul' y z := (a.toMonoidHom.elementCentralizerMap x).map_mul y z

private theorem cubic_conjugate_residual {K : Type*} [Group K] [Finite K]
    (x : K) (g : K)
    (hq : IsQuasisimple (solvableResidual (centralizer ({x} : Set K))))
    (he : Nonempty ((solvableResidual (centralizer ({x} : Set K)) ⧸
      center (solvableResidual (centralizer ({x} : Set K)))) ≃* M22)) :
    let y := g * x * g⁻¹
    IsQuasisimple (solvableResidual (centralizer ({y} : Set K))) ∧
      Nonempty ((solvableResidual (centralizer ({y} : Set K)) ⧸
        center (solvableResidual (centralizer ({y} : Set K)))) ≃* M22) ∧
      ∀ Q : Subgroup (centralizer ({y} : Set K)), Q.IsCComponent →
        Q = solvableResidual (centralizer ({y} : Set K)) := by
  let := hq
  let a := (cubicCentralizerEquiv (MulAut.conj g) x).solvableResidualEquiv
  let hq' := IsQuasisimple.of_mulEquiv a
  refine ⟨hq',⟨(centerQuotientCongr a.symm).trans he.some⟩,?_⟩
  intro Q hQ
  let := hQ.perfect
  have hr : (solvableResidual (centralizer ({g * x * g⁻¹} : Set K))).IsCComponent :=
    (show IsComponent _ _ from ⟨(inferInstance :
      (solvableResidual (centralizer ({g * x * g⁻¹} : Set K))).Normal).isSubnormal,
      hq'⟩).isCComponent
  exact hQ.eq_of_le hr (le_solvableResidual_of_isPerfect Q)

open Chapter4 Chapter4.Section04

/-- Original witnesses and literal maps, with a conjugate of the cubic in the original intersection residual. -/
@[expose] def MathieuPushingUpPlacedCubicCase {G : Type*} [Group G] [Finite G]
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
              ∀ Q : Subgroup (centralizer ({y} : Set K)), Q.IsCComponent →
                Q = solvableResidual (centralizer ({y} : Set K))) ∧
          ∀ Q : Subgroup (Subgroup.centralizer ({(x : K)} : Set K)), Q.IsCComponent →
            Q = solvableResidual (Subgroup.centralizer ({(x : K)} : Set K))

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Place the marked cubic in the original intersection residual by conjugacy
inside the same full covering component. The Sylow order and Frattini
containment are derived, with no embedding-catalogue premise. -/
theorem sourceOrbit_mathieu_pushingUp_cubic_placement
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    {A : Subgroup G} (hc : MathieuPushingUpFullCubicCase L V A) :
    MathieuPushingUpPlacedCubicCase L V A := by
  obtain ⟨J,H,W,hw,hesc,K,hK,hn,hout,hFK,hWK,hprod,e,x,hx,hqx,hmem,he,hquasi,heq,huniq⟩ := hc
  let := hn
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hFH : F ≤ H := (map_subtype_le _).trans inf_le_right
  obtain ⟨ef,_⟩ := hw.2.2.2.2.2.2.2.2.2.2.2.1
  let a := (centerQuotientCongr ef).trans (D.orbitCentralQuotientEquiv h)
  have hmF : HasMathieuCentralQuotient (F ⧸ pCore 2 F) := by
    rcases hm with ⟨⟨b⟩⟩ | ⟨⟨b⟩⟩ | ⟨⟨b⟩⟩ | ⟨⟨b⟩⟩
    · exact Or.inl ⟨a.trans b⟩
    · exact Or.inr (Or.inl ⟨a.trans b⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨a.trans b⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨a.trans b⟩))
  have hdF : 9 ∣ Nat.card F := (mathieu_nine hmF).trans
    (card_dvd_of_surjective (QuotientGroup.mk' (pCore 2 F)) (QuotientGroup.mk'_surjective _))
  let FK := (F.subgroupOf H).subgroupOf K
  have hdFK : 9 ∣ Nat.card FK := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hFK).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hFH).toEquiv]
    exact hdF
  have hxfull : (⟨(x : K),mem_centralizer_singleton_iff.mpr rfl⟩ :
      centralizer ({(x : K)} : Set K)) ∈ solvableResidual (centralizer ({(x : K)} : Set K)) := by
    rw [he]
    exact mem_map_of_mem _ hmem
  obtain ⟨g,hg⟩ := cubic_residual_conjugate_mem e
    (pushingUp_component_center_three_coprime hw K) (x : K)
    ((orderOf_coe x).trans hx) hxfull heq FK hdFK
  exact ⟨J,H,W,hw,hesc,K,hK,hn,hout,hFK,hWK,hprod,e,x,hx,hqx,hmem,he,hquasi,heq,
    ⟨g,hg,cubic_conjugate_residual (x : K) g hquasi heq⟩,huniq⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

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
C-component. A conjugate of the cubic lies in the original intersection residual.
The ambient pushing-up exclusion remains to be proved. -/
theorem sourceOrbit_mathieu_hall_placed_cubic_obstruction
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
      (MathieuPushingUpPlacedCubicCase L V A ∨
        (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
          MathieuJankoSeedResidualCase (T : Subgroup G) L V A
            (D.orbitComponent ⧸ center D.orbitComponent))) := by
  obtain ⟨p,A,hp,ho,hne,he,hAH,hAC,hAV,hAT,hout,hclosure,hcompare,hcase⟩ :=
    @sourceOrbit_mathieu_hall_full_cubic_obstruction G instG finG T L V D
      h hmany hV hm hnon H hH hlarge B hBN hHall hker
  exact ⟨p,A,hp,ho,hne,he,hAH,hAC,hAV,hAT,hout,hclosure,hcompare,
    hcase.imp (D.sourceOrbit_mathieu_pushingUp_cubic_placement h.toHypothesis1221 hm) id⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
