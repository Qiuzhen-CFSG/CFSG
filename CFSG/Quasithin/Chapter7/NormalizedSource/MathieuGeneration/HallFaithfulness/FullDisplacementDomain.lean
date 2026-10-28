module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.CoreFactorization
public import Theory.GroupTheory.RelativeNormalizerInvolution

/-!
# Full-domain involution selection in the Mathieu pushing-up branch

Let R = O₂(J), and retain the original full J₄ covering component K.
If R equals V C_R(K), the already proved disjointness makes this a direct
product. The exact involution-centralizer kernels first force N_P(R) to
centralize V, using residual irreducibility and the nontrivial central
intersection of R with the two-group N_P(R). A central involution of R/V
then lifts in C_R(K), with its commutator domain equal to the full N_P(R).
The proved cubic vanishing puts that domain back inside R, contrary to
strict normalizer growth.

Thus the source witnesses force V Z(K) strictly below R intersect K
whenever LT = L O₂(LT). This retains the full covering center and gives a
precise target for the remaining component-factor identification. The
literal Hall application carries this obstruction alongside all earlier
witnesses. The M₁₂/M₂₂ alternatives, component-factor identification and
separate M₂₄ fixed-line/odd-actor comparison are still open; this module
does not assert SourceMathieuHallFaithfulAt.

Source: Aschbacher--Smith 4.2.13, printed p.612; 4.4.14, pp.624--625.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

omit [Finite G] in
include D in
/-- The original intersection residual has no fixed points in the chosen module. -/
theorem sourceOrbit_pushingUp_residual_fixed_eq_bot
    (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    {A J H W : Subgroup G} (hw : Witness L V A J H W) :
    V ⊓ centralizer (((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype) : Set G) = ⊥ := by
  have hcore : L.pCoreIn 2 ≤ centralizer (V : Set G) :=
    (pCoreIn_mono_of_normalizes (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
      (sup_le L.le_normalizer D.sylow_normalizes_component)).trans D.core_centralizes
  apply bot_unique
  intro v hv
  apply hfix.le
  refine ⟨hv.1,?_⟩
  intro l hl
  obtain ⟨f,hf,q,hq,rfl⟩ := hw.2.2.2.2.2.2.2.1 ▸ (show l ∈ (L : Set G) from hl)
  calc
    (f*q)*v = f*(q*v) := mul_assoc _ _ _
    _ = f*(v*q) := congrArg (f * ·) ((hcore hq) v hv.1).symm
    _ = v*(f*q) := by rw [←mul_assoc,hv.2 f hf,mul_assoc]

/-- Once the component factor is V times its covering center, the full-domain
involution selection contradicts the cubic vanishing calculation. This states
the resulting obstruction without assuming the component-factor identity. -/
theorem sourceOrbit_pushingUp_core_ne_module_sup_centralizer
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : V = D.sourceOrbit) (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (e : (K ⧸ center K) ≃* Janko4.Model)
    (x : K) (hx : orderOf x = 3) (r₀ : G)
    (hfull : CubicPumpupFullResolution H K x r₀)
    (hjoin : (T : Subgroup G) ≤ L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (P : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L))
    (hRP : J.pCoreIn 2 ≤ (P : Subgroup _).map
      (sectionCentralizerIn (normalizer (L : Set G)) L).subtype) :
    J.pCoreIn 2 ≠ V ⊔ (J.pCoreIn 2 ⊓ centralizer (K.map H.subtype : Set G)) := by
  intro hprod
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let R := J.pCoreIn 2
  let C := R ⊓ centralizer (K.map H.subtype : Set G)
  let Pg := (P : Subgroup _).map (sectionCentralizerIn (normalizer (L : Set G)) L).subtype
  let Q := Pg ⊓ normalizer (R : Set G)
  have hc := hw.2.2.2.2.2.2.1
  have hFH : F ≤ H := (map_subtype_le _).trans inf_le_right
  have hFK : F ≤ K.map H.subtype := by
    have hh := map_mono (f := H.subtype) (hc.ordinary_component_contains_original K hK)
    rwa [map_subgroupOf_eq_of_le hFH] at hh
  have hVK : V ≤ K.map H.subtype := hw.2.2.2.2.2.2.2.2.2.2.1.trans hFK
  have hCF : C ≤ centralizer (F : Set G) := inf_le_right.trans (centralizer_le hFK)
  have hCV : C ≤ centralizer (V : Set G) := inf_le_right.trans (centralizer_le hVK)
  have hdis := (D.sourceOrbit_pushingUp_module_disjoint_central_factor hfix hw K hK).2
  have hCne : C ≠ ⊥ := by
    have hHC : H.pCoreIn 2 ≤ C := by
      refine le_inf hc.ambient_core_le_radical ?_
      let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
      have hh := hK.le_centralizer_of_solvable_normal (pCore 2 H)
      rintro r ⟨r,hr,rfl⟩ k ⟨k,hk,rfl⟩
      exact congrArg H.subtype ((hh hk) r hr).symm
    exact fun he => hc.core_nontrivial (bot_unique (hHC.trans_eq he))
  have hM := h.sylow_normalized_maximal_unique D.sylow_normalizes_component
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have huniq : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) :=
    ⟨hM.1,sup_le L.le_normalizer D.sylow_normalizes_component,hM.2⟩
  have hyp := source_hypothesis411 h huniq
  have hFP : F ≤ normalizer (Pg : Set G) :=
    ((map_subtype_le _).trans inf_le_left).trans
      (Chapter4.Section02.Unitary.sectionSylow_normalized
        hyp.plus_le hyp.plus_normal hyp.plus_perfect P)
  have hFR : F ≤ normalizer (R : Set G) :=
    (le_conjugateSpanBy F (H ⊓ normalizer (L : Set G))).trans hc.span_normalizes_radical
  have hFV : F ≤ normalizer (V : Set G) :=
    ((map_subtype_le _).trans inf_le_left).trans D.normalizes
  have hker : ∀ r : G, r ∈ C → orderOf r = 2 → R ≤ centralizer ({r} : Set G) →
      Pg ⊓ centralizer ({r} : Set G) = R := by
    intro r hr hr2 hRr
    exact D.sourceOrbit_pushingUp_core_involution_kernel h hw K hK hout r hr2
      (fun k hk => mem_centralizer_singleton_iff.mpr (hr.2 k hk)) hRr P hRP
  have hPg : IsPGroup 2 Pg := P.isPGroup'.map _
  have hlt : R < Pg := D.sourceOrbit_pushingUp_core_lt_of_localJoin h hw hjoin P hRP
  obtain ⟨hRQ,hQV⟩ := relative_normalizer_centralizes_irreducible_factor
    Pg R V C F hPg hlt hFP hFR hFV hCV hCF hprod
    (D.sourceOrbit_pushingUp_residual_fixed_eq_bot hfix hw) hc.radical_ne_bot
    (fun U hUV hFU => D.sourceOrbit_residual_invariant_subgroup hfix F U
      hw.2.2.2.2.2.2.2.1 hUV hFU) hker
  obtain ⟨r,hr,hr2,hRr,hrQ⟩ := exists_relative_complement_involution_central_modulo
    Q R V C (hPg.to_le (show Q ≤ Pg from inf_le_left)) hRQ.le inf_le_right hQV
    hprod hdis hCne
  have hKr : K.map H.subtype ≤ centralizer ({r} : Set G) :=
    fun k hk => mem_centralizer_singleton_iff.mpr (hr.2 k hk)
  have hdomain : pushingDisplacementDomain Pg R V r = Q := by
    apply le_antisymm ((commutatorPreimage_le _ _ _).trans inf_le_left)
    apply le_commutatorPreimage (le_inf le_rfl hQV)
    rwa [commutator_comm]
  have hvanish := D.sourceOrbit_pushingUp_core_involution_displacement h hV hm hfix
    hw K hK hout e x hx r₀ hfull r hr.1 hr2 hKr hRr P hRP
  have hQR : Q ≤ R := by
    rw [←hdomain]
    exact hvanish.2.1
  exact hRQ.not_ge hQR

/-- The unresolved component-factor identification must retain Z(K): even
that full identity would now contradict the actual pushing-up witnesses. -/
theorem sourceOrbit_pushingUp_component_factor_ne
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : V = D.sourceOrbit) (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (e : (K ⧸ center K) ≃* Janko4.Model)
    (x : K) (hx : orderOf x = 3) (r₀ : G)
    (hfull : CubicPumpupFullResolution H K x r₀)
    (hjoin : (T : Subgroup G) ≤ L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (P : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L))
    (hRP : J.pCoreIn 2 ≤ (P : Subgroup _).map
      (sectionCentralizerIn (normalizer (L : Set G)) L).subtype) :
    J.pCoreIn 2 ⊓ K.map H.subtype ≠ V ⊔ (center K).map (H.subtype.comp K.subtype) := by
  intro he
  have hf := sourceOrbit_pushingUp_core_central_product hw K hK e
  have hZ := hf.2.2.symm.le.trans inf_le_right
  apply D.sourceOrbit_pushingUp_core_ne_module_sup_centralizer h hV hm hfix hw K hK hout
    e x hx r₀ hfull hjoin P hRP
  calc
    _ = (J.pCoreIn 2 ⊓ K.map H.subtype) ⊔
        (J.pCoreIn 2 ⊓ centralizer (K.map H.subtype : Set G)) := hf.1
    _ = _ := by rw [he,sup_assoc,sup_eq_right.mpr hZ]

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
/-- A literal source witness whose component intersection strictly exceeds
V together with the full covering center whenever the local join factors. -/
@[expose] def MathieuPushingUpFactorGap {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (L V A : Subgroup G) : Prop :=
  ∃ J H W : Subgroup G, Witness L V A J H W ∧
    ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
      ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype).subgroupOf H ≤ K ∧
      ∃ (_e : (K ⧸ center K) ≃* Janko4.Model) (x : K) (r : G),
        orderOf x = 3 ∧ CubicPumpupFullResolution H K x r ∧
        ((T : Subgroup G) ≤ L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 →
          V ⊔ (center K).map (H.subtype.comp K.subtype) < J.pCoreIn 2 ⊓ K.map H.subtype)
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- The full-domain contradiction forces a genuine excess over V Z(K) in
the same original component, retaining its resolved cubic and full cover. -/
theorem pushingUp_component_factor_gap
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : V = D.sourceOrbit) (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    {A : Subgroup G} (hc : MathieuPushingUpFactoredCase T L V A) :
    MathieuPushingUpFactorGap T L V A := by
  obtain ⟨J,H,W,hw,hstrict,hesc,K,hK,hn,hout,hFK,hWK,hprod,hfactor,hcontrol,
    r,H₁,hr,hCH,hrel,hn₁,hKr,e,x,hx,hqx,hmem,he,hquasi,heq,
    ⟨g,hg,hqy,hey,hdata,hs,hp,hact,hfull,hdisp,huy⟩,hux⟩ := hc
  have hy : orderOf (g * (x : K) * g⁻¹) = 3 :=
    ((MulAut.conj g).orderOf_eq (x : K)).trans ((orderOf_coe x).trans hx)
  refine ⟨J,H,W,hw,K,hK,hn,hout,hFK,e,g * (x : K) * g⁻¹,r,hy,hfull,?_⟩
  intro hjoin
  obtain ⟨P,hRP,hcent,hrest⟩ := hdisp.1
  have hne := D.sourceOrbit_pushingUp_component_factor_ne h hV hm hfix hw K hK hout
    e (g * (x : K) * g⁻¹) hy r hfull hjoin P hRP
  exact lt_of_le_of_ne (sup_le hfactor.2.2.2.1 (hfactor.2.2.1.symm.le.trans inf_le_left)) hne.symm
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Representation.BinaryOffender
universe u
variable {G : Type u} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The literal Hall actor retains every original witness and, in the
pushing-up branch, constructs the strict component-factor obstruction.
No full-domain or involution-choice callback remains in this deduction. -/
theorem sourceOrbit_mathieu_hall_factor_gap
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
    (Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M12) ∨
      Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M22) ∨
      L ⊔ (T : Subgroup G) = L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2) ∧
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
      ((MathieuPushingUpFactoredCase T L V A ∧ MathieuPushingUpFactorGap T L V A) ∨
        (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
          MathieuJankoSeedResidualCase (T : Subgroup G) L V A
            (D.orbitComponent ⧸ center D.orbitComponent))) := by
  have hsource :=
    @sourceOrbit_mathieu_hall_factored_obstruction G instG finG T L V D
      h hmany hV hm hnon H hH hlarge B hBN hHall hker
  refine ⟨hsource.1,?_⟩
  refine hsource.2.imp fun p hp => hp.imp fun A => ?_
  iterate 11 apply And.imp_right
  exact Or.imp (fun hc => ⟨hc,D.pushingUp_component_factor_gap h.toHypothesis1221 hV hm
    (D.sourceOrbit_fixed_and_thompson_of_many h hmany hnon).1 hc⟩) id
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
