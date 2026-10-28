module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.AmbientAction
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.ModelExclusions
public import Theory.SpecificGroups.OddThreeSectionRank
public import Theory.Mathieu.TwoRankLower
public import Theory.SpecificGroups.FiniteModelTwoRank
public import Theory.SpecificGroups.PSL4.FermatSeven
public import Theory.SpecificGroups.FiniteModelFiveRank
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.TwoRankCoarse
public import Theory.SpecificGroups.Rudvalis.Model.Order
public import Theory.SpecificGroups.Held.OddOrderBound
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.PairBound

/-!
# Actual quotient models for the original cubic pumpup

The full M₂₂ fixed component supplies order divisibility and a literal
central-quotient section. These exclude the small alternating and binary
linear/symplectic rows, all binary rank-one rows, odd PSL₂/PSL₃/PSU₃,
and Fermat PSL₄. The involution tables and order calculations reduce the
sporadic list to McL. The remaining odd and binary rank-two models retain
the source's field parameters and actual multiplicative equivalences.

We apply this comparison to the original residual's odd-E orbit inside
C_G(x) and then to the literal Hall obstruction. A trivial induced action
still gives only the M₂₂ quotient: equality of the residual and its containing
two-component, the remaining model exclusions, the pushing-up contradiction,
and the M₂₄ fixed-line and odd-actor comparisons are not asserted here.

Source: Aschbacher--Smith A.2.3 and 4.2.13, printed pp.33 and 612;
the Hall application is 4.4.14, printed pp.623--625.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin Sporadic.Mathieu
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open ChapterA.Section02 ClassificationModels
open Chapter4.Section02.RankOneReciprocalEscape

private theorem cover_card_dvd {B Q : Type*} [Group B] [Group Q]
    (e : (B ⧸ center B) ≃* M22) (f : B →* Q) (hf : Function.Injective f) :
    Nat.card M22 ∣ Nat.card Q := by
  rw [←Nat.card_congr e.toEquiv]
  exact (card_quotient_dvd_card _).trans (card_dvd_of_injective f hf)

private theorem no_alternating_cover {Q B : Type*} [Group Q] [Group B]
    (eB : (B ⧸ center B) ≃* M22) (f : B →* Q) (hf : Function.Injective f)
    {n : ℕ} (hn : n ≤ 9) (e : Q ≃* alternatingGroup (Fin n)) : False := by
  have hd : 11 ∣ Nat.card Q := (by rw [m22_order]; decide : 11 ∣ Nat.card M22).trans
    (cover_card_dvd eB f hf)
  rw [Nat.card_congr e.toEquiv] at hd
  have hp := (alternatingGroup (Fin n)).card_subgroup_dvd_card
  rw [Nat.card_perm,Nat.card_fin] at hp
  have hh := hd.trans (hp.trans (Nat.factorial_dvd_factorial hn))
  norm_num [Nat.factorial] at hh

private theorem no_binary_linear_cover {Q B : Type*} [Group Q] [Group B]
    (eB : (B ⧸ center B) ≃* M22) (f : B →* Q) (hf : Function.Injective f)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (hm : ClassicalGroup.IsPSL Q n 2) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let ef : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  let a := e.trans (Atlas.fieldEquivPSL n ef)
  have hd : 11 ∣ Nat.card Q := (by rw [m22_order]; decide : 11 ∣ Nat.card M22).trans
    (cover_card_dvd eB f hf)
  rw [Nat.card_congr a.toEquiv] at hd
  have hs := hd.trans (card_quotient_dvd_card (center (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))))
  have hgl := hs.trans (card_dvd_of_injective Matrix.SpecialLinearGroup.toGL
    Matrix.SpecialLinearGroup.toGL_injective)
  rcases hn with rfl | rfl
  all_goals
    rw [Matrix.card_GL_field,ZMod.card] at hgl
    norm_num [Fin.prod_univ_succ] at hgl

private theorem no_fermat_linear_four_cover {Q B : Type*} [Group Q] [Group B]
    (eB : (B ⧸ center B) ≃* M22) (f : B →* Q) (hf : Function.Injective f)
    {r : ℕ} (hr : ∃ k : ℕ, r = 2 ^ (2 ^ k) + 1)
    (hm : ClassicalGroup.IsPSL Q 4 r) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  have hd : 7 ∣ Nat.card Q := (by rw [m22_order]; decide : 7 ∣ Nat.card M22).trans
    (cover_card_dvd eB f hf)
  rw [Nat.card_congr e.toEquiv] at hd
  exact Theory.SpecificGroups.PSL4.fermat_seven_not_dvd hr hF hd

private theorem no_binary_symplectic_cover {Q B : Type*} [Group Q] [Group B]
    (eB : (B ⧸ center B) ≃* M22) (f : B →* Q) (hf : Function.Injective f)
    (hm : ClassicalGroup.IsPSp Q 3 2) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  have hd : 11 ∣ Nat.card Q := (by rw [m22_order]; decide : 11 ∣ Nat.card M22).trans
    (cover_card_dvd eB f hf)
  rw [Nat.card_congr e.toEquiv] at hd
  have hs := hd.trans (card_quotient_dvd_card (center (Theory.SpecificGroups.SymplecticSix.Sp F)))
  rw [Theory.SpecificGroups.SymplecticSix.card_sp_of_card_two hF] at hs
  norm_num at hs

private theorem no_held_cover {B : Type*} [Group B]
    (eB : (B ⧸ center B) ≃* M22) (f : B →* Held.He) (hf : Function.Injective f) : False := by
  have hg := Held.NormalizerGraph.Orbital.held_le_preservingGroup
  have hHe := Held.OddOrderBound.card_dvd_of_graph_and_pair_bound hg
    (Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.pairStabilizer_card_dvd hg)
  have hd := (cover_card_dvd eB f hf).trans hHe
  rw [m22_order] at hd
  norm_num at hd

/-- Every sporadic B row with a fixed M₂₂ covering component is McL.
The component embedding is literal; no subgroup catalogue is assumed. -/
theorem m22_fixed_component_sporadic_remaining
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q] [Group.IsPerfect Q]
    (a : MulAut Q) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B)
    (eB : (B ⧸ center B) ≃* M22) (hm : IsTheoremBSporadicModel Q) :
    Nonempty (Q ≃* _root_.Sporadic.LeechRelated.McL.Carrier) := by
  let f := a.fixedSubgroup.subtype.comp B.subtype
  have hf : Function.Injective f := a.fixedSubgroup.subtype_injective.comp B.subtype_injective
  have hd := cover_card_dvd eB f hf
  have hex := m22_fixed_component_excludes_large_sporadic a ha B hB eB
  rcases hm with ⟨name,⟨e⟩⟩ | hm
  · cases name with
    | m11 =>
      rw [Nat.card_congr e.toEquiv] at hd
      change Nat.card M22 ∣ Nat.card M11 at hd
      rw [m11_order,m22_order] at hd
      norm_num at hd
    | m12 =>
      rw [Nat.card_congr e.toEquiv] at hd
      change Nat.card M22 ∣ Nat.card M12 at hd
      rw [m12_order,m22_order] at hd
      norm_num at hd
    | m22 => exact (hex (Or.inl ⟨e⟩)).elim
    | m23 => exact (hex (Or.inr (Or.inl ⟨e⟩))).elim
    | m24 => exact (hex (Or.inr (Or.inr (Or.inl ⟨e⟩)))).elim
    | j2 =>
      rw [Nat.card_congr e.toEquiv] at hd
      change Nat.card M22 ∣ Nat.card _root_.Sporadic.LeechRelated.J2.Carrier at hd
      rw [_root_.Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier,
        m22_order] at hd
      norm_num at hd
    | j3 =>
      rw [Nat.card_congr e.toEquiv] at hd
      change Nat.card M22 ∣ Nat.card _root_.Sporadic.Janko3.Model at hd
      rw [_root_.Sporadic.Janko3.model_card,m22_order] at hd
      norm_num at hd
    | j4 => exact (hex (Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩))))).elim
    | hs => exact (hex (Or.inr (Or.inr (Or.inr (Or.inr ⟨e⟩))))).elim
    | he => exact (no_held_cover eB (e.toMonoidHom.comp f) (e.injective.comp hf)).elim
    | ru =>
      rw [Nat.card_congr e.toEquiv] at hd
      change Nat.card M22 ∣ Nat.card Rudvalis.Model at hd
      rw [Rudvalis.model_card,m22_order] at hd
      norm_num at hd
  · rcases hm with hj | hm
    · obtain ⟨e⟩ := hj
      rw [Nat.card_congr e.toEquiv,Janko1.card_model,m22_order] at hd
      norm_num at hd
    · exact hm

private theorem no_cover_of_section_rank {Q B : Type*} [Group Q] [Group B]
    (eB : (B ⧸ center B) ≃* M22) (f : B →* Q) (hf : Function.Injective f)
    (hr : ∀ P : Subgroup Q, primeRank 2 (P ⧸ center P) ≤ 3) : False := by
  have hh := hr f.range
  let e := ((centerQuotientCongr (MonoidHom.ofInjective hf)).symm).trans eB
  let : Finite (f.range ⧸ center f.range) := Finite.of_equiv M22 e.symm.toEquiv
  rw [primeRank_equiv 2 e] at hh
  have hl := m22_four_le_twoRank
  omega

/-- A full M₂₂ cover cannot embed in odd-field PSL₃ or PSU₃: its literal
central quotient contradicts the section two-rank bound three. -/
theorem m22_cover_not_odd_ternary {Q B : Type*} [Group Q] [Group B]
    (eB : (B ⧸ center B) ≃* M22) (f : B →* Q) (hf : Function.Injective f)
    {q : ℕ} (hq : Odd q) :
    ¬ (ClassicalGroup.IsPSL Q 3 q ∨ ClassicalGroup.IsPSU Q 3 q) := by
  rintro (⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,J,hF,_,⟨e⟩⟩)
  · exact no_cover_of_section_rank eB (e.toMonoidHom.comp f) (e.injective.comp hf)
      (fun P => Theory.SpecificGroups.OddThreeSectionRank.psl3_subgroup_quotient_twoRank_le_three
        (hF.symm ▸ hq) P (center P))
  · exact no_cover_of_section_rank eB (e.toMonoidHom.comp f) (e.injective.comp hf)
      (fun P => Theory.SpecificGroups.OddThreeSectionRank.psu3_subgroup_quotient_twoRank_le_three
        J (hF.symm ▸ hq.pow) P (center P))

/-- The remaining actual Theorem B models for an involution fixed M₂₂ cover.
The odd-field unitary row retains the source's exact restriction;
all binary rank-one, odd PSL₂, odd ternary and Fermat PSL₄ rows are excluded. -/
@[expose] def M22PumpupRemainingModel (Q : Type*) [Group Q] : Prop :=
  (∃ p : ℕ, p.Prime ∧ Odd p ∧
    (ClassicalGroup.IsPSp Q 2 p ∨ IsG2At Q p)) ∨
  (∃ s : ℕ, s.Prime ∧ (∃ b : ℕ, s + 1 = 2 ^ b) ∧
    ClassicalGroup.IsPSU Q 4 s) ∨
  (∃ f, IsRankTwoModel Q f) ∨
    Nonempty (Q ≃* _root_.Sporadic.LeechRelated.McL.Carrier)

/-- The literal fixed-component comparison removes the alternating, binary
linear, binary symplectic, rank-one, odd ternary, Fermat PSL₄ and twelve sporadic rows.
This is a reduction to the displayed remaining models, not their exclusion. -/
theorem m22_fixed_component_theoremB_remaining
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q] [Group.IsPerfect Q]
    (a : MulAut Q) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B)
    (eB : (B ⧸ center B) ≃* M22) (hm : IsTheoremBModel Q) :
    M22PumpupRemainingModel Q := by
  let f := a.fixedSubgroup.subtype.comp B.subtype
  have hf : Function.Injective f := a.fixedSubgroup.subtype_injective.comp B.subtype_injective
  cases hm with
  | alternating n hn iso => exact (no_alternating_cover eB f hf hn iso.some).elim
  | odd h =>
    cases h with
    | linear_two q hq iso => exact (m22_cover_not_odd_linear_two eB f hf hq iso).elim
    | linear_three p n hp ho hn iso =>
      exact (m22_cover_not_odd_ternary eB f hf ho.pow (Or.inl iso)).elim
    | unitary_three p n hp ho hn iso =>
      exact (m22_cover_not_odd_ternary eB f hf ho.pow (Or.inr iso)).elim
    | symplectic p hp ho iso => exact Or.inl ⟨p,hp,ho,Or.inl iso⟩
    | g2 p hp ho iso => exact Or.inl ⟨p,hp,ho,Or.inr iso⟩
    | linear_four r hp hr iso => exact (no_fermat_linear_four_cover eB f hf hr iso).elim
    | unitary_four s hp hs iso => exact Or.inr (Or.inl ⟨s,hp,hs,iso⟩)
  | bender h => exact (m22_cover_not_bender eB f hf h).elim
  | rank_two n h => exact Or.inr (Or.inr (Or.inl ⟨n,h⟩))
  | linear_binary n hn h => exact (no_binary_linear_cover eB f hf hn h).elim
  | symplectic_binary h => exact (no_binary_symplectic_cover eB f hf h).elim
  | sporadic h => exact Or.inr (Or.inr (Or.inr
      (m22_fixed_component_sporadic_remaining a ha B hB eB h)))
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration


namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open ChapterA.Section02

/-- Proper containment leaves either a trivial quotient action and the actual
M₂₂ quotient, or one of the surviving models for a nontrivial action. -/
theorem m22_pumpup_model_comparison
    {G : Type*} [Group G] [Finite G]
    (t : G) (D X : Subgroup G) (hX : X.IsTwoComponent)
    (hm : IsTheoremBModel (X ⧸ oddTwoCore X))
    (ha : M22PumpupQuotientActionData t D X) :
    D = X ∨ Nonempty ((X ⧸ oddTwoCore X) ≃* M22) ∨
      M22PumpupRemainingModel (X ⧸ oddTwoCore X) := by
  rcases ha with he | ⟨hn,ha,B,hB,eB,hmap,hE,⟨eE⟩,hcase⟩
  · exact Or.inl he
  let := hn
  let : IsSimpleGroup (X ⧸ oddTwoCore X) := hX.isSimpleGroup_quotient_oddTwoCore
  let := hX.1.perfect
  let : Group.IsPerfect (X ⧸ oddTwoCore X) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  rcases hcase with ⟨_,he⟩ | ⟨hb,_⟩
  · exact Or.inr (Or.inl he)
  · exact Or.inr (Or.inr (m22_fixed_component_theoremB_remaining _ hb _ hE eE hm))

/-- The literal original residual, its actual odd-E orbit and the remaining
quotient alternatives. This does not assert equality from a quotient marking. -/
@[expose] def CubicPumpupModelComparison {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (K : Subgroup H) (x : K) : Prop :=
  let Cx := centralizer ({((x : H) : G)} : Set G)
  let D := (cubicResidualImage H K x).subgroupOf Cx
  let X := componentOrbit D (oddELayer Cx)
  D = X ∨ Nonempty ((X ⧸ oddTwoCore X) ≃* M22) ∨
    M22PumpupRemainingModel (X ⧸ oddTwoCore X)

/-- Apply the model exclusions to the same cubic, involution and containing
component already supplied by the source configuration. -/
theorem cubic_pumpup_model_comparison {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (K : Subgroup H) (x : K) (r : G)
    (hp : CubicPumpupData H K x r) (ha : CubicPumpupQuotientAction H K x r) :
    CubicPumpupModelComparison H K x := by
  obtain ⟨hrx,hX,_,_,_,hm,_⟩ := hp
  obtain ⟨hrx',ha⟩ := ha
  let Cx := centralizer ({((x : H) : G)} : Set G)
  let D := (cubicResidualImage H K x).subgroupOf Cx
  let X := componentOrbit D (oddELayer Cx)
  exact m22_pumpup_model_comparison (G := Cx) (⟨r,hrx'⟩ : Cx) D X hX hm ha
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open Janko4.InvolutionCentralizers

/-- The original full source configuration after finite and rank-one model exclusion.
The original residual, full covering component and all quotient maps are retained. -/
@[expose] def MathieuPushingUpModelComparisonCase {G : Type*} [Group G] [Finite G]
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
              CubicPumpupQuotientAction H K y (r : G) ∧
              CubicPumpupModelComparison H K y ∧
              ∀ Q : Subgroup (centralizer ({y} : Set K)), Q.IsCComponent →
                Q = solvableResidual (centralizer ({y} : Set K))) ∧
          ∀ Q : Subgroup (Subgroup.centralizer ({(x : K)} : Set K)), Q.IsCComponent →
            Q = solvableResidual (Subgroup.centralizer ({(x : K)} : Set K))


/-- Exclude the finite and rank-one quotient rows on the unique containing
two-component of the same placed cubic and reselected involution. -/
theorem pushingUp_cubic_model_comparison {G : Type*} [Group G] [Finite G]
    {L V A : Subgroup G} (hc : MathieuPushingUpQuotientActionCase L V A) :
    MathieuPushingUpModelComparisonCase L V A := by
  obtain ⟨J,H,W,hw,hesc,K,hK,hn,hout,hFK,hWK,hprod,r,H₁,hr,hCH,hrel,hn₁,hKr,
    e,x,hx,hqx,hmem,he,hquasi,heq,⟨g,hg,hqy,hey,hdata,hs,hp,hact,huy⟩,hux⟩ := hc
  have hm := cubic_pumpup_model_comparison H K (g * (x : K) * g⁻¹) (r : G) hp hact
  exact ⟨J,H,W,hw,hesc,K,hK,hn,hout,hFK,hWK,hprod,r,H₁,hr,hCH,hrel,hn₁,hKr,
    e,x,hx,hqx,hmem,he,hquasi,heq,⟨g,hg,hqy,hey,hdata,hs,hp,hact,hm,huy⟩,hux⟩
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

/-- The literal Hall obstruction excludes the finite and rank-one models on
the original cubic pumpup. The full cover, quotient maps and all original
Hall hypotheses are retained; no model-exclusion premise is added. -/
theorem sourceOrbit_mathieu_hall_model_comparison_obstruction
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
      (MathieuPushingUpModelComparisonCase L V A ∨
        (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
          MathieuJankoSeedResidualCase (T : Subgroup G) L V A
            (D.orbitComponent ⧸ center D.orbitComponent))) := by
  have hsource :=
    @sourceOrbit_mathieu_hall_quotient_action_obstruction G instG finG T L V D
      h hmany hV hm hnon H hH hlarge B hBN hHall hker
  refine hsource.imp fun p hp => hp.imp fun A => ?_
  iterate 11 apply And.imp_right
  exact Or.imp (@pushingUp_cubic_model_comparison G instG finG L V A) id

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
