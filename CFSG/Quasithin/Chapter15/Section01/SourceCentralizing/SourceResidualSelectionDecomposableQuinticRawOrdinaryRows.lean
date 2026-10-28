module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinaryActionBounds
public import CFSG.Quasithin.Chapter1.Section01.ModelActions115
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import GorensteinWalter.LinearThreeEquiv
public import GorensteinWalter.PSL2Center
public import Theory.SpecificGroups.SymmetricFourSolvable

/-!
# Remaining ordinary marked rows at the original quintic component

The faithful elementary sixteen excludes the alternating and odd-characteristic
constructors of the actual 1.1.5 action. The derived binary symplectic endpoint
is excluded through its genuine A₆ equivalence. The remaining characteristic-two
families, central two-covers and sporadic quotients retain their exact models
and the original marked automorphism. No whole-M generation, CaseI component
record, global residual control or larger-model placement is used.
-/

@[expose] public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker ClassificationModels
open Chapter1.Section02.LocalModels Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G]

/-- The retained characteristic-two models, with the derived A₆ endpoint removed. -/
def RawOrdinaryLieRows (H : Type*) [Group H] : Prop :=
  IsBenderModel H ∨
  (∃ n : ℕ, 1 ≤ n ∧ ClassicalGroup.IsPSL H 3 (2^n)) ∨
  (∃ n : ℕ, 2 ≤ n ∧ ClassicalGroup.IsPSp H 2 (2^n)) ∨
  (∃ n : ℕ, 2 ≤ n ∧ IsG2At H (2^n)) ∨
  (∃ n : ℕ, 1 ≤ n ∧ Triality.Standard.IsTrialityGroupAt (2^n) H) ∨
  (∃ m : ℕ, 1 ≤ m ∧ IsReeF4At H m) ∨
  Nonempty (H ≃* commutator (Atlas.G2.Model (ZMod 2))) ∨
  Nonempty (H ≃* Tits.ParrottGroup) ∨
  ∃ n : ℕ, (n = 4 ∨ n = 5) ∧ ClassicalGroup.IsPSL H n 2

/-- The remaining rows keep the same marked automorphism, including the exact
central two-cover and two-central sporadic action alternatives. -/
def RawOrdinaryActionRows (H : Type*) [Group H] (α : MulAut H) : Prop :=
  (IsSimpleGroup H ∧ RawOrdinaryLieRows H ∧ α ∈ (MulAut.conj (G := H)).range) ∨
  (center H ≠ ⊥ ∧ center H = pCore 2 H ∧
    (ClassicalGroup.IsPSL (H ⧸ pCore 2 H) 3 4 ∨ IsG2At (H ⧸ pCore 2 H) 4) ∧
    α ∈ (MulAut.conj (G := H)).range) ∨
  ∃ name : SporadicName, name ≠ .j3 ∧
    Nonempty ((H ⧸ pCore 2 H) ≃* name.Carrier) ∧ TwoCentralInner α

private def coreQuotientEquivOfCenterless
    {H X : Type*} [Group H] [Finite H] [Group X] [Finite X]
    (hc : center H = pCore 2 H) (e : H ≃* X) (hz : center X = ⊥) :
    (H ⧸ pCore 2 H) ≃* X := by
  have hb : pCore 2 H = ⊥ := by
    rw [←hc]
    apply (eq_bot_iff_card _).mpr
    rw [Nat.card_congr (centerCongr e).toEquiv,hz,card_bot]
  exact ((QuotientGroup.quotientMulEquivOfEq hb).trans QuotientGroup.quotientBot).trans e

private theorem no_alternating_action
    {H : Type*} [Group H] [Finite H] (hc : center H = pCore 2 H)
    {α : MulAut H} {n : ℕ} (hn : 4 ≤ n)
    (hnot : ¬ Nonempty ((H ⧸ pCore 2 H) ≃* alternatingGroup (Fin n)))
    (σ : Equiv.Perm (Fin n)) : ¬ AlternatingAction α n σ := by
  rintro (⟨e,_⟩ | ⟨_,⟨e⟩,_⟩)
  · exact hnot ⟨coreQuotientEquivOfCenterless hc e
      (alternatingGroup.center_eq_bot (by simpa using hn))⟩
  · have hcard : Nat.card (center H) = 3 := by simpa using Nat.card_congr e.toEquiv
    have hp : IsPGroup 2 (center H) := hc ▸ pCore_isPGroup
    rcases hp.card_eq_or_dvd with h1 | h2
    · omega
    · norm_num [hcard] at h2

private theorem primePSLEquiv
    {H : Type*} [Group H] {n p : ℕ} (hp : p.Prime)
    (hm : ClassicalGroup.IsPSL H n p) : Nonempty (H ≃* PSL(n,ZMod p)) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F,_,_,hc,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let k : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hc)
  exact ⟨e.trans (Atlas.fieldEquivPSL n k)⟩

private theorem no_odd_model
    {H : Type*} [Group H] [Finite H] [IsQuasisimple H]
    (hc : center H = pCore 2 H)
    (hthree : ¬ Nonempty ((H ⧸ pCore 2 H) ≃* Matrix.PSL3Three.PSL))
    (hprime : ∀ p : ℕ, p.Prime → 3 < p →
      ¬ Nonempty ((H ⧸ pCore 2 H) ≃* PSL(2,ZMod p))) :
    ¬ (ClassicalGroup.IsPSL H 3 3 ∨
      ∃ p : ℕ, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL H 2 p) := by
  rintro (hm | ⟨p,hp,hm⟩)
  · obtain ⟨e⟩ := primePSLEquiv Nat.prime_three hm
    exact hthree ⟨coreQuotientEquivOfCenterless hc e
      Matrix.PSL3Three.GraphWitnesses.EightCentralizers.psl_center_eq_bot⟩
  · have hne : p ≠ 2 := by
      rintro rfl
      rcases hp.2 with ⟨a,ha⟩ | ⟨a,ha⟩
      · have hlow : 2 ≤ 2 ^ (2 ^ a) := Nat.le_pow (by norm_num)
        omega
      · have hd : 2 ∣ 2 ^ a := dvd_pow_self _ (by rintro rfl; norm_num at ha)
        omega
    have hlo := hp.1.two_le
    let : Fact p.Prime := ⟨hp.1⟩
    obtain ⟨e⟩ := primePSLEquiv hp.1 hm
    by_cases he : p = 3
    · subst p
      let f := e.trans GorensteinWalter.psl2_three_equiv_alternatingGroup
      let : Nontrivial H := f.toEquiv.nontrivial
      let : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup_fin_four_isSolvable
      exact Group.IsPerfect.not_isSolvable H
        (Group.isSolvable_of_isSolvable_injective (f := f.toMonoidHom) f.injective)
    · exact hprime p hp.1 (by omega)
        ⟨coreQuotientEquivOfCenterless hc e (GorensteinWalter.psl2_center_eq_bot _)⟩

private theorem remaining_rows
    {H : Type*} [Group H] [Finite H] [IsQuasisimple H]
    (hc : center H = pCore 2 H)
    (h6 : ¬ Nonempty ((H ⧸ pCore 2 H) ≃* alternatingGroup (Fin 6)))
    (h7 : ¬ Nonempty ((H ⧸ pCore 2 H) ≃* alternatingGroup (Fin 7)))
    (hthree : ¬ Nonempty ((H ⧸ pCore 2 H) ≃* Matrix.PSL3Three.PSL))
    (hprime : ∀ p : ℕ, p.Prime → 3 < p →
      ¬ Nonempty ((H ⧸ pCore 2 H) ≃* PSL(2,ZMod p)))
    {α : MulAut H} (hm : ModelAction115 H α) : RawOrdinaryActionRows H α := by
  cases hm with
  | lie hs hm hi =>
      refine Or.inl ⟨hs,?_,hi⟩
      rcases hm with hB | hr | h45
      · exact Or.inl hB
      · cases hr with
        | linear n hn hm => exact Or.inr (Or.inl ⟨n,hn,hm⟩)
        | symplectic n hn hm => exact Or.inr (Or.inr (Or.inl ⟨n,hn,hm⟩))
        | g2 n hn hm => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n,hn,hm⟩)))
        | triality n hn hm => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n,hn,hm⟩))))
        | ree n hn hm => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n,hn,hm⟩)))))
        | symplectic_derived hm =>
            obtain ⟨e⟩ := hm
            exact (h6 ⟨coreQuotientEquivOfCenterless hc
              (e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)
              (alternatingGroup.center_eq_bot (by simp))⟩).elim
        | g2_derived hm => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm))))))
        | tits hm => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h45)))))))
  | two_cover hn hc hm hi => exact Or.inr (Or.inl ⟨hn,hc,hm,hi⟩)
  | six σ _ ha => exact (no_alternating_action hc (by decide) h6 σ ha).elim
  | seven σ _ ha => exact (no_alternating_action hc (by decide) h7 σ ha).elim
  | odd hm _ => exact (no_odd_model hc hthree hprime hm).elim
  | sporadic name hn hm ha => exact Or.inr (Or.inr ⟨name,hn,hm,ha⟩)

/-- Every retained actual action is inner; the sporadic row retains the
stronger two-central inner action in its own constructor. -/
theorem RawOrdinaryActionRows.inner {H : Type*} [Group H] {α : MulAut H}
    (h : RawOrdinaryActionRows H α) : α ∈ (MulAut.conj (G := H)).range := by
  rcases h with ⟨_,_,hi⟩ | ⟨_,_,_,hi⟩ | ⟨_,_,_,hi⟩
  · exact hi
  · exact hi
  · exact hi.1

/-- Exhaust the marked action list at the same original raw ordinary quintic
component, using its actual faithful sixteen rather than whole-M generation. -/
theorem PreparedChosenModule.decomposable_five_raw_ordinary_rows
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      let Z1 := thompsonPlane T V (c.ambientFactor d s.first).space
      let G1 := centralizer (Z1 : Set G)
      let C := M ⊓ G1
      let R := (pResidual 2 C).map C.subtype
      ∀ {L : Subgroup G}, L ≤ G1 → IsComponent G1 (L.subgroupOf G1) →
        center L = pCore 2 L →
        R ⊔ ⁅V,R⁆ ≤ normalizer (L : Set G) → ⁅L,⁅V,R⁆⁆ ≠ ⊥ →
        ∀ {α : MulAut L}, ModelAction115 L α → RawOrdinaryActionRows L α := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive Z1 G1 C R L hLG hLc hcenter hnL hmove α hm
  obtain ⟨h6,h7,hthree,hprime⟩ := h.decomposable_five_raw_ordinary_small_quotients
    hG T hempty hM hmany hJ hfull c d hd s π hp hs hdec hq hfive
    hLG hLc hcenter hnL hmove
  let := hLc.2
  let := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLG)
  exact remaining_rows hcenter h6 h7 hthree hprime hm

end CFSG.Quasithin.Chapter15.Section01
