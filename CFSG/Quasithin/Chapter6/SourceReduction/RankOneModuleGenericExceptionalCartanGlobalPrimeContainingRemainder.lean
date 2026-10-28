module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowMathieuCover
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Complete
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete

/-!
# Remaining containing components at the smaller changed Sylow

Apply the proved A.3.6 classification to the literal containing image in
X/O₂(X), where X = G₀T₀. Transport the already proved model exclusions
through the intrinsic two-core quotient equivalence. This leaves J₄, odd-prime
ternary simple groups and their cubic covers, and the two noncentral-Fitting
alternatives. Retain the full common A.3.6 assertions and covering data.

The construction uses the same selected right factor, both Hall markings,
relative component normality and strict quotient inclusion. It reduces the
containing catalogue; it does not discharge these remaining source cases.
Source: Aschbacher–Smith A.3.6, pp.43–45, and 5.2.2, pp.648–649.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open Chapter1.Section02 LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- The unresolved A.3.6 rows on the literal containing image, retaining
its central covering data and the full noncentral-Fitting alternatives. -/
@[expose] def RemainingSourceContainer (X K : Subgroup G) : Prop :=
  let I := (K.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
  A36Common I ∧
    ((IsComponent (X ⧸ pCore 2 X) I ∧ IsSimpleGroup I ∧ (Nonempty (I ≃* Janko4.Model) ∨
      ∃ q : ℕ, q.Prime ∧ Odd q ∧ ∃ u : Bool, IsPSLSign I u 3 q)) ∨
    (IsComponent (X ⧸ pCore 2 X) I ∧
      Nonempty (center I ≃* Multiplicative (ZMod 3)) ∧
      ∃ q : ℕ, q.Prime ∧ Odd q ∧ ∃ u : Bool, IsSLSign I u 3 q) ∨
    A36Natural I ∨ A36Nilpotent I)

private structure ContainingExclusions (Q : Type*) [Group Q] : Prop where
  bender : ¬ ClassificationModels.IsBenderModel Q
  rankTwo : ¬ RankTwoTheoremC Q
  alternating : ∀ m : ℕ, 5 ≤ m → m ≤ 8 → ¬ IsAlternating Q m
  binary : ∀ m : ℕ, m = 4 ∨ m = 5 → ¬ ClassicalGroup.IsPSL Q m 2
  odd : ∀ q k : ℕ, q.Prime → Odd q → (k = 1 ∨ k = 2) →
    ¬ ClassicalGroup.IsPSL Q 2 (q^k)
  ternary : ∀ k : ℕ, 1 ≤ k → ¬ (ClassicalGroup.IsPSL Q 3 (2^k) ∨
    IsSL Q 3 (2^k) ∨ IsSU Q 3 (2^k))
  sporadic : ∀ s : ClassificationModels.SporadicName, s ≠ .j3 → s ≠ .j4 →
    ¬ Nonempty (Q ≃* s.Carrier)
  jankoOne : ¬ Nonempty (Q ≃* Janko1.Model)
  sixCover : ¬ IsAlternatingCover Q 6
  sevenCover : ¬ IsAlternatingCover Q 7
  mathieuCover : ¬ IsM22Cover Q

private theorem sl_transport {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) {m q : ℕ} (h : IsSL X m q) : IsSL Y m q := by
  obtain ⟨F,_,_,hF,⟨a⟩⟩ := h
  exact ⟨F,inferInstance,inferInstance,hF,⟨e.symm.trans a⟩⟩

private theorem su_transport {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) {m q : ℕ} (h : IsSU X m q) : IsSU Y m q := by
  obtain ⟨F,_,_,J,hF,hc,⟨a⟩⟩ := h
  exact ⟨F,inferInstance,inferInstance,J,hF,hc,⟨e.symm.trans a⟩⟩

private theorem cover_transport {X Y : Type*} {S : Type} [Group X] [Group Y] [Group S]
    (e : X ≃* Y) (h : IsThreeCover X S) : IsThreeCover Y S := by
  let := h.1
  refine ⟨IsQuasisimple.of_mulEquiv e,
    ⟨(centerCongr e.symm).trans h.2.1.some⟩,?_⟩
  exact ⟨(QuotientGroup.congr _ _ e.symm (map_center_equiv e.symm)).trans h.2.2.some⟩

private theorem rankTwo_transport {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (h : RankTwoTheoremC X) : RankTwoTheoremC Y := by
  cases h with
  | linear f hf hm => exact .linear f hf (hm.of_mulEquiv e.symm)
  | symplectic f hf hm => exact .symplectic f hf (hm.of_mulEquiv e.symm)
  | g2 f hf hm =>
    obtain ⟨F,_,_,hc,⟨a⟩⟩ := hm
    exact .g2 f hf ⟨F,inferInstance,inferInstance,hc,⟨e.symm.trans a⟩⟩
  | triality f hf hm => exact .triality f hf (hm.of_mulEquiv e.symm)
  | ree m hm hmodel =>
    obtain ⟨d,⟨a⟩⟩ := hmodel
    exact .ree m hm ⟨d,⟨e.symm.trans a⟩⟩
  | symplectic_derived h => exact .symplectic_derived ⟨e.symm.trans h.some⟩
  | g2_derived h => exact .g2_derived ⟨e.symm.trans h.some⟩
  | tits h => exact .tits ⟨e.symm.trans h.some⟩

private theorem remaining_of_exclusions
    {X K : Subgroup G} (hQ : IsSQTK KnownSimple.IsKnownSimple (X ⧸ pCore 2 X))
    (hKX : K ≤ X) (hK : (K.subgroupOf X).IsCComponent)
    (hx : ContainingExclusions (K ⧸ pCore 2 K)) : RemainingSourceContainer X K := by
  let I := (K.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
  let : Group.IsNilpotent (pCore 2 X) := pCore_isNilpotent
  let ec := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKX)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKX))
  let e : I ≃* (K ⧸ pCore 2 K) := (cComponentTwoCoreQuotientEquiv hK).symm.trans ec
  obtain ⟨ha,hcommon⟩ := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    _ hQ (pCore_quotient_pCore_eq_bot 2) I (hK.map_quotient _)
  refine ⟨hcommon,?_⟩
  cases ha with
  | natural hn => exact .inr (.inr (.inl hn))
  | nilpotent hn => exact .inr (.inr (.inr hn))
  | simple hc hs hm =>
    apply Or.inl
    refine ⟨hc,hs,?_⟩
    cases hm with
    | alternating m hm h =>
      exact (hx.alternating m hm.1 hm.2 ⟨e.symm.trans h.some⟩).elim
    | linear_odd q k hq ho hk _ h => exact (hx.odd q k hq ho hk (h.of_mulEquiv e.symm)).elim
    | three_odd q hq ho u h => exact .inr ⟨q,hq,ho,u,h⟩
    | rank_one h => exact (hx.bender (h.of_mulEquiv e.symm)).elim
    | rank_two h => exact (hx.rankTwo (rankTwo_transport e h)).elim
    | binary_linear m hm h => exact (hx.binary m hm (h.of_mulEquiv e.symm)).elim
    | sporadic s hn h =>
      by_cases he : s = .j4
      · subst s
        exact .inl h
      · exact (hx.sporadic s hn he ⟨e.symm.trans h.some⟩).elim
    | janko_one h => exact (hx.jankoOne ⟨e.symm.trans h.some⟩).elim
  | cover hc hz hm =>
    apply Or.inr
    apply Or.inl
    refine ⟨hc,hz,?_⟩
    cases hm with
    | alternating_six h => exact (hx.sixCover (cover_transport e h)).elim
    | alternating_seven h => exact (hx.sevenCover (cover_transport e h)).elim
    | mathieu h => exact (hx.mathieuCover (cover_transport e h)).elim
    | classical u q hq h =>
      rcases hq with ⟨k,hk,rfl,_⟩ | ⟨hq,ho⟩
      · exfalso
        apply hx.ternary k hk
        cases u
        · exact .inr (.inl (sl_transport e h))
        · exact .inr (.inr (su_transport e h))
      · exact ⟨q,hq,ho,u,h⟩

/-- Exhaust the genuine A.3.6 catalogue on the same selected source pair.
The remaining alternatives keep the literal containing image and its Fitting data. -/
theorem source_prime_pair_containing_remainder
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    ∃ R : Subgroup G, LocalData T L H B D R ∧ SelectedSourceModels H R ∧
      (((generated L H D R).pCoreIn 2 = ⊥ ∧
        ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H)) ∨
       ((generated L H D R).pCoreIn 2 ≠ ⊥ ∧
        ¬ D ≤ normalizer (R : Set G) ∧
        (normalizingSylow T R).relIndex (T : Subgroup G) = 2 ∧
        (ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 → p = 5 ∧ n ≠ 2) ∧
        ∃ P : Sylow 2 (extension T L H B D R),
          let T₁ := (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype
          normalizingSylow T R ≤ T₁ ∧
          T₁ ≤ normalizer ((D ⊔ normalizingSylow T R : Subgroup G) : Set G) ∧
          ((T₁ = normalizingSylow T R ∧
            let X := generated L H D R ⊔ normalizingSylow T R
            let q := QuotientGroup.mk' (pCore 2 X)
            ∃ K : Subgroup G, R < K ∧ K ≤ X ∧
              (K.subgroupOf X).IsCComponent ∧ (K.subgroupOf X).Normal ∧
              (R.subgroupOf X).map q < (K.subgroupOf X).map q ∧
              RemainingSourceContainer X K) ∨
            ∃ U : Sylow 2 G, (U : Subgroup G) = T₁))) := by
  obtain ⟨R,d,hs,hcases⟩ :=
    source_prime_pair_mathieu_cover_containing_exclusion h hH hgen hthree c hd
  refine ⟨R,d,hs,?_⟩
  rcases hcases with hz | ⟨hz,hD,hi,hA5,P,hTP,hDT,hcases⟩
  · exact .inl hz
  refine .inr ⟨hz,hD,hi,hA5,P,hTP,hDT,?_⟩
  rcases hcases with ⟨he,K,hRK,hKX,hK,hKn,hlt,hb,hsmall,hternary,hrank,
    hj,h25,hseven,hprime,hbinary,hodd,hm11,hm12,hm,hj2,hhs,hru,hheld,hcover⟩ | ha
  · refine .inl ⟨he,K,hRK,hKX,hK,hKn,hlt,?_⟩
    let X := generated L H D R ⊔ normalizingSylow T R
    have hQX := (Chapter3.sqtk_of_mem_H h.qtke
      (d.extension_core_ne_bot hz)).subgroup (X.subgroupOf (extension T L H B D R))
    have hQ : IsSQTK KnownSimple.IsKnownSimple X :=
      (IsSQTK.equiv (subgroupOfEquivOfLe (show X ≤ extension T L H B D R from le_sup_left))).mp hQX
    have hQbar : IsSQTK KnownSimple.IsKnownSimple (X ⧸ pCore 2 X) := by
      refine ⟨?_,hQ.isKGroup.quotient _⟩
      intro q hq ho
      let : Fact q.Prime := ⟨hq⟩
      exact (primeRank_quotient_le_of_isTwoGroup q ho (pCore 2 X) pCore_isPGroup).trans
        (hQ.stronglyQuasithin q hq ho)
    apply remaining_of_exclusions hQbar hKX hK
    refine ⟨hb,hrank,?_,?_,hodd,hternary,?_,hj,
      fun hh => hsmall (.inr (.inr hh)), fun hh => hseven (.inr hh),hcover⟩
    · intro m hlo hhi hh
      interval_cases m
      · exact hsmall (.inl hh)
      · exact hsmall (.inr (.inl hh))
      · exact hseven (.inl hh)
      · exact hbinary (.inr (.inr hh))
    · intro m he hh
      rcases he with rfl | rfl
      · exact hbinary (.inl hh)
      · exact hbinary (.inr (.inl hh))
    · intro s h3 h4 hh
      cases s with
      | m11 => exact hm11 hh
      | m12 => exact hm12 hh
      | m22 => exact hm (.inl hh)
      | m23 => exact hm (.inr (.inl hh))
      | m24 => exact hm (.inr (.inr hh))
      | j2 => exact hj2 hh
      | j3 => exact h3 rfl
      | j4 => exact h4 rfl
      | hs => exact hhs hh
      | he => exact hheld hh
      | ru => exact hru hh
  · exact .inr ha

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
