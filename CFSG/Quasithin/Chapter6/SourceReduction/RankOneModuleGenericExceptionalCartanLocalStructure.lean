module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalMathieuCover
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalSevenCover
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.QuasisimpleContaining

/-!
# The genuine structural alternatives for the selected Cartan container

Apply the full A.3.6 theorem to the literal image of the same selected
C-component in Y/O₂(Y). All central triple-cover alternatives are excluded:
the even and odd classical rows use the original Cartan exclusions, the
six-point cover cannot properly contain the seed, and the seven-point and
M₂₂ covers are excluded by their original escaping actions.

The surviving image is either simple with its actual Theorem C carrier,
or satisfies the full natural or nilpotent Fitting alternative of A.3.6.
Its common radical, odd-core and quasisimple-quotient data are retained,
as are every preceding exclusion and the entire binary-triality endpoint.
Neither nonquasisimple alternative is assumed away. Their exclusion,
the remaining simple-carrier sieve and binary-triality ambient exclusion
are still required for SourceLocalCartanEscape.
Source: Aschbacher--Smith A.3.6 and 5.1.13, printed pp.43--45,636--637,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Chapter1.Section02 Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

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

/-- The same selected image has the full A.3.6 structure with every central-cover row removed. -/
theorem localCartan_escape_seed_structure_reduction
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H ∧
      ∃ C : Subgroup Y, C.IsCComponent ∧ K ≤ C.map Y.subtype ∧
        residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
        ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal ∧
        (K.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) <
          C.map (QuotientGroup.mk' (pCore 2 Y)) ∧
        ¬ SolvableSylowOvergroups (C ⧸ pCore 2 C) ∧
        (∀ m : ℕ, 0 < m → ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨
          IsSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨ IsSU (C ⧸ pCore 2 C) 3 (2 ^ m))) ∧
        (RankTwoTheoremC (C ⧸ pCore 2 C) →
          K = residual H ∧ C.Normal ∧
          Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C) ∧
          ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 8 ∧
          n = 2 ∧ Nat.card A = 3 ∧ A ≤ C.map Y.subtype ∧
          localBorel T L ≤ omegaCentralizer T ∧
          IsOneOrTwoA5Modules L (layer L W) ∧ Nat.card B = 7 ∧
          B ≤ centralizer
            (conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) L : Set G)) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 p) ∧
        ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 25 ∧
        C.Normal ∧
        ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Janko1.Model) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 p ∨
            ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 p ∨
            IsSL (C ⧸ pCore 2 C) 3 p ∨ IsSU (C ⧸ pCore 2 C) 3 p)) ∧
        ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Janko4.Model) ∧
        ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M22) ∧
        (Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M23) →
          K = residual H ∧
          ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4 ∧
          Nat.card B = 3) ∧
        let I := C.map (QuotientGroup.mk' (pCore 2 Y))
        Chapter1.Section02.A36Common I ∧
          ((IsSimpleGroup I ∧ TheoremCModel I) ∨
            Chapter1.Section02.A36Natural I ∨ Chapter1.Section02.A36Nilpotent I) := by
  obtain ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,
    hprime,h25,hCn,hJ,hOdd,hJ4,hM22,hM23⟩ :=
    localCartan_escape_seed_mathieu_reduction h hH hgen c hY hescape
  let : C.Normal := hCn
  refine ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,
    hprime,h25,hCn,hJ,hOdd,hJ4,hM22,hM23,?_⟩
  let I := C.map (QuotientGroup.mk' (pCore 2 Y))
  let : Group.IsNilpotent (pCore 2 Y) := pCore_isNilpotent
  let e : I ≃* (C ⧸ pCore 2 C) := (cComponentTwoCoreQuotientEquiv hC).symm
  obtain ⟨halt,hcommon⟩ := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    _ (uniqueness_local_quotient_sqtk h.qtke hY.1) (pCore_quotient_pCore_eq_bot 2)
    I (hC.map_quotient _)
  refine ⟨hcommon,?_⟩
  cases halt with
  | simple _ hs hm => exact .inl ⟨hs,hm⟩
  | natural hm => exact .inr (.inl hm)
  | nilpotent hm => exact .inr (.inr hm)
  | cover _ _ hm =>
    exfalso
    cases hm with
    | alternating_six hm =>
      exact LocalSieve.not_small_alternating_container h.qtke hKH hH.1.1.2 hKL hR
        hY hescape C hC hKC (.inr (.inr (cover_transport e hm)))
    | alternating_seven hm =>
      exact LocalSieve.not_alternating_seven_cover h hH hgen c hKL hKT hR
        hY hescape C hC hKC (cover_transport e hm)
    | mathieu hm =>
      exact LocalSieve.not_mathieu_cover_container h hH hgen c hKL hKT hR
        hY hescape C hC hKC (cover_transport e hm)
    | classical u p hp hm =>
      rcases hp with ⟨k,hk,rfl,_⟩ | ⟨hp,ho⟩
      · apply hternary k hk
        cases u
        · exact .inr (.inl (sl_transport e hm))
        · exact .inr (.inr (su_transport e hm))
      · apply hOdd p hp ho
        cases u
        · exact .inr (.inr (.inl (sl_transport e hm)))
        · exact .inr (.inr (.inr (su_transport e hm)))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
