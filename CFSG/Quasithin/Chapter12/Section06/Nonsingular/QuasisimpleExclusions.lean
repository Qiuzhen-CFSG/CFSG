module

public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.QuasisimpleRank
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.ComponentRecognition
public import Theory.GroupTheory.PrimeRankCentralCover
public import CFSG.Quasithin.ChapterA.Section02.OddModelTwoRank
public import Theory.SpecificGroups.BinaryLinear.AutomorphismTwoRank
public import Theory.Mathieu.SmallModuleRanks.M12
public import CFSG.Quasithin.ChapterG.Section07.SporadicLocal.PrimeEleven

/-!
# First quasisimple exclusions for the original nonsingular residual

The quotient rank excludes the odd-characteristic and small alternating
models. Faithful descent of automorphisms through the center excludes A₈,
M₁₁ and J₁, while the quotient rank excludes M₁₂. The SQTK inheritance and
Theorem C then give the remaining actual central-quotient models, also using
the previously proved M₂₃ exclusion. This is a partial reduction of 12.6.12;
the remaining rows still require their marked local and Sylow arguments.

Source: Aschbacher--Smith, Lemma 12.6.12, printed pp.825--826.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The odd-characteristic rows have insufficient quotient two-rank. -/
theorem SourceHypothesis.nonsingular_not_odd_centralQuotient
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v) :
    ¬ ChapterA.Section02.IsTheoremCOddModel ((Kv (v : G)) ⧸ center (Kv (v : G))) := by
  intro hm
  have := hm.twoRank_le_two
  have := H.nonsingular_centralQuotient_rank D v hv
  omega

/-- The alternating rows fail the quotient or automorphism two-rank bound. -/
theorem SourceHypothesis.nonsingular_not_alternating_centralQuotient
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G))) {n : ℕ} (hn : n ≤ 8) :
    ¬ Nonempty (((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* alternatingGroup (Fin n)) := by
  let := hK
  rintro ⟨e⟩
  have hr := H.nonsingular_centralQuotient_rank D v hv
  rw [primeRank_equiv 2 e,
    (GLS3.Chapter5.PRank.alternating_hasPRank_two n).primeRank_eq Nat.prime_two] at hr
  have hn8 : n = 8 := by omega
  subst n
  have hauto := automorphism_primeRank_le_quotient_center (E := Kv (v : G)) 2
  rw [primeRank_equiv 2 (MulAut.congr e),
    ← primeRank_equiv 2 (MulAut.congr Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8)] at hauto
  have hu := hauto.trans BinaryLinear.AutomorphismTwoRank.psl4_two_rank_le
  have hl := H.nonsingular_automorphism_rank D v hv
  omega

/-- Exclude the M₁₁, M₁₂ and J₁ central quotients by their proved rank bounds. -/
theorem SourceHypothesis.nonsingular_quasisimple_small_sporadic_exclusions
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G))) :
    (¬ Nonempty (((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.Mathieu.M11)) ∧
    (¬ Nonempty (((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.Mathieu.M12)) ∧
    (¬ Nonempty (((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Janko1.Model)) := by
  let := hK
  have ha := H.nonsingular_automorphism_rank D v hv
  have hq := H.nonsingular_centralQuotient_rank D v hv
  refine ⟨?_,?_,?_⟩
  · rintro ⟨e⟩
    have := ChapterG.Section07.SporadicLocal.m11_centralQuotient_automorphism_twoRank_le_three e
    omega
  · rintro ⟨e⟩
    rw [primeRank_equiv 2 e] at hq
    have := Sporadic.Mathieu.m12_twoRank_le_three
    omega
  · rintro ⟨e⟩
    have := ChapterG.Section07.SporadicLocal.j1_centralQuotient_automorphism_twoRank_le_three e
    omega

/-- Apply Theorem C to the literal central quotient, using the inherited SQTK hypotheses. -/
theorem SourceHypothesis.nonsingular_quasisimple_centralQuotient_catalogue
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G))) :
    ChapterA.Section02.IsTheoremCModel ((Kv (v : G)) ⧸ center (Kv (v : G))) := by
  let C := Kv (v : G)
  let := hK
  let : IsSimpleGroup (C ⧸ center C) := IsQuasisimple.simple
  have hv2 : orderOf (v : G) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian _ v.property)
    (fun he => nonsingular_ne_one D hv (Subtype.ext he))
  have hA := H.source.simpleQTKE.twoLocal_sqtk (isTwoLocal_involution_centralizer hv2)
  let j := inclusion (Kv_le_Gv (v : G))
  have hsq : IsSQTK KnownSimple.IsKnownSimple C :=
    ⟨hA.stronglyQuasithin.of_injective j (inclusion_injective _),
      hA.isKGroup.of_injective j (inclusion_injective _)⟩
  have hsem : componentLayer C = ⊤ := by
    apply top_unique
    exact le_sSup ⟨(inferInstance : (⊤ : Subgroup C).Normal).isSubnormal,
      IsQuasisimple.of_mulEquiv (topEquiv (G := C)).symm⟩
  have hsemi : ChapterA.Section02.IsSemisimple (C ⧸ center C) :=
    componentLayer_eq_top_of_surjective (QuotientGroup.mk' (center C))
      (QuotientGroup.mk'_surjective _) hsem
  have hsec : ChapterA.Section02.IsSectionOf (C ⧸ center C) C :=
    ChapterA.Section02.IsSectionOf.of_surjective _ (QuotientGroup.mk'_surjective (center C))
  have hq := ChapterA.Section02.theoremA_knownSimple.stronglyQuasithin_section
    hsq.stronglyQuasithin hsq.isKGroup hsec hsemi
  exact ChapterA.Section02.theoremC_knownSimple inferInstance
    (Group.IsPerfect.not_isMulCommutative _) hq (hsq.isKGroup.quotient _)

/-- The remaining central-quotient models after the first exclusions of 12.6.12. -/
theorem SourceHypothesis.nonsingular_quasisimple_remaining_models
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G))) :
    let C := (Kv (v : G)) ⧸ center (Kv (v : G))
    ClassificationModels.IsBenderModel C ∨
      (∃ f, ChapterA.Section02.IsTheoremCRankTwoModel C f) ∨
      ClassicalGroup.IsPSL C 5 2 ∨
      (∃ name : ClassificationModels.SporadicName,
        (name = .m22 ∨ name = .m24 ∨ name = .j2 ∨ name = .hs ∨
          name = .he ∨ name = .ru ∨ name = .j4) ∧ Nonempty (C ≃* name.Carrier)) := by
  let C := (Kv (v : G)) ⧸ center (Kv (v : G))
  obtain ⟨h11,h12,hJ1⟩ := H.nonsingular_quasisimple_small_sporadic_exclusions D v hv hK
  have hM23 := H.nonsingular_not_M23_centralQuotient D v hv hK
  cases H.nonsingular_quasisimple_centralQuotient_catalogue D v hv hK with
  | alternating n hn he => exact (H.nonsingular_not_alternating_centralQuotient D v hv hK hn he).elim
  | odd hm => exact (H.nonsingular_not_odd_centralQuotient D v hv hm).elim
  | bender hm => exact .inl hm
  | rank_two f hm => exact .inr (.inl ⟨f,hm⟩)
  | linear_binary n hn he =>
    rcases hn with rfl | rfl
    · obtain ⟨F,_,_,hF,⟨e⟩⟩ := he
      let : Fintype F := Fintype.ofFinite F
      let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
        simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
      exact (H.nonsingular_not_alternating_centralQuotient D v hv hK (by decide : 8 ≤ 8)
        ⟨(e.trans (Atlas.fieldEquivPSL 4 eF)).trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8⟩).elim
    · exact .inr (.inr (.inl he))
  | sporadic hm =>
    rcases hm with ⟨name,hne,he⟩ | he
    · right; right; right
      refine ⟨name,?_,he⟩
      cases name with
      | m11 => exact (h11 he).elim
      | m12 => exact (h12 he).elim
      | m23 => exact (hM23 he).elim
      | j3 => exact (hne rfl).elim
      | m22 => exact .inl rfl
      | m24 => exact .inr (.inl rfl)
      | j2 => exact .inr (.inr (.inl rfl))
      | hs => exact .inr (.inr (.inr (.inl rfl)))
      | he => exact .inr (.inr (.inr (.inr (.inl rfl))))
      | ru => exact .inr (.inr (.inr (.inr (.inr (.inl rfl)))))
      | j4 => exact .inr (.inr (.inr (.inr (.inr (.inr rfl)))))
    · exact (hJ1 he).elim
end CFSG.Quasithin.Chapter12.Section06
