module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.Alternatives.MarkedCatalogue
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.TrialityPerfect
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.ReePerfect
public import Theory.SpecificGroups.Tits.SolvableSylowOvergroups
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BinaryLinearCoverPerfect
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.JankoTwoOddRank
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.HigmanSimsOddRank
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.Alternatives.MarkedThreeFree
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.RudvalisOddRank
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.Alternatives.MarkedOddPair

/-!
# Further nonternary exclusions in the original marked normalizer

The genuine triality and Ree parabolic calculations contradict the preserved
odd-prime rank of the literal residual image. The Tits full-Sylow overgroups
are solvable and cannot contain a proper local C-component. The J₂ and HS
full-Sylow covers have large odd-prime rank at most one, as does the
completed Rudvalis cover. Held is excluded by the three-free, two-perfect
radical image, and J₄ by the actual odd-complement Sylow pair. These arguments
use the pre-embedding source data, before any case-ten extension or parameter
identification. The remaining signed odd-ternary branch retains its actual
projective or special model witness.

Source: Aschbacher–Smith A.3.12, pp.47–48, used in 1.3.8, p.513.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.FiveCase
open Section02 Section02.LocalModels ClassificationModels ChapterA.Section03.SourceEmbeddings
universe u
variable {G : Type u} [Group G] [Finite G]
variable {𝒦 : GroupClass.{u}} {p r : ℕ} {L : Subgroup G} {T : Sylow 2 G}
variable {C : Subgroup (radicalCore p L T)} {K : Subgroup G}

/-- All positive binary exponents of the genuine triality carrier are excluded. -/
theorem SourceData.containing_not_binary_triality (h : SourceData 𝒦 p r L T C K)
    {n : ℕ} (hn : 1 ≤ n) :
    ¬ Triality.Standard.IsTrialityGroupAt (2 ^ n) (quotientImage K
      (normalizer (C.map (radicalCore p L T).subtype : Set G))) := by
  intro hm
  let : Fact p.Prime := ⟨h.prime⟩
  have ho : Odd p := h.prime.odd_of_ne_two (by have := h.large; omega)
  obtain ⟨S, _, hB, _, hBD, _, hrank, hD⟩ := h.marked_image_setup
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ n (by omega)).mp hm
  exact hBD.ne (eq_of_triality_containing_component_of_odd_rank
    S hB hD hBD.le ho hrank (by omega) e)

/-- Both genuine Ree parabolic factors have insufficient marked odd rank. -/
theorem SourceData.containing_not_ree_f4 (h : SourceData 𝒦 p r L T C K)
    {m : ℕ} (hm : 1 ≤ m) :
    ¬ IsReeF4At (quotientImage K
      (normalizer (C.map (radicalCore p L T).subtype : Set G))) m := by
  rintro ⟨d,⟨e⟩⟩
  let : Fact p.Prime := ⟨h.prime⟩
  have ho : Odd p := h.prime.odd_of_ne_two (by have := h.large; omega)
  obtain ⟨S, _, hB, _, hBD, _, hrank, hD⟩ := h.marked_image_setup
  exact hBD.ne (eq_of_ree_containing_component_of_odd_rank S hB hD hBD.le ho hrank hm (e.trans d.modelEquiv))

/-- The separate Tits endpoint has no proper nonsolvable full-Sylow overgroup. -/
theorem SourceData.containing_not_tits (h : SourceData 𝒦 p r L T C K) :
    ¬ Nonempty (quotientImage K
      (normalizer (C.map (radicalCore p L T).subtype : Set G)) ≃* Tits.ParrottGroup) := by
  rintro ⟨e⟩
  obtain ⟨S, _, hB, _, hBD, _, _, hD⟩ := h.marked_image_setup
  exact hBD.ne (eq_of_solvable_sylow_overgroups S hB hD hBD.le
    (SolvableSylowOvergroups.of_equiv e Tits.ProperSylowOvergroups.solvableSylowOvergroups))

/-- The two actual J₂ Sylow overgroups have no large-prime square in their orders. -/
theorem SourceData.containing_not_janko_two (h : SourceData 𝒦 p r L T C K) :
    ¬ Nonempty (quotientImage K
      (normalizer (C.map (radicalCore p L T).subtype : Set G)) ≃*
      Sporadic.LeechRelated.J2.Carrier) := by
  rintro ⟨e⟩
  let : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨S, _, hB, _, hBD, _, hrank, hD⟩ := h.marked_image_setup
  exact hBD.ne (eq_of_jankoTwo_containing_component_of_large_odd_rank
    S hB hD hBD.le h.large hrank e)

/-- The actual Higman–Sims Sylow overgroups have insufficient marked rank. -/
theorem SourceData.containing_not_higman_sims (h : SourceData 𝒦 p r L T C K) :
    ¬ Nonempty (quotientImage K
      (normalizer (C.map (radicalCore p L T).subtype : Set G)) ≃*
      Sporadic.LeechRelated.HS.Carrier) := by
  rintro ⟨e⟩
  let : Fact p.Prime := ⟨h.prime⟩
  have ho : Odd p := h.prime.odd_of_ne_two (by have := h.large; omega)
  obtain ⟨S, _, hB, _, hBD, _, hrank, hD⟩ := h.marked_image_setup
  exact hBD.ne (eq_of_higmanSims_containing_component_of_large_odd_rank
    S hB hD hBD.le h.large ho hrank e)

/-- Binary SL₃ central covers are excluded through their literal projective
map and the central Frattini argument, retaining the field-four case. -/
theorem SourceData.containing_not_binary_sl3 (h : SourceData 𝒦 p r L T C K)
    {n : ℕ} (hn : 1 ≤ n) :
    ¬ IsSL (quotientImage K
      (normalizer (C.map (radicalCore p L T).subtype : Set G))) 3 (2 ^ n) := by
  rintro ⟨F, _, _, hF, ⟨e⟩⟩
  by_cases hlarge : 1 < n
  · let : Fact p.Prime := ⟨h.prime⟩
    have ho : Odd p := h.prime.odd_of_ne_two (by have := h.large; omega)
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    obtain ⟨S, _, hB, _, hBD, _, hrank, hD⟩ := h.marked_image_setup
    exact hBD.ne (eq_of_binary_sl3_containing_component_of_large_odd_rank
      S hB hD hBD.le h.large ho hrank hlarge hF e)
  · have he : n = 1 := by omega
    subst n
    have hz : center (Matrix.SpecialLinearGroup (Fin 3) F) = ⊥ :=
      (Matrix.SL3.center_eq_bot_iff_card_mod_three F).mpr (by
        rw [hF]; norm_num)
    apply h.containing_not_small_binary_linear (by omega : 3 ≤ 3 ∧ 3 ≤ 5)
    exact ⟨F,inferInstance,inferInstance,by simpa only [pow_one] using hF,
      ⟨e.trans (Matrix.SL3.equivProjectiveOfCenterEqBot F hz)⟩⟩

/-- The completed Rudvalis cover contradicts the marked rank in the
actual quasisimple containing image. -/
theorem SourceData.containing_not_rudvalis
    (h : SourceData KnownSimple.IsKnownSimple p r L T C K) :
    ¬ Nonempty (quotientImage K
      (normalizer (C.map (radicalCore p L T).subtype : Set G)) ≃* Rudvalis.Model) := by
  rintro ⟨e⟩
  let : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨hq,_⟩ := h.containing_model_remainder
  obtain ⟨S, _, hB, _, hBD, _, hrank, hD⟩ := h.marked_image_setup
  exact hBD.ne (eq_of_rudvalis_containing_component_of_large_odd_rank
    S hB hD hBD.le h.large hrank hq e)

/-- All nonternary rows are excluded on the original source data. The
remaining witness retains both signs and both projective and special groups;
it does not assert the still-needed case-ten extension. -/
theorem SourceData.containing_model_signed_oddThree
    (h : SourceData KnownSimple.IsKnownSimple p r L T C K) :
    let D := quotientImage K (normalizer (C.map (radicalCore p L T).subtype : Set G))
    IsQuasisimple D ∧
      (∃ q : ℕ, q.Prime ∧ Odd q ∧ ∃ unitary : Bool,
        IsPSLSign D unitary 3 q ∨ IsSLSign D unitary 3 q) := by
  obtain ⟨hq,hm⟩ := h.containing_model_remainder
  refine ⟨hq,?_⟩
  rcases hm with hm | ⟨n,hn,hm⟩ | ⟨m,hm,he⟩ | hm | ⟨name,hn,hm⟩ | ⟨n,hn,hm⟩
  · exact hm
  · exact (h.containing_not_binary_triality hn hm).elim
  · exact (h.containing_not_ree_f4 hm he).elim
  · exact (h.containing_not_tits hm).elim
  · rcases hn with rfl | rfl | rfl | rfl | rfl
    · exact (h.containing_not_janko_two hm).elim
    · exact (h.containing_not_higman_sims hm).elim
    · exact (h.containing_not_rudvalis hm).elim
    · exact (h.containing_not_held hm).elim
    · exact (h.containing_not_janko_four hm).elim
  · exact (h.containing_not_binary_sl3 hn hm).elim

end CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.FiveCase
