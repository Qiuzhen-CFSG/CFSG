module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoReduction.LargeSporadic
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.SylowOvergroups.Coverage
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer
public import Theory.GroupTheory.TwoThreeSolvable

/-!
# The Hall--Janko exclusion for the original moved component

The certified Sylow-overgroup cover in the actual degree-100 J₂ carrier
has two proper members, of orders 1920 and 1152. Divisibility makes both
maximal, and the second is solvable. Sylow conjugacy transports this pair
to the literal component quotient. The existing odd-action argument then
contradicts generation of the enlarged local group by its residual, Sylow
and odd supplement.

The resulting source sieve retains the full odd classical groups and
cubic covers, both nonquasisimple alternatives and every A.3.6 common
clause. J₁ is now the only remaining sporadic quotient. The remaining
recognition and field-four terminal geometry belong to
qt-d-1222-natural-line-action; this does not yet prove 11.2.3.

Source: Aschbacher--Smith 3.3.12, printed p.589, using A.3.12(16),
pp.47--48. The imported J₂ certificates retain the ATLAS attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
open Sporadic.LeechRelated.J2
open ExceptionalParabolics ExceptionalParabolics.Seed

private theorem janko_two_first_maximal : IsCoatom l₁ := by
  have hne : l₁ ≠ ⊤ := by
    intro he
    have hc := FirstParabolic.card_l₁
    rw [he, Nat.card_congr topEquiv.toEquiv, FirstParabolic.card_carrier] at hc
    omega
  apply isCoatom_iff_ge_of_le.mpr
  refine ⟨hne, fun B hB hle => ?_⟩
  rcases SylowOvergroups.proper_overgroup_le B (SecondParabolic.s_le_l₁.trans hle) hB with h | h
  · exact h
  · have hd := card_dvd_of_le (hle.trans h)
    rw [FirstParabolic.card_l₁, PairNormalizer.card_p₂] at hd
    norm_num at hd

private theorem janko_two_second_maximal : IsCoatom p₂ := by
  have hne : p₂ ≠ ⊤ := by
    intro he
    have hc := PairNormalizer.card_p₂
    rw [he, Nat.card_congr topEquiv.toEquiv, FirstParabolic.card_carrier] at hc
    omega
  apply isCoatom_iff_ge_of_le.mpr
  refine ⟨hne, fun B hB hle => ?_⟩
  rcases SylowOvergroups.proper_overgroup_le B (PairNormalizer.s_le_p₂.trans hle) hB with h | h
  · have hd := card_dvd_of_le (hle.trans h)
    rw [PairNormalizer.card_p₂, FirstParabolic.card_l₁] at hd
    norm_num at hd
  · exact h

private theorem janko_two_second_solvable : Group.IsSolvable p₂ := by
  apply isSolvable_of_prime_dvd_card_eq_two_or_three
  intro p hp hd
  rw [PairNormalizer.card_p₂] at hd
  have hd' : p ∣ 2 ^ 7 * 3 ^ 2 := hd
  rcases hp.dvd_mul.mp hd' with h | h
  · exact .inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  · exact .inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h))

private theorem janko_two_sylow_overgroups {H : Type*} [Group H] [Finite H]
    (e : H ≃* Carrier) (S : Sylow 2 H) :
    ∃ P Q : Subgroup H, IsCoatom P ∧ IsCoatom Q ∧
      (S : Subgroup H) ≤ P ∧ (S : Subgroup H) ≤ Q ∧
      Group.IsSolvable (P ⊓ Q : Subgroup H) ∧
      ∀ J : Subgroup H, (S : Subgroup H) ≤ J → J ≠ ⊤ → J ≤ P ∨ J ≤ Q := by
  obtain ⟨_,a,_,hS⟩ := SolvableSylowControl.exists_aligned_equiv e S
    (SecondParabolic.sylow FirstParabolic.card_l₁)
  change (S : Subgroup H).map a.toMonoidHom = s at hS
  let P := l₁.comap a.toMonoidHom
  let Q := p₂.comap a.toMonoidHom
  refine ⟨P,Q,isCoatom_comap_of_surjective a.surjective janko_two_first_maximal,
    isCoatom_comap_of_surjective a.surjective janko_two_second_maximal,
    map_le_iff_le_comap.mp (hS ▸ SecondParabolic.s_le_l₁),
    map_le_iff_le_comap.mp (hS ▸ PairNormalizer.s_le_p₂),?_,?_⟩
  · let : Group.IsSolvable p₂ := janko_two_second_solvable
    let f : (P ⊓ Q : Subgroup H) →* p₂ :=
      (a.toMonoidHom.comp (P ⊓ Q).subtype).codRestrict p₂ (fun x => x.property.2)
    exact Group.isSolvable_of_isSolvable_injective (f := f) (by
      intro x y hxy
      exact Subtype.ext (a.injective (congrArg Subtype.val hxy)))
  · intro J hSJ hJ
    have hj : J.map a.toMonoidHom ≠ ⊤ := by
      intro he
      apply hJ
      apply map_injective (f := a.toMonoidHom) a.injective
      rw [he,map_top_of_surjective _ a.surjective]
    have hu : s ≤ J.map a.toMonoidHom := hS ▸ map_mono hSJ
    rcases SylowOvergroups.proper_overgroup_le (J.map a.toMonoidHom) hu hj with hp | hq
    · exact .inl (map_le_iff_le_comap.mp hp)
    · exact .inr (map_le_iff_le_comap.mp hq)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {c : Coordinates D S.field} {f : InvariantFlag c} {A : OddSupplement T}
namespace MovedComponent
variable (E : MovedComponent S f A)

/-- The literal Hall--Janko quotient cannot admit the original moved residual. -/
theorem quotient_not_janko_two :
    ¬ Nonempty ((E.component ⧸ pCore 2 E.component) ≃* Carrier) := by
  rintro ⟨e⟩
  exact E.false_of_two_sylow_overgroups (janko_two_sylow_overgroups e)

end MovedComponent

open Chapter1.Section02 Chapter1.Section02.LocalModels

/-- The full source alternatives after every sporadic row except J₁ is excluded. -/
inductive SourceCasesAfterJankoTwo (Q : Type*) [Group Q] [Finite Q] : Prop
  | simple (simple : IsSimpleGroup Q)
      (model : (∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ unitary : Bool, IsPSLSign Q unitary 3 p) ∨
        Nonempty (Q ≃* Janko1.Model))
  | cover (quasisimple : IsQuasisimple Q)
      (center : Nonempty (Subgroup.center Q ≃* Multiplicative (ZMod 3)))
      (model : ∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ unitary : Bool, IsSLSign Q unitary 3 p)
  | natural (data : A36Natural (⊤ : Subgroup Q))
  | nilpotent (data : A36Nilpotent (⊤ : Subgroup Q))

namespace MovedComponent
variable (E : MovedComponent S f A)

/-- Refine the actual source catalogue without dropping any nonsporadic case. -/
theorem source_cases_after_janko_two :
    SourceCasesAfterJankoTwo (E.component ⧸ pCore 2 E.component) ∧
      A36Common (⊤ : Subgroup (E.component ⧸ pCore 2 E.component)) := by
  obtain ⟨hc,hcommon⟩ := E.source_cases_after_large_sporadic
  refine ⟨?_,hcommon⟩
  cases hc with
  | simple hs hm =>
    apply SourceCasesAfterJankoTwo.simple hs
    rcases hm with h | h | h
    · exact .inl h
    · exact (E.quotient_not_janko_two h).elim
    · exact .inr h
  | cover hq hz hm => exact .cover hq hz hm
  | natural h => exact .natural h
  | nilpotent h => exact .nilpotent h

/-- An actual sporadic quotient is recognized as J₁; the independent classical
and nonquasisimple source rows remain in `source_cases_after_janko_two`. -/
theorem sporadic_quotient_is_janko_one
    (hs : IsSimpleGroup (E.component ⧸ pCore 2 E.component))
    (hm : (∃ name : ClassificationModels.SporadicName, name ≠ .j3 ∧
      Nonempty ((E.component ⧸ pCore 2 E.component) ≃* name.Carrier)) ∨
      Nonempty ((E.component ⧸ pCore 2 E.component) ≃* Janko1.Model)) :
    Nonempty ((E.component ⧸ pCore 2 E.component) ≃* Janko1.Model) := by
  rcases hm with ⟨name,hname,⟨e⟩⟩ | h
  · rcases E.remaining_sporadic_name name hname ⟨e⟩ with rfl | rfl | rfl | rfl
    · exact (E.quotient_not_janko_two ⟨e⟩).elim
    · exact (E.quotient_not_higman_sims ⟨e⟩).elim
    · exact (E.quotient_not_rudvalis hs ⟨e⟩).elim
    · exact (E.quotient_not_janko_four hs ⟨e⟩).elim
  · exact h

end MovedComponent

/-- Apply the complete sporadic exclusion to the component constructed from
the original escaping Sylow normalizer, with the original A.3.6 common data. -/
theorem exists_moved_component_after_janko_two (f : InvariantFlag c) (A : OddSupplement T)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ∃ E : MovedComponent S f A,
      SourceCasesAfterJankoTwo (E.component ⧸ pCore 2 E.component) ∧
      A36Common (⊤ : Subgroup (E.component ⧸ pCore 2 E.component)) := by
  obtain ⟨E⟩ := exists_movedComponent f A hescape
  exact ⟨E,E.source_cases_after_janko_two⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
