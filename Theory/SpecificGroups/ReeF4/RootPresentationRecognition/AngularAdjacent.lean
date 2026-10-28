module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.AngularPresentation

/-!
# Adjacent root commutation and literal angular equations

The native interval theorem puts a commutator of adjacent main curves in the
empty interval. Two closure arguments extend this to their whole root groups.
For any commuting pair, uniqueness of native angular coordinates identifies
the chosen table with the tuple containing only the second root parameter.
This proves the exact table equation in every realization where that pair
commutes, without assuming a comparison homomorphism.

Source: GLS3, 2.4.5(d) and Corollary 2.4.6; the angular collection step used
in Fong--Seitz II, Section 10. All field parameters, including zero, are retained.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup
open ReeF4 ReeF4.CentralCovers.TwoPrimary
open ReeF4.ElementaryTwoBound ReeF4.NormalizedRootCentralizers.CenterExponent
open Theory.GroupTheory.OrderedRootPresentation
open ReeF4.RootPresentationRecognition
namespace ReeF4.RootPresentationRecognition.AngularAdjacent

/-- Neighboring whole root groups commute in the native model. -/
theorem native_adjacent_commute (m : ℕ) (i j : Fin 8) (hij : i.val + 1 = j.val)
    (x : X m i) (y : X m j) : Commute (x : Model m) (y : Model m) := by
  have hc (t u : CoefficientField m) :
      Commute (mainElement m i t) (mainElement m j u) := by
    have hh := TailRelations.BaseIntervals.main_commutator_mem m i j (by omega) ⊥
      (fun k hk hkj => by exfalso; omega) t u
    have he : (mainElement m i t)⁻¹ * (mainElement m j u)⁻¹ *
        mainElement m i t * mainElement m j u = 1 := mem_bot.mp hh
    have hh' : Commute ((mainElement m i t)⁻¹) ((mainElement m j u)⁻¹) :=
      commutatorElement_eq_one_iff_commute.mp (by
        simpa only [commutatorElement_def,inv_inv] using he)
    exact hh'.inv_left.inv_right
  have hle (t : CoefficientField m) : X m j ≤ centralizer {mainElement m i t} := by
    apply (closure_le _).mpr
    rintro _ ⟨u,rfl⟩
    exact mem_centralizer_singleton_iff.mpr (hc t u).symm
  have hle' : X m i ≤ centralizer {(y : Model m)} := by
    apply (closure_le _).mpr
    rintro _ ⟨t,rfl⟩
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_singleton_iff.mp (hle t y.property)).symm
  exact mem_centralizer_singleton_iff.mp (hle' x.property)

namespace SingletonCoordinates
variable {I : Type*} [DecidableEq I] (R : I → Type*) [∀ i, Group (R i)]
private def singletonTuple (j : I) (b : R j) : (l : List I) → Tuple R l
  | [] => PUnit.unit
  | k :: l => ((if h : k = j then h.symm ▸ b else 1), singletonTuple j b l)
private theorem singleton_word_not_mem {G : Type*} [Group G]
    (f : ∀ i, R i →* G) (j : I) (b : R j) (l : List I) (hj : j ∉ l) :
    word R (fun i => f i) l (singletonTuple R j b l) = 1 := by
  induction l with
  | nil => rfl
  | cons k l ih =>
    have hk : k ≠ j := by intro he; subst k; exact hj (by simp)
    have hl : j ∉ l := fun h => hj (List.mem_cons_of_mem _ h)
    simp only [singletonTuple, word, dif_neg hk, map_one, one_mul, ih hl]
private theorem singleton_word {G : Type*} [Group G]
    (f : ∀ i, R i →* G) (j : I) (b : R j) (l : List I)
    (hn : l.Nodup) (hj : j ∈ l) :
    word R (fun i => f i) l (singletonTuple R j b l) = f j b := by
  induction l with
  | nil => simp at hj
  | cons k l ih =>
    by_cases hk : k = j
    · subst k
      simp only [singletonTuple, word, dite_true]
      rw [singleton_word_not_mem R f j b l (List.nodup_cons.mp hn).1, mul_one]
    · have hl : j ∈ l := (List.mem_cons.mp hj).resolve_left (Ne.symm hk)
      simp only [singletonTuple, word, dif_neg hk, map_one, one_mul]
      exact ih (List.nodup_cons.mp hn).2 hl
end SingletonCoordinates

/-- The exact native table equation transfers whenever this pair commutes in
both realizations. Uniqueness retains the literal, chosen coefficient tuple. -/
theorem equation_of_commute {G : Type*} [Group G] (m : ℕ)
    (f : ∀ i, AngularPresentation.Parameter m i →* G)
    (i j : PositiveTables.Root) (hj : j ∈ tail sourceOrder i)
    (a : AngularPresentation.Parameter m i) (b : AngularPresentation.Parameter m j)
    (hnative : Commute (a : Model m) (b : Model m))
    (hsource : Commute (f i a) (f j b)) :
    f i a * f j b * (f i a)⁻¹ =
      word (AngularPresentation.Parameter m) (fun k => f k) (tail sourceOrder i)
        ((AngularPresentation.table m).conjugate i j hj a b) := by
  have hn : (tail sourceOrder i).Nodup := AngularPresentation.order_nodup.drop
  have he := AngularPresentation.conjugate_unique m i j hj a b
    (SingletonCoordinates.singletonTuple (AngularPresentation.Parameter m) j b (tail sourceOrder i))
    (by
      rw [SingletonCoordinates.singleton_word _ _ _ _ _ hn hj]
      change (a : Model m) * b * (a : Model m)⁻¹ = (b : Model m)
      rw [hnative.eq, mul_inv_cancel_right])
  rw [he, SingletonCoordinates.singleton_word _ _ _ _ _ hn hj,
    hsource.eq, mul_inv_cancel_right]
end ReeF4.RootPresentationRecognition.AngularAdjacent
