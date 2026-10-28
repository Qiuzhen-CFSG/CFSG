module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.AlternatingSeven
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.LinearThree
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.LinearTwo
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.SmallLinear
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.NativeSource.Sporadic
public import CFSG.Quasithin.Chapter1.Section01.ModelActions115
public import Theory.SpecificGroups.ReeF4.Model.LocalBlock

/-!
# Assembling the component model and intersection refinements

The literal model and conjugation action from 1.1.5 feed all completed
2.3.9(7) calculations. In particular the small prime-field overlaps are
converted by actual exceptional isomorphisms, and the alternating triple
covers retain their central quotient and the actual intersection map.
The surviving binary M₂₂ cover remains a separate, explicit residual.

Source: Aschbacher--Smith 2.3.9(7), printed pp.525--526.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement
open Subgroup Theory.GroupTheory ClassificationModels
open Chapter15.Section03.Candidates.ComponentStructure
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The partition identification keeps the original central quotient;
for the triple cover this is not a full inverse-image assertion. -/
def AlternatingSevenIntersection (L M : Subgroup G) (z : G) : Prop :=
  (Nonempty (L ≃* alternatingGroup (Fin 7)) ∨ IsAlternatingCover L 7) ∧
  ∃ e : (L ⧸ center L) ≃* AlternatingSeven.A7,
    (M.subgroupOf L).map (AlternatingSeven.quotientMap e) =
      AlternatingSeven.alternatingStabilizer ∧
    L ⊓ M = L ⊓ centralizer ({z} : Set G) ∧
    ∃ f : M.subgroupOf L ≃* AlternatingSeven.alternatingStabilizer,
      ∀ x, (f x : AlternatingSeven.A7) = AlternatingSeven.quotientMap e (x : L)

/-- All source alternatives, with every intersection and diagram assertion.
The M₁₁ instance of (d) is grouped with its sporadic source family. -/
inductive RefinedIntersection (L M S : Subgroup G) (z : G) : Prop
  | bender (model : IsBenderModel L)
  | case_b (model : LieType.CaseB L)
  | alternating (conclusion : AlternatingSevenIntersection L M z)
  | linear_three (model : Nonempty (L ≃* Matrix.PSL3Three.PSL))
      (intersection : ∃ t : L, orderOf t = 2 ∧ IsConjugationProjection L z t ∧
        L ⊓ M = L ⊓ centralizer ({(t : G)} : Set G))
  | linear_two (p : ℕ) (prime : IsFermatOrMersennePrime p)
      (model : ClassicalGroup.IsPSL L 2 p) (intersection : L ⊓ M = S ⊓ L)
  | sporadic (conclusion : SporadicIntersection L M z)
  | case_g (conclusion : LieType.CaseG L M S z)

private theorem simpleLieModel_of_source (hm : LieTypeTwoModel L) : LieType.SimpleLieModel L := by
  rcases hm with hm | hm | hm
  · exact .inl hm
  · apply Or.inr ∘ Or.inl
    cases hm with
    | linear f hf he => exact ⟨f,.linear hf he⟩
    | symplectic f hf he => exact ⟨f,.symplectic hf he⟩
    | g2 f hf he => exact ⟨f,.g2 hf he⟩
    | triality f hf he => exact ⟨f,.triality hf he⟩
    | ree m hm he => exact ⟨2*m+1,.ree_f4 m hm rfl
        ((ReeF4.exists_localBlockInput_mulEquiv_iff L m).mp he)⟩
    | symplectic_derived he => exact ⟨1,.symplectic_derived rfl he⟩
    | g2_derived he => exact ⟨1,.g2_derived rfl he⟩
    | tits he => exact ⟨1,.tits rfl he⟩
  · exact .inr (.inr hm)

private theorem refined_of_lie
    (h : IsBenderModel L ∨ LieType.CaseB L ∨ LieType.CaseG L M ((S : Subgroup H).map H.subtype) z) :
    RefinedIntersection L M ((S : Subgroup H).map H.subtype) z := by
  rcases h with h | h | h
  · exact .bender h
  · exact .case_b h
  · exact .case_g h

private theorem seven_intersection (h : LocalSetup H L M S z)
    (α : MulAut L) (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (σ : Equiv.Perm (Fin 7)) (hσ : σ.cycleType = {2,2,2})
    (ha : AlternatingAction α 7 σ) : AlternatingSevenIntersection L M z := by
  let : Finite G := h.finite
  have hc (e : (L ⧸ center L) ≃* AlternatingSeven.A7)
      (hz : Nat.card (center L) = 1 ∨ Nat.card (center L) = 3)
      (ha : ∀ x : L, (AlternatingSeven.quotientMap e (α x) : AlternatingSeven.S7) =
        σ * AlternatingSeven.quotientMap e x * σ⁻¹) :=
    AlternatingSeven.exists_partition_identification h e hz α hα σ hσ ha
  rcases ha with ⟨e,ha⟩ | ⟨hs,⟨ec⟩,e,ha⟩
  · have hz : center L = ⊥ := by
      apply le_bot_iff.mp
      intro x hx
      have he : e x ∈ center (alternatingGroup (Fin 7)) :=
        (centerCongr e ⟨x,hx⟩).property
      rw [alternatingGroup.center_eq_bot (by norm_num),mem_bot] at he
      exact e.injective (he.trans (map_one e).symm)
    let eZ : (L ⧸ center L) ≃* alternatingGroup (Fin 7) :=
      ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans e
    obtain ⟨e',_,hi⟩ := hc eZ (Or.inl (by rw [hz,card_bot])) (by intro x; exact ha x)
    exact ⟨.inl ⟨e⟩,e',hi⟩
  · have hz : Nat.card (center L) = 3 := by
      rw [Nat.card_congr ec.toEquiv]
      simp
    obtain ⟨e',_,hi⟩ := hc e (.inr hz) ha
    exact ⟨.inr ⟨hs,⟨ec⟩,⟨e⟩⟩,e',hi⟩

private theorem primeLinearEquiv {K : Type*} [Group K] (n p : ℕ)
    [Fact p.Prime] (hm : ClassicalGroup.IsPSL K n p) :
    Nonempty (K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod p)) := by
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let k : F ≃+* ZMod p := (ZMod.ringEquivOfPrime F Fact.out
    (by simpa only [Nat.card_eq_fintype_card] using hcard)).symm
  exact ⟨e.trans (Atlas.fieldEquivPSL n k)⟩

/-- Complete assembly of the six model/action alternatives of 1.1.5.
Every extra alternative in the result is the precise binary M₂₂ frontier. -/
theorem LocalSetup.refinement_or_binary_mathieu
    (h : LocalSetup H L M S z) (α : MulAut L)
    (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (hm : ModelAction115 L α) :
    RefinedIntersection L M ((S : Subgroup H).map H.subtype) z ∨
      (Nat.card (pCore 2 L) = 2 ∧ Nonempty ((L ⧸ pCore 2 L) ≃* Sporadic.Mathieu.M22)) := by
  cases hm with
  | lie hs hm hi =>
      let := hs
      exact .inl (refined_of_lie (LieType.refinement_of_inner_action h
        (simpleLieModel_of_source hm) α hα hi))
  | two_cover hn hc hm hi =>
      obtain ⟨t,rfl⟩ := hi
      exact .inl (.case_b (LieType.caseB_of_centralTwoCover h hc
        (hc ▸ hn) ⟨t,fun x => (hα x).symm⟩ hm))
  | six σ hσ ha =>
      rcases ha with ⟨e,_⟩ | ⟨hs,⟨ec⟩,e,_⟩
      · exact .inl (.case_b (.inl (LieType.isDerivedSymplecticFour_of_alternatingSix e)))
      · exact .inl (.case_b (.inr (.inr (.inr ⟨hs,by
          rw [Nat.card_congr ec.toEquiv]; simp,⟨e⟩⟩))))
  | seven σ hσ ha => exact .inl (.alternating (seven_intersection h α hα σ hσ ha))
  | odd hm hi =>
      rcases hm with hm | ⟨p,hp,hm⟩
      · obtain ⟨e⟩ := primeLinearEquiv 3 3 hm
        exact .inl (.linear_three ⟨e⟩ (linearThree_intersection h e α hα hi))
      · let : Fact p.Prime := ⟨hp.1⟩
        obtain ⟨e⟩ := primeLinearEquiv 2 p hm
        rcases h.linearPrime_small_alternatives p e with ⟨_,⟨e5⟩⟩ | ⟨_,⟨e7⟩⟩ | hbig
        · exact .inl (.bender (.linear 2 (by decide)
            ⟨GaloisField 2 2,inferInstance,inferInstance,by rw [GaloisField.card 2 2 (by decide)],⟨e5⟩⟩))
        · exact .inl (.case_b (.inr (.inl ⟨1,by decide,
            ZMod 2,inferInstance,inferInstance,by norm_num,⟨e7⟩⟩)))
        · exact .inl (.linear_two p hp hm (h.linearPrime_intersection p hp hbig e))
  | sporadic name hn hm hi =>
      obtain ⟨e⟩ := hm
      rcases h.sporadic_intersection_or_binary_cover ⟨e,α,hα,hi.1⟩ hn with h | ⟨_,h⟩
      · exact .inl (.sporadic h)
      · exact .inr h

/-- The inner-action clause of 2.3.9(7), preserving both alternating exceptions. -/
theorem inner_or_alternating_quotient_of_modelAction {α : MulAut L} (hm : ModelAction115 L α) :
    α ∈ (MulAut.conj (G := L)).range ∨
      Nonempty ((L ⧸ center L) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((L ⧸ center L) ≃* alternatingGroup (Fin 7)) := by
  cases hm with
  | lie _ _ hi | two_cover _ _ _ hi | odd _ hi => exact .inl hi
  | sporadic _ _ _ hi => exact .inl hi.1
  | six σ hs ha | seven σ hs ha =>
      rcases ha with ⟨e,_⟩ | ⟨_,_,e,_⟩
      · have hz : center L = ⊥ := by
          apply le_bot_iff.mp
          intro x hx
          have he : e x ∈ center _ := (centerCongr e ⟨x,hx⟩).property
          rw [alternatingGroup.center_eq_bot (by norm_num),mem_bot] at he
          exact e.injective (he.trans (map_one e).symm)
        let eZ := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans e
        first | exact .inr (.inl ⟨eZ⟩) | exact .inr (.inr ⟨eZ⟩)
      · first | exact .inr (.inl ⟨e⟩) | exact .inr (.inr ⟨e⟩)

end CFSG.Quasithin.Chapter2.ComponentRefinement
