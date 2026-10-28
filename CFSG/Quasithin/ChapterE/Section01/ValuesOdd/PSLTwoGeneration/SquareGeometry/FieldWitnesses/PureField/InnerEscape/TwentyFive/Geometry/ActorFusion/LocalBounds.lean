module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.Inputs

/-!
# Projective bounds and full ambient spans of characteristic-five actors

The supplied comparison gives actual PGL₂(5) × C₂ coordinates. An eligible
actor has order four or eight, so its projective image is nontrivial; the
projective two-rank bound makes that image have order two or four. Failure
of positioning therefore puts it inside the literal inverse image of PSL₂.

If no ambient conjugate in T is positioned, this bounds the entire ambient
conjugacy span. Normality of the original linear kernel separates linear
actors. The small-span and large-span lemmas below reduce the remaining
calculation to a marked intersection of order four and a local conjugator.
A bound on the projected intersection of the two large subgroups supplies
coverage. These reductions do not assert the remaining coordinate facts.

Source: Aschbacher--Smith, E.1.5, E.1.8 and E.1.14(6), printed pp.210--214;
the last refers to Aschbacher (1982), Lemma 4.10. This is a sufficient local
route for the exact `Frame.Fusion` contract, not a proof of E.1.14(6).
-/

public section
noncomputable section
open Subgroup GorensteinWalter Matrix
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.Frame

variable {F : Type*} [Field F] [Finite F] {σ : F ≃+* F}
variable (c : Frame σ) (hF : Nat.card F = 5 ^ 2) (hσ : orderOf σ = 2)

/-- The full, marked product coordinates associated with the supplied comparison. -/
@[expose] def productCoordinates (i : Bool) : c.centralizerAt i ≃*
    PGL2 (FixedPoints.subfield (zpowers σ) F) × zpowers σ :=
  (c.comparisonAt i).trans
    (pureCentralizerEquiv (by decide : Nat.Prime 5) (by decide) hF σ hσ)

theorem projection_eq_fst_productCoordinates (i : Bool) (x : c.centralizerAt i) :
    c.projection hF hσ i x = (c.productCoordinates hF hσ i x).1 := rfl

variable [Finite (innerModel F σ)]

omit [Finite F] in
theorem Eligible.card_eq_four_or_eight {A : Subgroup (innerModel F σ)}
    (hA : c.Eligible A) : Nat.card A = 4 ∨ Nat.card A = 8 := by
  let := hA.1
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  have hr : Group.rank A = n := le_antisymm
    (IsElementaryAbelian.rank_le_of_card_le A hn.le)
    (IsElementaryAbelian.rank_ge_of_card hn)
  rcases hA.2.2.2 with h | h
  · left; simpa [← hr, h] using hn
  · right; simpa [← hr, h] using hn

omit [Finite F] in
theorem Eligible.four_le_card {A : Subgroup (innerModel F σ)}
    (hA : c.Eligible A) : 4 ≤ Nat.card A := by
  rcases hA.card_eq_four_or_eight c with h | h <;> omega

theorem Eligible.projectiveImage_ne_bot {A : Subgroup (innerModel F σ)}
    (hA : c.Eligible A) (i : Bool) :
    (A.subgroupOf (c.centralizerAt i)).map (c.projection hF hσ i) ≠ ⊥ := by
  let : Finite (zpowers σ) := Nat.finite_of_card_ne_zero
    (by rw [Nat.card_zpowers, hσ]; decide)
  intro hb
  let e := c.productCoordinates hF hσ i
  let a : A → c.centralizerAt i := fun x => ⟨x, c.sylow_le i (hA.2.1 x.property)⟩
  have hf (x : A) : (e (a x)).1 = 1 :=
    (Subgroup.map_eq_bot_iff _).mp hb (show a x ∈ A.subgroupOf _ from x.property)
  let f : A → zpowers σ := fun x => (e (a x)).2
  have hi : Function.Injective f := by
    intro x y h
    have he : e (a x) = e (a y) := Prod.ext ((hf x).trans (hf y).symm) h
    have hxy : (x : innerModel F σ) = (y : innerModel F σ) :=
      congrArg (fun t : c.centralizerAt i => (t : innerModel F σ)) (e.injective he)
    exact Subtype.ext hxy
  have hc := Nat.card_le_card_of_injective f hi
  rw [Nat.card_zpowers, hσ] at hc
  have ha := hA.four_le_card c
  omega

theorem Eligible.projectiveImage_card {A : Subgroup (innerModel F σ)}
    (hA : c.Eligible A) (i : Bool) :
    Nat.card ((A.subgroupOf (c.centralizerAt i)).map (c.projection hF hσ i)) = 2 ∨
      Nat.card ((A.subgroupOf (c.centralizerAt i)).map (c.projection hF hσ i)) = 4 := by
  let K := FixedPoints.subfield (zpowers σ) F
  let : Finite (PGL2 K) := Finite.of_surjective
    ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  let := hA.1
  let : IsElementaryAbelian 2 (A.subgroupOf (c.centralizerAt i)) :=
    IsElementaryAbelian.subgroupOf (hA.2.1.trans (c.sylow_le i))
  let B := (A.subgroupOf (c.centralizerAt i)).map (c.projection hF hσ i)
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map (c.projection hF hσ i)
  have hK : Nat.card K = 5 := fixedSubfield_card hF σ
    ((orderOf_eq_prime_iff (x := σ)).mp hσ).1
    ((orderOf_eq_prime_iff (x := σ)).mp hσ).2
  have hu : Nat.card B ≤ 4 :=
    (primeRank_le_iff_elementary_card_le _).mp
      (Theory.PSL2.odd_pgl_two_rank K
        ⟨5, 1, by decide, by decide, le_rfl, by simpa using hK⟩) B inferInstance
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 B).exists_card_eq
  have hle : n ≤ 2 := (pow_le_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).mp (hn ▸ hu)
  have hne : Nat.card B ≠ 1 := fun h =>
    hA.projectiveImage_ne_bot c hF hσ i (B.eq_bot_of_card_eq h)
  change Nat.card B = 2 ∨ Nat.card B = 4
  interval_cases n
  · exact (hne hn).elim
  · exact Or.inl hn
  · exact Or.inr hn

theorem Eligible.not_isPositioned_iff {A : Subgroup (innerModel F σ)}
    (hA : c.Eligible A) (i : Bool) :
    ¬ c.IsPositioned hF hσ i A ↔
      Nat.card ((A.subgroupOf (c.centralizerAt i)).map (c.projection hF hσ i)) = 4 ∧
      (A.subgroupOf (c.centralizerAt i)).map (c.projection hF hσ i) ≤
        (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2)
          (R := FixedPoints.subfield (zpowers σ) F)).range := by
  simp only [IsPositioned, PositionedImage]
  rcases hA.projectiveImage_card c hF hσ i with hc | hc <;> rw [hc] <;> simp

theorem Eligible.le_large_of_not_isPositioned {A : Subgroup (innerModel F σ)}
    (hA : c.Eligible A) (i : Bool) (hn : ¬ c.IsPositioned hF hσ i A) :
    A ≤ c.large hF hσ i := by
  have hi := ((hA.not_isPositioned_iff c hF hσ i).mp hn).2
  intro x hx
  refine ⟨hA.2.1 hx, ?_⟩
  exact ⟨⟨x, c.sylow_le i (hA.2.1 hx)⟩, hi ⟨_, hx, rfl⟩, rfl⟩

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.Frame

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry

private theorem conjugatesIn_self {G : Type*} [Group G] {T A : Subgroup G}
    (hAT : A ≤ T) : A ∈ conjugatesIn T A := by
  refine ⟨hAT, 1, ?_⟩
  have h : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by ext x; simp
  rw [h, Subgroup.map_id]

namespace Frame
variable {F : Type*} [Field F] [Finite F] {σ : F ≃+* F}
variable (c : Frame σ) (hF : Nat.card F = 5 ^ 2) (hσ : orderOf σ = 2)
variable [Finite (innerModel F σ)]

omit [Finite F] in
theorem Eligible.of_mem_conjugatesIn {A B : Subgroup (innerModel F σ)}
    (hA : c.Eligible A) (hB : B ∈ conjugatesIn (c.T : Subgroup _) A) : c.Eligible B := by
  obtain ⟨hBT, g, rfl⟩ := hB
  let := hA.1
  have hr := Group.rank_congr
    (A.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)
  refine ⟨IsElementaryAbelian.map _, hBT, ?_, ?_⟩
  · exact fun hb => hA.2.2.1
      ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective).mp hb)
  · rw [← hr]
    exact hA.2.2.2

omit [Finite (innerModel F σ)] in
theorem usable_of_isPositioned {A : Subgroup (innerModel F σ)}
    (hAT : A ≤ (c.T : Subgroup _)) (i : Bool) (hp : c.IsPositioned hF hσ i A) :
    c.Usable hF hσ i A := ⟨A, conjugatesIn_self hAT, hp⟩

omit [Finite (innerModel F σ)] in
theorem not_isPositioned_of_not_usable {A B : Subgroup (innerModel F σ)} (i : Bool)
    (hn : ¬ c.Usable hF hσ i A) (hB : B ∈ conjugatesIn (c.T : Subgroup _) A) :
    ¬ c.IsPositioned hF hσ i B := fun h => hn ⟨B, hB, h⟩

/-- Failure of usability bounds the FULL ambient span, including conjugates
whose conjugating elements are outside either centralizer. -/
theorem orbitSpan_le_large_of_not_usable {A : Subgroup (innerModel F σ)}
    (hA : c.Eligible A) (i : Bool) (hn : ¬ c.Usable hF hσ i A) :
    orbitSpan (c.T : Subgroup _) A ≤ c.large hF hσ i := by
  apply sSup_le
  intro B hB
  exact (hA.of_mem_conjugatesIn c hB).le_large_of_not_isPositioned c hF hσ i
    (c.not_isPositioned_of_not_usable hF hσ i hn hB)

omit [Finite F] [Finite (innerModel F σ)] in
/-- Normality of the original linear kernel separates its actors under every
ambient conjugation. -/
theorem orbitSpan_le_linearKernel {A : Subgroup (innerModel F σ)}
    (hA : A ≤ pGammaL2LinearKernel F (innerModel F σ)) :
    orbitSpan (c.T : Subgroup _) A ≤ pGammaL2LinearKernel F (innerModel F σ) := by
  apply sSup_le
  rintro B ⟨_, g, rfl⟩
  exact (map_mono hA).trans_eq (Subgroup.Normal.map_conj_eq _ g)

/-- A marked local intersection and its order identify the small ambient
span. There is no hypothesis asserting the ambient span equality. -/
theorem orbitSpan_eq_small_of_linear {A : Subgroup (innerModel F σ)}
    (hA : c.Eligible A) (i : Bool) (hn : ¬ c.Usable hF hσ i A)
    (hlin : A ≤ pGammaL2LinearKernel F (innerModel F σ))
    (hmark : c.large hF hσ i ⊓ pGammaL2LinearKernel F (innerModel F σ) =
      c.small hF hσ i)
    (hcard : Nat.card (c.small hF hσ i) = 4) :
    orbitSpan (c.T : Subgroup _) A = c.small hF hσ i := by
  have hu : orbitSpan (c.T : Subgroup _) A ≤ c.small hF hσ i := by
    rw [← hmark]
    exact le_inf (c.orbitSpan_le_large_of_not_usable hF hσ hA i hn)
      (c.orbitSpan_le_linearKernel hlin)
  have he : A = c.small hF hσ i := eq_of_le_of_card_ge
    ((le_orbitSpan hA.2.1).trans hu) (hcard ▸ hA.four_le_card c)
  exact le_antisymm hu (he ▸ le_orbitSpan hA.2.1)

/-- Two explicitly exhibited conjugates suffice for the large span; the
universal upper bound still uses every ambient conjugate in T. -/
theorem orbitSpan_eq_large_of_local_join {A : Subgroup (innerModel F σ)}
    (hA : c.Eligible A) (i : Bool) (hn : ¬ c.Usable hF hσ i A)
    (g : innerModel F σ)
    (hgT : A.map (MulAut.conj g).toMonoidHom ≤ (c.T : Subgroup _))
    (hjoin : c.large hF hσ i ≤ A ⊔ A.map (MulAut.conj g).toMonoidHom) :
    orbitSpan (c.T : Subgroup _) A = c.large hF hσ i := by
  apply le_antisymm (c.orbitSpan_le_large_of_not_usable hF hσ hA i hn)
  exact hjoin.trans (sup_le (le_orbitSpan hA.2.1) (le_sSup ⟨hgT, g, rfl⟩))

/-- A bound on the projected intersection of the two literal large subgroups
gives coverage without classifying ambient conjugacy classes. -/
theorem positioned_coverage_of_intersection_bound
    (hcross : Nat.card (((c.large hF hσ false ⊓ c.large hF hσ true).subgroupOf
      (c.centralizerAt false)).map (c.projection hF hσ false)) ≤ 2)
    {A : Subgroup (innerModel F σ)} (hA : c.Eligible A) :
    c.IsPositioned hF hσ false A ∨ c.IsPositioned hF hσ true A := by
  classical
  let : Finite (PGL2 (FixedPoints.subfield (zpowers σ) F)) := Finite.of_surjective
    ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  by_contra! hn
  have hsub := le_inf
    (hA.le_large_of_not_isPositioned c hF hσ false hn.1)
    (hA.le_large_of_not_isPositioned c hF hσ true hn.2)
  have hc := card_le_of_le (map_mono (subgroupOf_mono (c.centralizerAt false) hsub)
    (f := c.projection hF hσ false))
  have ha := ((hA.not_isPositioned_iff c hF hσ false).mp hn.1).1
  omega

end Frame
end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry
