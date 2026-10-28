module

public import CFSG.Quasithin.ChapterG.Section11.Catalogue
public import Theory.Representation.AlternatingSevenConjugatePair.ElementaryGeometry
public import Theory.Mathieu.M22.ValueBoundParabolics.SmallQuotients
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.PrimeRankOrderBound
public import Theory.Mathieu.M22.Properties.TwoRank
public import Theory.SpecificGroups.PSL2.BinaryAutomorphismRank
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import CFSG.Quasithin.ChapterG.Section11.Reduction
public import Theory.Representation.OrthogonalFourPlusMatrix.OuterElementaryRank

/-!
# Numerical exclusions in the printed G.11 catalogue

An elementary actor of rank at least half the degree excludes the tensor,
outer orthogonal, SL₂(8), exchanged A₅ and triple-M₂₂ rows by their literal
model maps. The solvable degree-six row is excluded by the original G.10
solvable-action theorem. This leaves the four-dimensional, natural A₇,
split orthogonal six-space and G₂(2) rows.

These arguments extract the model calculations of Chapter14's rank-two
`ComponentCatalogueLargeActorDegreesSieve` and `...DegreesOuter` without
its unrelated terminal source hypotheses. The original rank-three HS
consumer is in `CaseOneHS.LocalStructure.SourceAction.CatalogueReduction`.
Catalogue exhaustiveness is still a separate recognition obligation.
Source: Aschbacher--Smith G.11.2, pp.364--367, and 14.3.24, p.1000.
-/

public noncomputable section
open Subgroup Module Theory.GroupTheory Representation
open scoped IsMulCommutative

private theorem even_three_involution : ∀ a : Equiv.Perm (Fin 3),
    a ^ 2 = 1 → a.sign = 1 → a = 1 := by decide +kernel

private theorem actor_finrank_le_of_embedding
    {D J : Type*} [Group D] [Finite D] [Group J] [Finite J]
    (f : D →* J) (hf : Function.Injective f) (X : Subgroup D)
    [IsElementaryAbelian 2 X] {r : ℕ} (hr : primeRank 2 J ≤ r) :
    finrank (ZMod 2) (Additive X) ≤ r := by
  let : IsElementaryAbelian 2 (X.map f) := IsElementaryAbelian.map f
  have hc := (primeRank_le_iff_elementary_card_le J).mp hr (X.map f) inferInstance
  rw [Subgroup.card_map_of_injective hf, Nat.card_congr Additive.ofMul,
    Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc

private theorem actor_finrank_le_three_of_five_three
    {D : Type*} [Group D] [Finite D]
    (f : D →* Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3))
    (hf : Function.Injective f) (X : Subgroup D) [IsElementaryAbelian 2 X] :
    finrank (ZMod 2) (Additive X) ≤ 3 := by
  apply actor_finrank_le_of_embedding f hf X
  rw [primeRank_prod_eq_add]
  exact Nat.add_le_add
    Sporadic.Mathieu.M22ValueBound.SmallQuotients.symmetricFive_primeRank_le_two
    Sporadic.Mathieu.M22ValueBound.SmallQuotients.symmetricThree_primeRank_le_one


namespace CFSG.Quasithin.ChapterG.Section11.LargeActorCatalogue
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (hlarge : finrank (ZMod 2) V ≤ 2 * finrank (ZMod 2) (Additive X))
include hlarge

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem false_of_eight_of_actor_le_three
    (hd : finrank (ZMod 2) V = 8)
    (hm : finrank (ZMod 2) (Additive X) ≤ 3) : False := by
  have h := hlarge
  omega

omit [FiniteDimensional (ZMod 2) V] in
/-- G.11.2(8) is impossible for an actor satisfying the half-degree bound: every elementary
subgroup of the full seven-letter symmetric group has rank at most three. -/
private theorem not_caseEight :
    ¬ ChapterG.Section11.CaseEight ρ B
      X := by
  rintro ⟨hd, ⟨e⟩, _⟩
  apply false_of_eight_of_actor_le_three hlarge hd
  exact actor_finrank_le_of_embedding e.toMonoidHom e.injective _
    Representation.AlternatingSevenConjugatePair.ElementaryGeometry.primeRank_symmetric.le

omit [FiniteDimensional (ZMod 2) V] in
/-- All four actual tensor actions in G.11.2(9) have actor rank at most
three, using the S₅ marking of the natural semilinear extension. -/
private theorem not_caseNine : ¬ ChapterG.Section11.CaseNine ρ := by
  rintro ⟨hd, hc⟩
  apply false_of_eight_of_actor_le_three hlarge hd
  rcases hc with ⟨e, _, _⟩ | ⟨e, _, _⟩ | ⟨e, _, _⟩ | ⟨e, _, _⟩
  · exact actor_finrank_le_three_of_five_three e.toMonoidHom e.injective _
  · let f := (alternatingGroup (Fin 5)).subtype.prodMap
      (MonoidHom.id (Equiv.Perm (Fin 3)))
    have hf : Function.Injective f := by
      intro a b h
      exact Prod.ext (Subtype.ext (congrArg Prod.fst h))
        (congrArg (fun z : Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3) => z.2) h)
    exact actor_finrank_le_three_of_five_three (f.comp e.toMonoidHom)
      (hf.comp e.injective) _
  · let a := RankTwo.TensorModels.Natural.groupEquiv.prodCongr
      (MulEquiv.refl (Equiv.Perm (Fin 3)))
    exact actor_finrank_le_three_of_five_three (e.trans a).toMonoidHom
      (e.trans a).injective _
  · let f := ((alternatingGroup (Fin 5)).subtype.comp
      RankTwo.TensorModels.Natural.alternatingEquiv.toMonoidHom).prodMap
        (MonoidHom.id (Equiv.Perm (Fin 3)))
    have hf : Function.Injective f := by
      intro a b h
      exact Prod.ext (RankTwo.TensorModels.Natural.alternatingEquiv.injective
        (Subtype.ext (congrArg Prod.fst h)))
          (congrArg (fun z : Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3) => z.2) h)
    exact actor_finrank_le_three_of_five_three (f.comp e.toMonoidHom)
      (hf.comp e.injective) _

omit [FiniteDimensional (ZMod 2) V] in
/-- In G.11.2(10), projection to S₆ is injective on the elementary actor:
its kernel consists of even permutations on three letters, hence is odd.
Embedding S₆ in S₇ bounds the actor by rank three. -/
private theorem not_caseTen :
    ¬ ChapterG.Section11.CaseTen ρ
      X := by
  rintro ⟨hd, e, _⟩
  let q : X →* Equiv.Perm (Fin 6) :=
    (((MonoidHom.fst (Equiv.Perm (Fin 6)) (Equiv.Perm (Fin 3))).comp
      RankTwo.Imprimitive.AlternatingSixTensor.equalSign.subtype).comp
        e.toMonoidHom).comp X.subtype
  have hq : Function.Injective q := by
    apply (injective_iff_map_eq_one q).mpr
    intro x hx
    change (e (x : G)).val.1 = 1 at hx
    have hp : e (x : G) ^ 2 = 1 := by
      rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian (x : G) x.property,
        map_one]
    have hs : (e (x : G)).val.2.sign = 1 := by
      have hs' : (e (x : G)).val.1.sign =
          (e (x : G)).val.2.sign := (e (x : G)).property
      rw [← hs', hx, map_one]
    have htwo := even_three_involution (e (x : G)).val.2
      (congrArg (fun z : RankTwo.Imprimitive.AlternatingSixTensor.GroupModel => z.val.2) hp) hs
    apply Subtype.ext
    apply e.injective
    change e (x : G) = e 1
    rw [map_one]
    exact Subtype.ext (Prod.ext hx htwo)
  let j : Equiv.Perm (Fin 6) →* Equiv.Perm (Fin 7) :=
    Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb
  have hj : Function.Injective j := Equiv.Perm.viaEmbeddingHom_injective _
  let f := j.comp q
  let : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hc := Representation.AlternatingSevenConjugatePair.ElementaryGeometry.elementary_card_le
    (A := f.range) inferInstance
  rw [← Nat.card_congr (MonoidHom.ofInjective (f := f) (hj.comp hq)).toEquiv,
    Nat.card_congr Additive.ofMul, Module.natCard_eq_pow_finrank (K := ZMod 2),
    Nat.card_zmod] at hc
  exact false_of_eight_of_actor_le_three hlarge hd
    ((Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc)

omit [FiniteDimensional (ZMod 2) V] in
/-- The group with generalized Fitting subgroup SL₂(8) acts faithfully on
that centerless subgroup. The actual automorphism rank bound excludes
G.11.2(11) for a larger actor, without classifying the full extension. -/
private theorem not_caseEleven : ¬ ChapterG.Section11.CaseEleven ρ := by
  rintro ⟨hd, e, _⟩
  let H := generalizedFitting G
  have hZ : center H = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hz : e x ∈ center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 3)) := by
      apply mem_center_iff.mpr
      intro y
      obtain ⟨z, rfl⟩ := e.surjective y
      simpa only [map_mul] using congrArg e (mem_center_iff.mp hx z)
    rw [Theory.PSL2.sl2_center_eq_bot, mem_bot] at hz
    exact e.injective (hz.trans e.map_one.symm)
  have hC : centralizer (H : Set G) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxH := centralizer_generalizedFitting_le G hx
    have hz : (⟨x, hxH⟩ : H) ∈ center H := by
      apply mem_center_iff.mpr
      intro y
      exact Subtype.ext (mem_centralizer_iff.mp hx y y.property)
    rw [hZ, mem_bot] at hz
    exact congrArg (fun y : H => (y : G)) hz
  let a : G →* MulAut H := MulAut.conjNormal
  have ha : Function.Injective a := by
    rw [← MonoidHom.ker_eq_bot_iff, MulAut.conjNormal_ker_eq_centralizer]
    exact hC
  let f := (MulAut.congr e).toMonoidHom.comp a
  have hf : Function.Injective f := (MulAut.congr e).injective.comp ha
  have hr := Theory.PSL2.BinaryAutomorphismRank.sl2_automorphism_two_rank_le
    (F := GaloisField 2 3) (n := 3) (by decide)
    (GaloisField.card 2 3 (by decide))
  exact false_of_eight_of_actor_le_three hlarge hd
    (actor_finrank_le_of_embedding f hf X hr)

omit [FiniteDimensional (ZMod 2) V] in
/-- The literal actor in G.11.2(12) has order eight. Its rank three
contradicts the half-degree inequality in degree eight. -/
private theorem not_caseTwelve :
    ¬ ChapterG.Section11.CaseTwelve ρ
      X := by
  rintro ⟨hd, L, hL, x, hx, hrest⟩
  have hc := hrest.2.2.2.2
  rw [Nat.card_congr Additive.ofMul, Module.natCard_eq_pow_finrank (K := ZMod 2),
    Nat.card_zmod] at hc
  have hm : finrank (ZMod 2) (Additive X) = 3 :=
    Nat.pow_right_injective (by decide : 1 < 2) hc
  exact false_of_eight_of_actor_le_three hlarge hd hm.le

omit [FiniteDimensional (ZMod 2) V] in
open Janko4.InvolutionCentralizers.First.QuotientExtension in
/-- The genuine triple-cover extension in G.11.2(13) maps to Aut(M₂₂)
with its actual order-three scalar kernel. Its two-rank is at most five,
which excludes a larger actor in degree twelve. -/
private theorem not_caseThirteen : ¬ ChapterG.Section11.CaseThirteen ρ := by
  rintro ⟨hd, ⟨e⟩⟩
  have hk : primeRank 2 quotientConjugation.ker ≤ 0 := by
    apply primeRank_le_of_prime_pow_not_dvd
    rw [quotientConjugation_ker, scalarSubgroup_card]
    decide
  have hr := primeRank_le_ker_add (p := 2) quotientConjugation
  have hAut := Sporadic.Mathieu.m22_automorphism_twoRank_le_five
  have hmodel : primeRank 2
      Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel.actionGroup ≤ 5 := by
    omega
  have hm := actor_finrank_le_of_embedding e.toMonoidHom e.injective
    X hmodel
  have hlarge := hlarge
  omega


omit [FiniteDimensional (ZMod 2) V] in
/-- Row (7) is impossible: every elementary actor of rank at least four
in the binary determinant normalizer lies in the marked Ω₄⁺(4). -/
private theorem not_caseSeven (hf : Function.Injective ρ) :
    ¬ ChapterG.Section11.CaseSeven ρ X := by
  rintro ⟨hd, hout, e, f, he⟩
  have hm := hlarge
  have hc : 16 ≤ Nat.card X := by
    rw [Nat.card_congr Additive.ofMul, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mpr (show 4 ≤
      finrank (ZMod 2) (Additive X) by omega)
  let a := e.trans ClassicalOrthogonal.FourPlusMatrix.Binary.orthogonalEquiv.symm
  let E := f.trans ClassicalOrthogonal.FourPlusMatrix.Binary.binaryCoordinates
  apply hout
  apply BinaryOffender.elementary_le_marked_determinant_of_card_ge_sixteen
    ρ hf (generalizedFitting G) a E
    (X := X) (hc := hc)
  intro h w
  change ClassicalOrthogonal.FourPlusMatrix.Binary.binaryCoordinates
    (f (ρ h w)) = _
  have hew := he h w
  change f (ρ h w) = _ at hew
  rw [hew]
  have hh := ClassicalOrthogonal.FourPlusMatrix.Binary.binaryCoordinates_projective_equivariant
    (ClassicalOrthogonal.FourPlusMatrix.Binary.orthogonalEquiv.symm (e h)) (f w)
  rw [MulEquiv.apply_symm_apply] at hh
  exact hh


private theorem not_solvable_of_six_le
    (h : Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (hw : LowRankWitness ρ v X) (hd : 6 ≤ finrank (ZMod 2) V) :
    ¬ Group.IsSolvable G := by
  intro hs
  have hi : IsIrreducible ρ := by
    by_contra hn
    have := (h.reducible_degree_and_solvable hn).1
    omega
  have hX : X ≠ ⊥ := by
    intro he
    obtain ⟨a,ha,ho,_⟩ := hw.exists_involution h.point_ne_zero
    have ha1 : a = 1 := mem_bot.mp (he ▸ ha)
    simp [ha1] at ho
  rcases h.solvable_irreducible_cases cover hs hi hX with h1 | h2 | h3 | h4 | h6
  · have := h1.2.1; omega
  · have := h2.2.1; omega
  · have := h3.2.1; omega
  · have := h4.2.1; omega
  · obtain ⟨hr,hdim⟩ := h6
    omega

private theorem not_caseThree
    (h : Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (hw : LowRankWitness ρ v X) : ¬ CaseThree ρ := by
  rintro ⟨hd, H, _, ⟨e⟩⟩
  let : Group.IsNilpotent RankTwo.ExtraspecialModel.P :=
    (IsPGroup.of_card (p := 3) (n := 3) (HeisenbergPrime.card (p := 3))).isNilpotent
  let : Group.IsNilpotent RankTwo.ExtraspecialModel.S :=
    (IsPGroup.of_card (p := 2) (n := 4)
      (Semidihedral.standardModel_card 4 (Nat.le_refl 4))).isNilpotent
  let : Group.IsSolvable RankTwo.ExtraspecialModel.Model :=
    Group.isSolvable_of_ker_le_range SemidirectProduct.inl SemidirectProduct.rightHom
      SemidirectProduct.range_inl_eq_ker_rightHom.ge
  exact not_solvable_of_six_le hlarge h cover hw hd.ge
    (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)

/-- The literal printed catalogue under the half-degree bound has just four
remaining rows. This theorem does not assume a terminal source configuration
or assert exhaustive recognition of the catalogue itself. -/
theorem remaining_rows
    (h : Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (hw : LowRankWitness ρ v X) (hd : 4 ≤ finrank (ZMod 2) V)
    (hc : Conclusion ρ B X) :
    CaseTwo ρ B ∨ CaseFour ρ ∨ CaseFive ρ B ∨ CaseSix ρ := by
  rcases hc with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
  · have := h1.1; omega
  · exact .inl h2
  · exact (not_caseThree hlarge h cover hw h3).elim
  · exact .inr (.inl h4)
  · exact .inr (.inr (.inl h5))
  · exact .inr (.inr (.inr h6))
  · exact (not_caseSeven hlarge h.faithful h7).elim
  · exact (not_caseEight hlarge h8).elim
  · exact (not_caseNine hlarge h9).elim
  · exact (not_caseTen hlarge h10).elim
  · exact (not_caseEleven hlarge h11).elim
  · exact (not_caseTwelve hlarge h12).elim
  · exact (not_caseThirteen hlarge h13).elim

end CFSG.Quasithin.ChapterG.Section11.LargeActorCatalogue
