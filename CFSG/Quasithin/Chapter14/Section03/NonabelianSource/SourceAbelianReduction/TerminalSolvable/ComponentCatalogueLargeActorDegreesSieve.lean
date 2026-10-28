module

public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueLargeActorDegrees
public import CFSG.Quasithin.ChapterG.Section11.Catalogue
public import Theory.Representation.AlternatingSevenConjugatePair.ElementaryGeometry
public import Theory.Mathieu.M22.ValueBoundParabolics.SmallQuotients
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.PrimeRankOrderBound
public import Theory.Mathieu.M22.Properties.TwoRank
public import Theory.SpecificGroups.PSL2.BinaryAutomorphismRank
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents

/-!
# Source degree alternatives after the numerical catalogue sieve

For the actual larger terminal actor, the solvable extraspecial row and
G.11.2 rows (8)--(13) are impossible. The S₇ and tensor-product rows have
actor rank at most three. In the A₆×C₃ extension the projection to S₆ is
injective on the elementary actor. The SL₂(8) generalized Fitting subgroup
is centerless, so the full group embeds in its automorphism group. The
triple-cover extension maps to Aut(M₂₂) with its actual odd scalar kernel.
These literal maps give the required upper bounds, contradicting the
half-degree lower bound. Row (12) specifies the actor's order directly.

The final theorem applies these exclusions to the original source prefix
and the complete thirteen-case catalogue. It returns the exact degree
alternatives consumed by `source_component_large_actor_of_degree_cases`,
or one of the remaining source rows (4), (5), (7). Construction of that
catalogue and elimination of these three rows remain with the degree-case
owner `qt-e-14314-large-actor-degree-cases`; no exhaustive classification
or unconditional 14.3.14 is claimed here. The final component assembly is
owned by `qt-e-14315-component-large-actor`.

Source: Aschbacher--Smith, 14.3.13--14, printed pp.993--994, and G.11.2,
printed pp.364--367. The full G₂(2) equivalence in row (6) is retained.
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

namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

namespace LargeActorSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  (s : LargeActorSource T M Mc F g B v)
include s

/-- The extraspecial-by-semidihedral group in G.11.2(3) is solvable,
as are its subgroups, so it cannot be the nonsolvable terminal group. -/
theorem not_caseThree : ¬ ChapterG.Section11.CaseThree F.terminalRepresentation := by
  rintro ⟨_, H, _, ⟨e⟩⟩
  let : Group.IsNilpotent RankTwo.ExtraspecialModel.P :=
    (IsPGroup.of_card (p := 3) (n := 3) (HeisenbergPrime.card (p := 3))).isNilpotent
  let : Group.IsNilpotent RankTwo.ExtraspecialModel.S :=
    (IsPGroup.of_card (p := 2) (n := 4)
      (Semidihedral.standardModel_card 4 (Nat.le_refl 4))).isNilpotent
  let : Group.IsSolvable RankTwo.ExtraspecialModel.Model :=
    Group.isSolvable_of_ker_le_range SemidirectProduct.inl SemidirectProduct.rightHom
      SemidirectProduct.range_inl_eq_ker_rightHom.ge
  exact s.nonsolvable (Group.isSolvable_of_isSolvable_injective
    (f := e.toMonoidHom) e.injective)

private theorem false_of_eight_of_actor_le_three
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 8)
    (hm : finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤ 3) : False := by
  have h := s.half_degree_le_actor
  omega

/-- G.11.2(8) is impossible for the original larger actor: every elementary
subgroup of the full seven-letter symmetric group has rank at most three. -/
theorem not_caseEight :
    ¬ ChapterG.Section11.CaseEight F.terminalRepresentation B
      (F.terminalDot (F.X g)) := by
  rintro ⟨hd, ⟨e⟩, _⟩
  apply s.false_of_eight_of_actor_le_three hd
  exact actor_finrank_le_of_embedding e.toMonoidHom e.injective _
    Representation.AlternatingSevenConjugatePair.ElementaryGeometry.primeRank_symmetric.le

/-- All four actual tensor actions in G.11.2(9) have actor rank at most
three, using the S₅ marking of the natural semilinear extension. -/
theorem not_caseNine : ¬ ChapterG.Section11.CaseNine F.terminalRepresentation := by
  rintro ⟨hd, hc⟩
  apply s.false_of_eight_of_actor_le_three hd
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

/-- In G.11.2(10), projection to S₆ is injective on the elementary actor:
its kernel consists of even permutations on three letters, hence is odd.
Embedding S₆ in S₇ bounds the original actor by rank three. -/
theorem not_caseTen :
    ¬ ChapterG.Section11.CaseTen F.terminalRepresentation
      (F.terminalDot (F.X g)) := by
  rintro ⟨hd, e, _⟩
  let X := F.terminalDot (F.X g)
  let q : X →* Equiv.Perm (Fin 6) :=
    (((MonoidHom.fst (Equiv.Perm (Fin 6)) (Equiv.Perm (Fin 3))).comp
      RankTwo.Imprimitive.AlternatingSixTensor.equalSign.subtype).comp
        e.toMonoidHom).comp X.subtype
  have hq : Function.Injective q := by
    apply (injective_iff_map_eq_one q).mpr
    intro x hx
    change (e (x : F.TerminalHdot)).val.1 = 1 at hx
    have hp : e (x : F.TerminalHdot) ^ 2 = 1 := by
      rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian (x : F.TerminalHdot) x.property,
        map_one]
    have hs : (e (x : F.TerminalHdot)).val.2.sign = 1 := by
      have hs' : (e (x : F.TerminalHdot)).val.1.sign =
          (e (x : F.TerminalHdot)).val.2.sign := (e (x : F.TerminalHdot)).property
      rw [← hs', hx, map_one]
    have htwo := even_three_involution (e (x : F.TerminalHdot)).val.2
      (congrArg (fun z : RankTwo.Imprimitive.AlternatingSixTensor.GroupModel => z.val.2) hp) hs
    apply Subtype.ext
    apply e.injective
    change e (x : F.TerminalHdot) = e 1
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
  exact s.false_of_eight_of_actor_le_three hd
    ((Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc)

/-- The group with generalized Fitting subgroup SL₂(8) acts faithfully on
that centerless subgroup. The actual automorphism rank bound excludes
G.11.2(11) for a larger actor, without classifying the full extension. -/
theorem not_caseEleven : ¬ ChapterG.Section11.CaseEleven F.terminalRepresentation := by
  rintro ⟨hd, e, _⟩
  let H := generalizedFitting F.TerminalHdot
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
  have hC : centralizer (H : Set F.TerminalHdot) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxH := centralizer_generalizedFitting_le F.TerminalHdot hx
    have hz : (⟨x, hxH⟩ : H) ∈ center H := by
      apply mem_center_iff.mpr
      intro y
      exact Subtype.ext (mem_centralizer_iff.mp hx y y.property)
    rw [hZ, mem_bot] at hz
    exact congrArg (fun y : H => (y : F.TerminalHdot)) hz
  let a : F.TerminalHdot →* MulAut H := MulAut.conjNormal
  have ha : Function.Injective a := by
    rw [← MonoidHom.ker_eq_bot_iff, MulAut.conjNormal_ker_eq_centralizer]
    exact hC
  let f := (MulAut.congr e).toMonoidHom.comp a
  have hf : Function.Injective f := (MulAut.congr e).injective.comp ha
  have hr := Theory.PSL2.BinaryAutomorphismRank.sl2_automorphism_two_rank_le
    (F := GaloisField 2 3) (n := 3) (by decide)
    (GaloisField.card 2 3 (by decide))
  exact s.false_of_eight_of_actor_le_three hd
    (actor_finrank_le_of_embedding f hf (F.terminalDot (F.X g)) hr)

/-- The literal actor in G.11.2(12) has order eight. Its rank three
contradicts the larger-actor inequality in degree eight. -/
theorem not_caseTwelve :
    ¬ ChapterG.Section11.CaseTwelve F.terminalRepresentation
      (F.terminalDot (F.X g)) := by
  rintro ⟨hd, L, hL, x, hx, hrest⟩
  have hc := hrest.2.2.2.2
  rw [Nat.card_congr Additive.ofMul, Module.natCard_eq_pow_finrank (K := ZMod 2),
    Nat.card_zmod] at hc
  have hm : finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 3 :=
    Nat.pow_right_injective (by decide : 1 < 2) hc
  exact s.false_of_eight_of_actor_le_three hd hm.le

open Janko4.InvolutionCentralizers.First.QuotientExtension in
/-- The genuine triple-cover extension in G.11.2(13) maps to Aut(M₂₂)
with its actual order-three scalar kernel. Its two-rank is at most five,
which excludes a larger actor in degree twelve. -/
theorem not_caseThirteen : ¬ ChapterG.Section11.CaseThirteen F.terminalRepresentation := by
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
    (F.terminalDot (F.X g)) hmodel
  have hlarge := s.half_degree_le_actor
  omega

/-- Apply the numerical exclusions to the original terminal action and
the literal thirteen-case catalogue. The first output is exactly the degree
alternative needed by `source_component_large_actor_of_degree_cases`.
The remaining three rows and construction of the catalogue are still source
obligations of this degree-alternative owner. -/
theorem degree_cases_or_remaining_catalogue
    (hc : ChapterG.Section11.Conclusion F.terminalRepresentation B
      (F.terminalDot (F.X g))) :
    ((finrank (ZMod 2) (Additive F.Uhat) = 4 ∧
        2 ≤ finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) ∨
      (finrank (ZMod 2) (Additive F.Uhat) = 6 ∧
        finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 3 ∧
        Nonempty (F.TerminalHdot ≃* Atlas.G2.Model (ZMod 2)))) ∨
    (ChapterG.Section11.CaseFour F.terminalRepresentation ∨
      ChapterG.Section11.CaseFive F.terminalRepresentation B ∨
      ChapterG.Section11.CaseSeven F.terminalRepresentation (F.terminalDot (F.X g))) := by
  rcases hc with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
  · have hlow := s.four_le_degree
    have hd := h1.1
    omega
  · exact Or.inl (Or.inl ⟨h2.1, s.two_le_actor⟩)
  · exact (s.not_caseThree h3).elim
  · exact Or.inr (Or.inl h4)
  · exact Or.inr (Or.inr (Or.inl h5))
  · obtain ⟨hd, e, _, _⟩ := h6
    exact Or.inl (Or.inr ⟨hd, s.actor_eq_three_of_six_binaryG2 hd e, ⟨e⟩⟩)
  · exact Or.inr (Or.inr (Or.inr h7))
  · exact (s.not_caseEight h8).elim
  · exact (s.not_caseNine h9).elim
  · exact (s.not_caseTen h10).elim
  · exact (s.not_caseEleven h11).elim
  · exact (s.not_caseTwelve h12).elim
  · exact (s.not_caseThirteen h13).elim

end LargeActorSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
