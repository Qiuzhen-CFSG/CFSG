module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianComponents
public import CFSG.Quasithin.Chapter12.Section08.Terminal.SevenModel
public import CFSG.Quasithin.ChapterG.Section11.FullLinearFourModelForm
public import Theory.SpecificGroups.Alternating.FiveSquareFitting
public import Theory.SpecificGroups.PSL2.EightFitting
public import Theory.Representation.SL2FourNaturalOrbits.ElementaryActors

/-!
# Comparing the original nonabelian action with the G.11 rows

The original seed gives the lower dimension bound, and the perfect point
residual supplies a seven-section. These exclude rows (1), (2), (3), (7),
(8), (9), (10) and (11), using the actual model maps. The full Sylow
comparisons also exclude S₈ in both original degrees and hence the
exceptional full GL₄(2) natural-plus-dual row omitted from the printed
catalogue. No exhaustive catalogue theorem is asserted here.

The actual source consumer below retains all markings and reduces either
the printed or corrected catalogue to rows (4)--(6) in degree four, or
rows (12)--(13). Construction of the catalogue, these remaining comparisons,
the nonnormal abelianity argument and local control stay with the original
natural-branch assembly owner. NaturalReduction 4 remains unaltered there.

Source: Aschbacher--Smith 12.9.4, printed pp.859--860, and G.11.2,
printed p.364; see the source correction in docs/quasithin-proof-basis.md.
-/

public noncomputable section
open Subgroup Module Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G} {n : ℕ}

/-- The seven-section of the original point residual divides the faithful actor. -/
theorem nonabelian_hat_seven_dvd {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U) :
    7 ∣ Nat.card F.TerminalHdot :=
  (point_hat_seven_dvd h hn F hne).trans (F.terminalDot (F.Li L 1)).card_subgroup_dvd_card

/-- The original nontrivial perfect point image makes the actor nonsolvable. -/
theorem nonabelian_hat_not_solvable {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U) :
    ¬ Group.IsSolvable F.TerminalHdot := by
  intro hs
  let := hs
  let := point_hat_perfect h hn F
  let : Nontrivial (F.terminalDot (F.Li L 1)) :=
    (nontrivial_iff_ne_bot _).mpr (point_hat_ne_bot h hn F hne)
  exact Group.IsPerfect.not_isSolvable (F.terminalDot (F.Li L 1)) inferInstance

/-- The actual actor cannot embed in a group of order prime to seven. -/
theorem nonabelian_hat_not_embeds_seven_free {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    {Q : Type*} [Group Q] [Finite Q] (hq : ¬ 7 ∣ Nat.card Q)
    (f : F.TerminalHdot →* Q) : ¬ Function.Injective f := by
  intro hf
  exact hq ((nonabelian_hat_seven_dvd h hn F hne).trans (card_dvd_of_injective f hf))

variable {K : GroupClass.{u}}
  (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
  (earlier : EarlierSetupResults K) (F : InvariantFlag T V n)
  (hne : ¬ IsMulCommutative F.U) [IsElementaryAbelian 2 F.Uhat]
include h hn hne

include earlier in
/-- Exclude the original two-dimensional row of G.11.2. -/
theorem nonabelian_not_caseOne : ¬ ChapterG.Section11.CaseOne F.terminalRepresentation := by
  intro hc
  exact hne (point_span_abelian_of_hat_rank_le_four h hn earlier F (by have := hc.1; omega))

include earlier in
/-- Exclude the original four-dimensional row, with its supplied form. -/
theorem nonabelian_not_caseTwo (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) :
    ¬ ChapterG.Section11.CaseTwo F.terminalRepresentation B := by
  intro hc
  exact hne (point_span_abelian_of_hat_rank_le_four h hn earlier F hc.1.le)

/-- The extraspecial-by-semidihedral row is solvable. -/
theorem nonabelian_not_caseThree : ¬ ChapterG.Section11.CaseThree F.terminalRepresentation := by
  rintro ⟨_, H, _, ⟨e⟩⟩
  let : Group.IsNilpotent RankTwo.ExtraspecialModel.P :=
    (IsPGroup.of_card (p := 3) (n := 3) (HeisenbergPrime.card (p := 3))).isNilpotent
  let : Group.IsNilpotent RankTwo.ExtraspecialModel.S :=
    (IsPGroup.of_card (p := 2) (n := 4)
      (Semidihedral.standardModel_card 4 (Nat.le_refl 4))).isNilpotent
  let : Group.IsSolvable RankTwo.ExtraspecialModel.Model :=
    Group.isSolvable_of_ker_le_range SemidirectProduct.inl SemidirectProduct.rightHom
      SemidirectProduct.range_inl_eq_ker_rightHom.ge
  exact nonabelian_hat_not_solvable h hn F hne
    (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)

/-- The actual projective Ω₄⁺(4) generalized Fitting subgroup is A₅×A₅.
Its full automorphism group has order prime to seven, excluding row (7). -/
theorem nonabelian_not_caseSeven (X : Subgroup F.TerminalHdot) :
    ¬ ChapterG.Section11.CaseSeven F.terminalRepresentation X := by
  rintro ⟨_,_,e,_,_⟩
  let a := ClassicalOrthogonal.FourPlusMatrix.Binary.orthogonalEquiv
  let b := Representation.SL2FourNatural.alternatingFiveEquiv.prodCongr
    Representation.SL2FourNatural.alternatingFiveEquiv
  exact Theory.SpecificGroups.Alternating.FiveSquareFitting.seven_not_dvd
    ((e.trans a.symm).trans b) (nonabelian_hat_seven_dvd h hn F hne)

include earlier in
/-- Apply the full-Sylow S₇ exclusion to the literal representation row (8). -/
theorem nonabelian_not_caseEight
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (X : Subgroup F.TerminalHdot) :
    ¬ ChapterG.Section11.CaseEight F.terminalRepresentation B X :=
  fun hc => point_hat_not_symmetric_seven h hn earlier F hne hc.2.1

/-- All four tensor actors of row (9) embed in S₅×S₃, whose order is prime
to seven. The actual natural semilinear coordinates are retained. -/
theorem nonabelian_not_caseNine : ¬ ChapterG.Section11.CaseNine F.terminalRepresentation := by
  rintro ⟨_,hc⟩
  have hfree : ¬ 7 ∣ Nat.card (Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3)) := by
    rw [Nat.card_prod,Nat.card_perm,Nat.card_perm,Nat.card_fin,Nat.card_fin]
    decide
  rcases hc with ⟨e,_,_⟩ | ⟨e,_,_⟩ | ⟨e,_,_⟩ | ⟨e,_,_⟩
  · exact nonabelian_hat_not_embeds_seven_free h hn F hne hfree e.toMonoidHom e.injective
  · let f := (alternatingGroup (Fin 5)).subtype.prodMap (MonoidHom.id (Equiv.Perm (Fin 3)))
    have hf : Function.Injective f := by
      intro a b he
      exact Prod.ext (Subtype.ext (congrArg Prod.fst he))
        (congrArg (fun z : Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3) => z.2) he)
    exact nonabelian_hat_not_embeds_seven_free h hn F hne hfree
      (f.comp e.toMonoidHom) (hf.comp e.injective)
  · let a := RankTwo.TensorModels.Natural.groupEquiv.prodCongr
      (MulEquiv.refl (Equiv.Perm (Fin 3)))
    exact nonabelian_hat_not_embeds_seven_free h hn F hne hfree
      (e.trans a).toMonoidHom (e.trans a).injective
  · let f := ((alternatingGroup (Fin 5)).subtype.comp
      RankTwo.TensorModels.Natural.alternatingEquiv.toMonoidHom).prodMap
        (MonoidHom.id (Equiv.Perm (Fin 3)))
    have hf : Function.Injective f := by
      intro a b he
      exact Prod.ext (RankTwo.TensorModels.Natural.alternatingEquiv.injective
        (Subtype.ext (congrArg Prod.fst he)))
          (congrArg (fun z : Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3) => z.2) he)
    exact nonabelian_hat_not_embeds_seven_free h hn F hne hfree
      (f.comp e.toMonoidHom) (hf.comp e.injective)

/-- The equal-sign A₆×C₃ extension of row (10) embeds in S₆×S₃. -/
theorem nonabelian_not_caseTen (X : Subgroup F.TerminalHdot) :
    ¬ ChapterG.Section11.CaseTen F.terminalRepresentation X := by
  rintro ⟨_,e,_⟩
  let f := RankTwo.Imprimitive.AlternatingSixTensor.equalSign.subtype.comp e.toMonoidHom
  apply nonabelian_hat_not_embeds_seven_free h hn F hne (f := f) _
    (RankTwo.Imprimitive.AlternatingSixTensor.equalSign.subtype_injective.comp e.injective)
  rw [Nat.card_prod,Nat.card_perm,Nat.card_perm,Nat.card_fin,Nat.card_fin]
  decide

/-- The SL₂(8) generalized Fitting row cannot contain the original perfect
point residual with its GL₃(2) or GL₄(2) two-core quotient. -/
theorem nonabelian_not_caseEleven :
    ¬ ChapterG.Section11.CaseEleven F.terminalRepresentation := by
  rintro ⟨_,e,_⟩
  let := point_hat_perfect h hn F
  apply Theory.PSL2.EightFitting.perfect_core_card_excluded e (F.terminalDot (F.Li L 1))
  have hc := point_hat_core_card h hn F hne
  split_ifs at hc with hd
  · exact Or.inl hc
  · exact Or.inr hc

omit h hn hne in
/-- The exceptional corrected full-linear-four row has actual actor S₈,
which is excluded in both original degrees by the point residual. -/
theorem nonabelian_not_fullLinearFour
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (hne : ¬ IsMulCommutative F.U)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (W : Submodule (ZMod 2) (Additive F.Uhat))
    (X : Subgroup F.TerminalHdot) (X₀ : Subgroup X) :
    ¬ ChapterG.Section11.FullLinearFour.MarkedAlternative F.terminalRepresentation B v W X X₀ := by
  rintro ⟨H,I,J,m,_⟩
  exact point_hat_not_symmetric_eight h hn earlier F hne ⟨m.symmetricEquiv⟩

include earlier in
/-- Apply the proved comparisons to the literal thirteen-row catalogue.
This does not construct that catalogue. The surviving six-dimensional rows
have original degree four; the remaining higher-dimensional rows retain
all their markings for the subsequent component comparison. -/
theorem nonabelian_catalogue_remaining
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (X : Subgroup F.TerminalHdot)
    (hc : ChapterG.Section11.Conclusion F.terminalRepresentation B X) :
    (n = 4 ∧ (ChapterG.Section11.CaseFour F.terminalRepresentation ∨
      ChapterG.Section11.CaseFive F.terminalRepresentation B ∨
      ChapterG.Section11.CaseSix F.terminalRepresentation)) ∨
    ChapterG.Section11.CaseTwelve F.terminalRepresentation X ∨
    ChapterG.Section11.CaseThirteen F.terminalRepresentation := by
  rcases hc with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
  · exact (nonabelian_not_caseOne h hn earlier F hne h1).elim
  · exact (nonabelian_not_caseTwo h hn earlier F hne B h2).elim
  · exact (nonabelian_not_caseThree h hn F hne h3).elim
  · exact Or.inl ⟨nonabelian_degree_four_of_hat_rank_le_six h hn earlier F hne h4.1.le,
      Or.inl h4⟩
  · exact Or.inl ⟨nonabelian_degree_four_of_hat_rank_le_six h hn earlier F hne h5.1.le,
      Or.inr (Or.inl h5)⟩
  · exact Or.inl ⟨nonabelian_degree_four_of_hat_rank_le_six h hn earlier F hne h6.1.le,
      Or.inr (Or.inr h6)⟩
  · exact (nonabelian_not_caseSeven h hn F hne X h7).elim
  · exact (nonabelian_not_caseEight h hn earlier F hne B X h8).elim
  · exact (nonabelian_not_caseNine h hn F hne h9).elim
  · exact (nonabelian_not_caseTen h hn F hne X h10).elim
  · exact (nonabelian_not_caseEleven h hn F hne h11).elim
  · exact Or.inr (Or.inl h12)
  · exact Or.inr (Or.inr h13)

omit h hn hne in
/-- The same actual comparison applies to the corrected catalogue including
full GL₄(2). This discharges that extra row rather than assuming it away;
construction of the catalogue and the remaining source rows stay with the
natural-branch assembly owner. -/
theorem nonabelian_corrected_catalogue_remaining
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (hne : ¬ IsMulCommutative F.U)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (W : Submodule (ZMod 2) (Additive F.Uhat))
    (X : Subgroup F.TerminalHdot) (X₀ : Subgroup X)
    (hc : ChapterG.Section11.FullLinearFour.ConclusionWithFullLinearFour
      F.terminalRepresentation B v W X X₀) :
    (n = 4 ∧ (ChapterG.Section11.CaseFour F.terminalRepresentation ∨
      ChapterG.Section11.CaseFive F.terminalRepresentation B ∨
      ChapterG.Section11.CaseSix F.terminalRepresentation)) ∨
    ChapterG.Section11.CaseTwelve F.terminalRepresentation X ∨
    ChapterG.Section11.CaseThirteen F.terminalRepresentation := by
  rcases hc with hc | hc
  · exact nonabelian_catalogue_remaining h hn earlier F hne B X hc
  · exact (nonabelian_not_fullLinearFour F h hn earlier hne B v W X X₀ hc).elim

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
