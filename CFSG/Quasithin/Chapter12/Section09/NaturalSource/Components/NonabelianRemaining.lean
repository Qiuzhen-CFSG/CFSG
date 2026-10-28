module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianCases
public import Theory.SpecificGroups.G2.BinaryPerfectSylow
public import Theory.SpecificGroups.Alternating.FivePairFitting

/-!
# Further exclusions for the original nonabelian point action

The perfect point residual is normalized by the literal quotient Sylow.
In G₂(2) this would force it to be G₂(2)′, contradicting its intrinsic
two-core quotient. The exchanged A₅ row has generalized Fitting subgroup
A₅ × A₅, so its automorphism group has no seven-section.

Both comparisons apply to the actual H/C_H(U/Z(U)) and its point image.
The final sieve retains the original action and form. It is conditional
on catalogue exhaustion; that construction and the remaining abelianity
branches stay with the natural-source assembly owner.
Source: Aschbacher--Smith 12.9.4, printed pp.859--860.
-/

public noncomputable section
open Subgroup Module Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G} {n : ℕ}

/-- The actual faithful actor cannot be the full binary G₂ group. -/
theorem point_hat_not_binary_g2 {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n)
    (hne : ¬ IsMulCommutative F.U) :
    ¬ Nonempty (F.TerminalHdot ≃* Atlas.G2.Model (ZMod 2)) := by
  rintro ⟨e⟩
  let C := F.terminalDot (F.Li L 1)
  let B := C.map e.toMonoidHom
  let c : C ≃* B := C.equivMapOfInjective e.toMonoidHom e.injective
  have hc : Nat.card (B ⧸ pCore 2 B) = if n = 4 then 168 else 20160 :=
    (Nat.card_congr (QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).symm.toEquiv).trans
      (point_hat_core_card h hn F hne)
  let := point_hat_perfect h hn F
  let : Group.IsPerfect B := Group.IsPerfect.map _
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  let Sbase : Sylow 2 F.H := T.subtype (F.invariant 1)
  let S₀ := Sbase.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  let S := S₀.mapSurjective (f := e.toMonoidHom) e.surjective
  have hn₀ : (Sbase : Subgroup F.H) ≤
      normalizer ((F.Li L 1).subgroupOf F.H : Set F.H) := by
    intro t ht b
    exact sylow_normalizes_Li h earlier F 1 ht (b : G)
  have hn₁ : (S₀ : Subgroup F.TerminalHdot) ≤ normalizer (C : Set F.TerminalHdot) :=
    (map_mono hn₀).trans (((F.Li L 1).subgroupOf F.H).le_normalizer_map q)
  have hn₂ : (S : Subgroup (Atlas.G2.Model (ZMod 2))) ≤ normalizer (B : Set _) :=
    (map_mono hn₁).trans (C.le_normalizer_map e.toMonoidHom)
  apply Atlas.G2.BinaryPerfectSylow.core_card_excluded B S hn₂
  split_ifs at hc with hd
  · exact Or.inl hc
  · exact Or.inr hc

/-- Exclude G.11.2(6) with its full G₂(2) action. -/
theorem nonabelian_not_caseSix {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n)
    (hne : ¬ IsMulCommutative F.U) [IsElementaryAbelian 2 F.Uhat] :
    ¬ ChapterG.Section11.CaseSix F.terminalRepresentation := by
  rintro ⟨_,e,_,_⟩
  exact point_hat_not_binary_g2 h hn earlier F hne ⟨e⟩

/-- The exchanged components of row (12) are genuinely distinct, and their
product excludes the original seven-section. No actor-rank bound is needed. -/
theorem nonabelian_not_caseTwelve {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (X : Subgroup F.TerminalHdot) :
    ¬ ChapterG.Section11.CaseTwelve F.terminalRepresentation X := by
  rintro ⟨hd,A,hA,x,_,hfit,hcompl,⟨e,_,_⟩,_⟩
  let B := A.map (MulAut.conj x).toMonoidHom
  have hAB : A ≠ B := by
    intro he
    change IsCompl (BinaryOffender.subspaceCommutator F.terminalRepresentation ⊤ A)
      (BinaryOffender.subspaceCommutator F.terminalRepresentation ⊤ B) at hcompl
    rw [← he] at hcompl
    have hb := hcompl.disjoint.eq_bot
    rw [inf_idem] at hb
    have ht := hcompl.codisjoint.eq_top
    rw [sup_idem,hb] at ht
    have hh := congrArg (fun P : Submodule (ZMod 2) (Additive F.Uhat) =>
      finrank (ZMod 2) P) ht
    simp only [finrank_bot,finrank_top] at hh
    omega
  let a : A ≃* B := A.equivMapOfInjective (MulAut.conj x).toMonoidHom
    (MulAut.conj x).injective
  exact Theory.SpecificGroups.Alternating.FivePairFitting.seven_not_dvd A B hA
    (hA.map_equiv (MulAut.conj x)) hAB e (a.symm.trans e) hfit
      (nonabelian_hat_seven_dvd h hn F hne)

/-- After the original residual comparisons, only the A₇, orthogonal-six
and triple-M₂₂ rows can remain. This retains the catalogue premise explicitly. -/
theorem nonabelian_catalogue_three_rows {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n)
    (hne : ¬ IsMulCommutative F.U) [IsElementaryAbelian 2 F.Uhat]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (X : Subgroup F.TerminalHdot)
    (hc : ChapterG.Section11.Conclusion F.terminalRepresentation B X) :
    (n = 4 ∧ (ChapterG.Section11.CaseFour F.terminalRepresentation ∨
      ChapterG.Section11.CaseFive F.terminalRepresentation B)) ∨
    ChapterG.Section11.CaseThirteen F.terminalRepresentation := by
  rcases nonabelian_catalogue_remaining h hn earlier F hne B X hc with
    ⟨hd,h4 | h5 | h6⟩ | h12 | h13
  · exact Or.inl ⟨hd,Or.inl h4⟩
  · exact Or.inl ⟨hd,Or.inr h5⟩
  · exact (nonabelian_not_caseSix h hn earlier F hne h6).elim
  · exact (nonabelian_not_caseTwelve h hn F hne X h12).elim
  · exact Or.inr h13

/-- The same sieve discharges the exceptional full-linear-four alternative
in the corrected catalogue while retaining every actual marking. -/
theorem nonabelian_corrected_catalogue_three_rows
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (W : Submodule (ZMod 2) (Additive F.Uhat))
    (X : Subgroup F.TerminalHdot) (X₀ : Subgroup X)
    (hc : ChapterG.Section11.FullLinearFour.ConclusionWithFullLinearFour
      F.terminalRepresentation B v W X X₀) :
    (n = 4 ∧ (ChapterG.Section11.CaseFour F.terminalRepresentation ∨
      ChapterG.Section11.CaseFive F.terminalRepresentation B)) ∨
    ChapterG.Section11.CaseThirteen F.terminalRepresentation := by
  rcases hc with hc | hc
  · exact nonabelian_catalogue_three_rows h hn earlier F hne B X hc
  · exact (nonabelian_not_fullLinearFour F h hn earlier hne B v W X X₀ hc).elim

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
